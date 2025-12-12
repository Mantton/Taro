use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    mir::{self, Operand},
    sema::models::{FloatTy, IntTy, Ty, TyKind, UIntTy},
    span::Symbol,
};
use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel,
    builder::Builder,
    context::Context,
    module::Module,
    passes::PassManager,
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FloatType, FunctionType, IntType},
    values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, PointerValue},
};
use rustc_hash::FxHashMap;
use std::{fs, path::PathBuf};

/// Lower MIR for a package into a single LLVM module and cache its IR.
pub fn emit_package<'gcx>(
    package: &'gcx mir::MirPackage<'gcx>,
    gcx: GlobalContext<'gcx>,
) -> CompileResult<PathBuf> {
    let context = Context::create();
    let module = context.create_module(&gcx.config.identifier);
    let builder = context.create_builder();

    let mut emitter = Emitter::new(&context, module, builder, gcx);
    emitter.declare_functions(package);
    emitter.lower_functions(package)?;
    emitter.emit_start_shim(package);
    emitter.run_function_passes();

    let ir = emitter.module.print_to_string().to_string();
    println!("{ir}");

    let obj = emitter.emit_object_file()?;
    gcx.cache_object_file(obj.clone());
    Ok(obj)
}

struct Emitter<'llvm, 'gcx> {
    context: &'llvm Context,
    module: Module<'llvm>,
    builder: Builder<'llvm>,
    gcx: GlobalContext<'gcx>,
    functions: FxHashMap<hir::DefinitionID, FunctionValue<'llvm>>,
    strings: FxHashMap<Symbol, PointerValue<'llvm>>,
}

#[derive(Clone, Copy)]
enum LocalStorage<'llvm> {
    Value(Option<BasicValueEnum<'llvm>>),
    Stack(PointerValue<'llvm>),
}

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn new(
        context: &'llvm Context,
        module: Module<'llvm>,
        builder: Builder<'llvm>,
        gcx: GlobalContext<'gcx>,
    ) -> Self {
        Emitter {
            context,
            module,
            builder,
            gcx,
            functions: FxHashMap::default(),
            strings: FxHashMap::default(),
        }
    }

    fn declare_functions(&mut self, package: &mir::MirPackage<'gcx>) {
        for (&def_id, _) in &package.functions {
            let sig = self.gcx.get_signature(def_id);
            let fn_ty = lower_fn_sig(self.context, sig);
            let name = mangle(self.gcx, def_id);
            let f = self.module.add_function(&name, fn_ty, None);
            self.functions.insert(def_id, f);
        }
    }

    fn lower_functions(&mut self, package: &mir::MirPackage<'gcx>) -> CompileResult<()> {
        for (&def_id, body) in &package.functions {
            self.lower_body(def_id, body)?;
        }
        Ok(())
    }

    fn emit_start_shim(&mut self, package: &mir::MirPackage<'gcx>) {
        let Some(entry) = package.entry else {
            return;
        };
        let Some(&user_fn) = self.functions.get(&entry) else {
            return;
        };
        let entry_sig = self.gcx.get_signature(entry);

        let i32_ty = self.context.i32_type();
        let start_ty = i32_ty.fn_type(&[], false);
        let start_fn = self.module.add_function("taro_start", start_ty, None);

        let builder = self.context.create_builder();
        let bb = self.context.append_basic_block(start_fn, "entry");
        builder.position_at_end(bb);
        let call = builder.build_call(user_fn, &[], "call_main").unwrap();

        let exit_code = match (entry_sig.output.kind(), call.try_as_basic_value().basic()) {
            (TyKind::Infer(_) | TyKind::Error, _) => {
                i32_ty.const_int(0, false).as_basic_value_enum()
            }
            (TyKind::Tuple(items), _) if items.is_empty() => {
                i32_ty.const_int(0, false).as_basic_value_enum()
            }
            (TyKind::Bool, Some(val)) => {
                let int = builder
                    .build_int_z_extend_or_bit_cast(val.into_int_value(), i32_ty, "bool_to_i32")
                    .unwrap();
                int.as_basic_value_enum()
            }
            (TyKind::Int(_) | TyKind::UInt(_) | TyKind::Rune, Some(val)) => {
                let int_val = val.into_int_value();
                let cast = builder
                    .build_int_cast(int_val, i32_ty, "int_to_i32")
                    .unwrap();
                cast.as_basic_value_enum()
            }
            (TyKind::Float(_), Some(val)) => builder
                .build_float_to_signed_int(val.into_float_value(), i32_ty, "float_to_i32")
                .unwrap()
                .as_basic_value_enum(),
            (TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::String, Some(val)) => {
                let ptr = val.into_pointer_value();
                let int64 = builder
                    .build_ptr_to_int(ptr, self.context.i64_type(), "ptr_to_int")
                    .unwrap();
                builder
                    .build_int_cast(int64, i32_ty, "ptr_to_i32")
                    .unwrap()
                    .as_basic_value_enum()
            }
            (_, Some(val)) => val,
            _ => i32_ty.const_int(0, false).as_basic_value_enum(),
        };

        let _ = builder.build_return(Some(&exit_code)).unwrap();

        // Provide a conventional `main` that forwards to `taro_start` for easier linking.
        let main_fn = self.module.add_function("main", start_ty, None);
        let main_builder = self.context.create_builder();
        let main_bb = self.context.append_basic_block(main_fn, "entry");
        main_builder.position_at_end(main_bb);
        let start_call = main_builder
            .build_call(start_fn, &[], "call_start")
            .unwrap();
        let main_ret = start_call
            .try_as_basic_value()
            .basic()
            .map(|v| v.into_int_value())
            .unwrap_or_else(|| i32_ty.const_int(0, false));
        let _ = main_builder.build_return(Some(&main_ret)).unwrap();
    }

    fn run_function_passes(&self) {
        let fpm = PassManager::create(&self.module);
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.add_promote_memory_to_register_pass();
        fpm.initialize();

        for func in self.module.get_functions() {
            let _ = fpm.run_on(&func);
        }
    }

    fn emit_object_file(&mut self) -> CompileResult<PathBuf> {
        // Configure target machine for host.
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|_| crate::error::ReportedError)?;
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).map_err(|_| crate::error::ReportedError)?;
        let cpu = TargetMachine::get_host_cpu_name();
        let features = TargetMachine::get_host_cpu_features();
        let tm = target
            .create_target_machine(
                &triple,
                cpu.to_str().unwrap_or(""),
                features.to_str().unwrap_or(""),
                OptimizationLevel::Default,
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or(crate::error::ReportedError)?;

        self.module
            .set_data_layout(&tm.get_target_data().get_data_layout());
        self.module.set_triple(&triple);

        let out_dir = self.gcx.output_root().clone();
        if let Err(e) = fs::create_dir_all(&out_dir) {
            let msg = format!("failed to create output directory: {e}");
            self.gcx.dcx().emit_error(msg.into(), None);
            return Err(crate::error::ReportedError);
        }
        let obj_path = out_dir.join(format!("{}.o", self.gcx.config.identifier));

        tm.write_to_file(&self.module, FileType::Object, &obj_path)
            .map_err(|e| {
                let msg = format!("failed to write object file: {e}");
                self.gcx.dcx().emit_error(msg.into(), None);
                crate::error::ReportedError
            })?;

        Ok(obj_path)
    }

    fn lower_body(
        &mut self,
        def_id: hir::DefinitionID,
        body: &mir::Body<'gcx>,
    ) -> CompileResult<()> {
        let function = *self
            .functions
            .get(&def_id)
            .expect("function must be declared");

        let llvm_blocks = self.create_blocks(function, body);
        let entry_block = llvm_blocks[body.start_block.index()];
        let mut locals = self.allocate_locals(body, entry_block, function);

        self.builder.position_at_end(entry_block);

        for (bb_id, bb) in body.basic_blocks.iter_enumerated() {
            let llvm_bb = llvm_blocks[bb_id.index()];
            self.builder.position_at_end(llvm_bb);

            for stmt in &bb.statements {
                self.lower_statement(body, &mut locals, stmt)?;
            }

            if let Some(term) = &bb.terminator {
                self.lower_terminator(body, &mut locals, term, &llvm_blocks)?;
            } else if llvm_bb.get_terminator().is_none() {
                let _ = self.builder.build_unreachable().unwrap();
            }
        }

        Ok(())
    }

    fn create_blocks(
        &self,
        function: FunctionValue<'llvm>,
        body: &mir::Body<'gcx>,
    ) -> Vec<inkwell::basic_block::BasicBlock<'llvm>> {
        let mut blocks = Vec::with_capacity(body.basic_blocks.len());
        for (idx, _) in body.basic_blocks.iter().enumerate() {
            blocks.push(
                self.context
                    .append_basic_block(function, &format!("bb{idx}")),
            );
        }
        blocks
    }

    fn allocate_locals(
        &self,
        body: &mir::Body<'gcx>,
        entry_block: inkwell::basic_block::BasicBlock<'llvm>,
        function: FunctionValue<'llvm>,
    ) -> Vec<LocalStorage<'llvm>> {
        let alloc_builder = self.context.create_builder();
        alloc_builder.position_at_end(entry_block);

        let mut locals = Vec::with_capacity(body.locals.len());
        for (idx, decl) in body.locals.iter().enumerate() {
            let name = decl
                .name
                .map(|s| s.as_str().to_string())
                .unwrap_or_else(|| format!("tmp{idx}"));
            let storage = match decl.kind {
                mir::LocalKind::Param => LocalStorage::Value(None),
                mir::LocalKind::Temp | mir::LocalKind::Return => LocalStorage::Value(None),
                mir::LocalKind::User => match lower_type(self.context, decl.ty) {
                    Some(ty) => {
                        let slot = alloc_builder.build_alloca(ty, &name).unwrap();
                        LocalStorage::Stack(slot)
                    }
                    None => LocalStorage::Value(None),
                },
            };
            locals.push(storage);
        }

        // Seed parameters with incoming SSA arguments.
        let mut params = function.get_param_iter();
        for (idx, decl) in body.locals.iter().enumerate() {
            if let mir::LocalKind::Param = decl.kind {
                if let Some(arg) = params.next() {
                    locals[idx] = LocalStorage::Value(Some(arg));
                }
            }
        }

        locals
    }

    fn lower_statement(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        stmt: &mir::Statement<'gcx>,
    ) -> CompileResult<()> {
        match &stmt.kind {
            mir::StatementKind::Assign(place, rvalue) => {
                let dest_ty = body.locals[place.local].ty;
                if let Some(value) = self.lower_rvalue(body, locals, dest_ty, rvalue)? {
                    self.store_local(place.local, locals, value, body);
                }
            }
            mir::StatementKind::Store { ptr, value } => {
                if let (Some(ptr_val), Some(val)) = (
                    self.eval_operand(body, locals, ptr)?,
                    self.eval_operand(body, locals, value)?,
                ) {
                    if let BasicValueEnum::PointerValue(ptr) = ptr_val {
                        let _ = self.builder.build_store(ptr, val).unwrap();
                    }
                }
            }
            mir::StatementKind::Nop => {}
        }
        Ok(())
    }

    fn lower_rvalue(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        dest_ty: Ty<'gcx>,
        rvalue: &mir::Rvalue<'gcx>,
    ) -> CompileResult<Option<BasicValueEnum<'llvm>>> {
        let value = match rvalue {
            mir::Rvalue::Use(op) => self.eval_operand(body, locals, op)?,
            mir::Rvalue::UnaryOp { op, operand } => {
                let operand = match self.eval_operand(body, locals, operand)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                Some(self.lower_unary(dest_ty, *op, operand))
            }
            mir::Rvalue::BinaryOp { op, lhs, rhs } => {
                let lhs_ty = self.operand_ty(body, lhs);
                let lhs = match self.eval_operand(body, locals, lhs)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                let rhs = match self.eval_operand(body, locals, rhs)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                self.lower_binary(lhs_ty, *op, lhs, rhs)
            }
            mir::Rvalue::Cast { operand, ty } => {
                let from_ty = self.operand_ty(body, operand);
                let val = match self.eval_operand(body, locals, operand)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                self.lower_cast(from_ty, *ty, val)
            }
        };
        Ok(value)
    }

    fn lower_unary(
        &mut self,
        dest_ty: Ty<'gcx>,
        op: hir::UnaryOperator,
        operand: BasicValueEnum<'llvm>,
    ) -> BasicValueEnum<'llvm> {
        match op {
            hir::UnaryOperator::LogicalNot => {
                let val = operand.into_int_value();
                self.builder
                    .build_not(val, "bool_not")
                    .unwrap()
                    .as_basic_value_enum()
            }
            hir::UnaryOperator::Negate => match dest_ty.kind() {
                TyKind::Float(_) => {
                    let val = operand.into_float_value();
                    self.builder
                        .build_float_neg(val, "neg")
                        .unwrap()
                        .as_basic_value_enum()
                }
                _ => {
                    let val = operand.into_int_value();
                    self.builder
                        .build_int_neg(val, "neg")
                        .unwrap()
                        .as_basic_value_enum()
                }
            },
            hir::UnaryOperator::BitwiseNot => {
                let val = operand.into_int_value();
                self.builder
                    .build_not(val, "not")
                    .unwrap()
                    .as_basic_value_enum()
            }
        }
    }

    fn lower_binary(
        &mut self,
        operand_ty: Ty<'gcx>,
        op: hir::BinaryOperator,
        lhs: BasicValueEnum<'llvm>,
        rhs: BasicValueEnum<'llvm>,
    ) -> Option<BasicValueEnum<'llvm>> {
        let result = match operand_ty.kind() {
            TyKind::Float(_) => {
                let lhs = lhs.into_float_value();
                let rhs = rhs.into_float_value();
                match op {
                    hir::BinaryOperator::Add => self
                        .builder
                        .build_float_add(lhs, rhs, "add")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Sub => self
                        .builder
                        .build_float_sub(lhs, rhs, "sub")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Mul => self
                        .builder
                        .build_float_mul(lhs, rhs, "mul")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Div => self
                        .builder
                        .build_float_div(lhs, rhs, "div")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Rem => self
                        .builder
                        .build_float_rem(lhs, rhs, "rem")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Eql => self
                        .builder
                        .build_float_compare(FloatPredicate::OEQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Neq => self
                        .builder
                        .build_float_compare(FloatPredicate::UNE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Gt => self
                        .builder
                        .build_float_compare(FloatPredicate::OGT, lhs, rhs, "gt")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Lt => self
                        .builder
                        .build_float_compare(FloatPredicate::OLT, lhs, rhs, "lt")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Geq => self
                        .builder
                        .build_float_compare(FloatPredicate::OGE, lhs, rhs, "ge")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Leq => self
                        .builder
                        .build_float_compare(FloatPredicate::OLE, lhs, rhs, "le")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Bool => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                match op {
                    hir::BinaryOperator::BoolAnd => self
                        .builder
                        .build_and(lhs, rhs, "and")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::BoolOr => self
                        .builder
                        .build_or(lhs, rhs, "or")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::String => {
                let lhs_ptr = lhs.into_pointer_value();
                let rhs_ptr = rhs.into_pointer_value();
                let ptr_int_ty = self.context.i64_type();
                let lhs = self
                    .builder
                    .build_ptr_to_int(lhs_ptr, ptr_int_ty, "ptr_l")
                    .unwrap();
                let rhs = self
                    .builder
                    .build_ptr_to_int(rhs_ptr, ptr_int_ty, "ptr_r")
                    .unwrap();
                match op {
                    hir::BinaryOperator::PtrEq | hir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "ptr_eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "ptr_neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Rune => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                let signed = is_signed(operand_ty);
                match op {
                    hir::BinaryOperator::Add => self
                        .builder
                        .build_int_add(lhs, rhs, "add")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Sub => self
                        .builder
                        .build_int_sub(lhs, rhs, "sub")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Mul => self
                        .builder
                        .build_int_mul(lhs, rhs, "mul")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Div => {
                        if signed {
                            self.builder
                                .build_int_signed_div(lhs, rhs, "div")
                                .unwrap()
                                .as_basic_value_enum()
                        } else {
                            self.builder
                                .build_int_unsigned_div(lhs, rhs, "div")
                                .unwrap()
                                .as_basic_value_enum()
                        }
                    }
                    hir::BinaryOperator::Rem => {
                        if signed {
                            self.builder
                                .build_int_signed_rem(lhs, rhs, "rem")
                                .unwrap()
                                .as_basic_value_enum()
                        } else {
                            self.builder
                                .build_int_unsigned_rem(lhs, rhs, "rem")
                                .unwrap()
                                .as_basic_value_enum()
                        }
                    }
                    hir::BinaryOperator::BitAnd | hir::BinaryOperator::BoolAnd => self
                        .builder
                        .build_and(lhs, rhs, "and")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::BitOr | hir::BinaryOperator::BoolOr => self
                        .builder
                        .build_or(lhs, rhs, "or")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::BitXor => self
                        .builder
                        .build_xor(lhs, rhs, "xor")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::BitShl => self
                        .builder
                        .build_left_shift(lhs, rhs, "shl")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::BitShr => self
                        .builder
                        .build_right_shift(lhs, rhs, signed, "shr")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Gt => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SGT
                            } else {
                                IntPredicate::UGT
                            },
                            lhs,
                            rhs,
                            "gt",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Lt => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SLT
                            } else {
                                IntPredicate::ULT
                            },
                            lhs,
                            rhs,
                            "lt",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Geq => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SGE
                            } else {
                                IntPredicate::UGE
                            },
                            lhs,
                            rhs,
                            "ge",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::Leq => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SLE
                            } else {
                                IntPredicate::ULE
                            },
                            lhs,
                            rhs,
                            "le",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    hir::BinaryOperator::PtrEq => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                }
            }
            _ => return None,
        };
        Some(result)
    }

    fn lower_cast(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> Option<BasicValueEnum<'llvm>> {
        if from_ty == to_ty {
            return Some(value);
        }

        if let (Some((_, _)), Some((to_int, to_signed))) =
            (self.int_type(from_ty), self.int_type(to_ty))
        {
            return Some(
                self.builder
                    .build_int_cast_sign_flag(value.into_int_value(), to_int, to_signed, "int_cast")
                    .unwrap()
                    .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some(to_float)) = (self.int_type(from_ty), self.float_type(to_ty)) {
            let signed = is_signed(from_ty);
            return Some(
                if signed {
                    self.builder
                        .build_signed_int_to_float(value.into_int_value(), to_float, "itof")
                        .unwrap()
                } else {
                    self.builder
                        .build_unsigned_int_to_float(value.into_int_value(), to_float, "itof")
                        .unwrap()
                }
                .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some((to_int, to_signed))) =
            (self.float_type(from_ty), self.int_type(to_ty))
        {
            return Some(
                if to_signed {
                    self.builder
                        .build_float_to_signed_int(value.into_float_value(), to_int, "ftoi")
                        .unwrap()
                } else {
                    self.builder
                        .build_float_to_unsigned_int(value.into_float_value(), to_int, "ftoi")
                        .unwrap()
                }
                .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some(to_float)) = (self.float_type(from_ty), self.float_type(to_ty)) {
            let val = value.into_float_value();
            return Some(
                self.builder
                    .build_float_cast(val, to_float, "fcast")
                    .unwrap()
                    .as_basic_value_enum(),
            );
        }

        if matches!(
            to_ty.kind(),
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::String
        ) {
            return Some(
                self.builder
                    .build_bit_cast(
                        value,
                        self.context
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum(),
                        "ptrcast",
                    )
                    .unwrap()
                    .into(),
            );
        }

        None
    }

    fn lower_terminator(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        terminator: &mir::Terminator<'gcx>,
        blocks: &[inkwell::basic_block::BasicBlock<'llvm>],
    ) -> CompileResult<()> {
        match &terminator.kind {
            mir::TerminatorKind::Goto { target } => {
                let _ = self
                    .builder
                    .build_unconditional_branch(blocks[target.index()])
                    .unwrap();
            }
            mir::TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let Some(value) = self.eval_operand(body, locals, discr)? else {
                    let _ = self.builder.build_unreachable().unwrap();
                    return Ok(());
                };
                let discr_val = value.into_int_value();
                let default_bb = blocks[otherwise.index()];

                let cases: Vec<(inkwell::values::IntValue<'llvm>, _)> = targets
                    .iter()
                    .map(|(const_val, bb)| {
                        (
                            discr_val.get_type().const_int(*const_val as u64, false),
                            blocks[bb.index()],
                        )
                    })
                    .collect();
                let _ = self
                    .builder
                    .build_switch(discr_val, default_bb, &cases)
                    .unwrap();
            }
            mir::TerminatorKind::Return => match self.load_local(body, locals, body.return_local) {
                Some(val) => {
                    let _ = self.builder.build_return(Some(&val)).unwrap();
                }
                None => {
                    let _ = self.builder.build_return(None).unwrap();
                }
            },
            mir::TerminatorKind::Unreachable => {
                let _ = self.builder.build_unreachable().unwrap();
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
            } => {
                let callable = self.lower_callable(func);

                let mut lowered_args = Vec::with_capacity(args.len());
                for arg in args {
                    if let Some(val) = self.eval_operand(body, locals, arg)? {
                        lowered_args.push(BasicMetadataValueEnum::from(val));
                    }
                }

                let call_site = self
                    .builder
                    .build_call(callable, &lowered_args, "call")
                    .unwrap();

                if let Some(ret) = call_site.try_as_basic_value().basic() {
                    self.store_local(destination.local, locals, ret, body);
                }
                let _ = self
                    .builder
                    .build_unconditional_branch(blocks[target.index()])
                    .unwrap();
            }
        }
        Ok(())
    }

    fn lower_callable(&self, func: &Operand<'gcx>) -> FunctionValue<'llvm> {
        if let Operand::Constant(c) = func {
            if let mir::ConstantKind::Function(def_id, _) = c.value {
                if let Some(&f) = self.functions.get(&def_id) {
                    return f;
                }
            }
        }

        self.functions
            .values()
            .copied()
            .next()
            .expect("at least one function")
    }

    fn eval_operand(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        op: &mir::Operand<'gcx>,
    ) -> CompileResult<Option<BasicValueEnum<'llvm>>> {
        let value = match op {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.load_local(body, locals, place.local)
            }
            mir::Operand::Constant(c) => self.lower_constant(c),
        };
        Ok(value)
    }

    fn load_local(
        &self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        local: mir::LocalId,
    ) -> Option<BasicValueEnum<'llvm>> {
        match locals[local.index()] {
            LocalStorage::Value(Some(v)) => Some(v),
            LocalStorage::Value(None) => None,
            LocalStorage::Stack(ptr) => {
                let ty = lower_type(self.context, body.locals[local].ty)?;
                Some(self.builder.build_load(ty, ptr, "load").unwrap())
            }
        }
    }

    fn store_local(
        &self,
        local: mir::LocalId,
        locals: &mut [LocalStorage<'llvm>],
        value: BasicValueEnum<'llvm>,
        body: &mir::Body<'gcx>,
    ) {
        match locals[local.index()] {
            LocalStorage::Value(_) => {
                locals[local.index()] = LocalStorage::Value(Some(value));
            }
            LocalStorage::Stack(ptr) => {
                if lower_type(self.context, body.locals[local].ty).is_some() {
                    let _ = self.builder.build_store(ptr, value).unwrap();
                }
            }
        }
    }

    fn lower_constant(&mut self, constant: &mir::Constant<'gcx>) -> Option<BasicValueEnum<'llvm>> {
        match constant.value {
            mir::ConstantKind::Bool(b) => Some(
                self.context
                    .bool_type()
                    .const_int(b as u64, false)
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::Rune(r) => Some(
                self.context
                    .i32_type()
                    .const_int(r as u64, false)
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::String(sym) => Some(self.lower_string(sym).as_basic_value_enum()),
            mir::ConstantKind::Integer(i) => self
                .int_type(constant.ty)
                .map(|(ty, _)| ty.const_int(i, false).as_basic_value_enum()),
            mir::ConstantKind::Float(f) => self
                .float_type(constant.ty)
                .map(|ty| ty.const_float(f).as_basic_value_enum()),
            mir::ConstantKind::Unit => None,
            mir::ConstantKind::Function(def_id, _) => self
                .functions
                .get(&def_id)
                .map(|f| f.as_global_value().as_pointer_value().as_basic_value_enum()),
        }
    }

    fn lower_string(&mut self, sym: Symbol) -> PointerValue<'llvm> {
        if let Some(ptr) = self.strings.get(&sym) {
            return *ptr;
        }
        let gv = self
            .builder
            .build_global_string_ptr(sym.as_str(), "str")
            .unwrap();
        let ptr = gv.as_pointer_value();
        let _ = self.strings.insert(sym, ptr);
        ptr
    }

    fn operand_ty(&self, body: &mir::Body<'gcx>, operand: &mir::Operand<'gcx>) -> Ty<'gcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => body.locals[place.local].ty,
            mir::Operand::Constant(c) => c.ty,
        }
    }

    fn int_type(&self, ty: Ty<'gcx>) -> Option<(IntType<'llvm>, bool)> {
        match ty.kind() {
            TyKind::Bool => Some((self.context.bool_type(), false)),
            TyKind::Rune => Some((self.context.i32_type(), true)),
            TyKind::Int(i) => Some((int_from_kind(self.context, i), true)),
            TyKind::UInt(u) => Some((uint_from_kind(self.context, u), false)),
            _ => None,
        }
    }

    fn float_type(&self, ty: Ty<'gcx>) -> Option<FloatType<'llvm>> {
        match ty.kind() {
            TyKind::Float(FloatTy::F32) => Some(self.context.f32_type()),
            TyKind::Float(FloatTy::F64) => Some(self.context.f64_type()),
            _ => None,
        }
    }
}

fn lower_fn_sig<'llvm>(
    context: &'llvm Context,
    sig: &crate::sema::models::LabeledFunctionSignature,
) -> FunctionType<'llvm> {
    let params: Vec<BasicMetadataTypeEnum<'llvm>> = sig
        .inputs
        .iter()
        .filter_map(|p| lower_type(context, p.ty).map(|t| t.into()))
        .collect();
    match lower_type(context, sig.output) {
        Some(ret) => ret.fn_type(&params, sig.is_variadic),
        None => context.void_type().fn_type(&params, sig.is_variadic),
    }
}

fn lower_type<'llvm>(context: &'llvm Context, ty: Ty) -> Option<BasicTypeEnum<'llvm>> {
    match ty.kind() {
        TyKind::Bool => Some(context.bool_type().into()),
        TyKind::Rune => Some(context.i32_type().into()),
        TyKind::String => todo!(),
        TyKind::Int(i) => Some(int_from_kind(context, i).into()),
        TyKind::UInt(u) => Some(uint_from_kind(context, u).into()),
        TyKind::Float(f) => Some(match f {
            FloatTy::F32 => context.f32_type().into(),
            FloatTy::F64 => context.f64_type().into(),
        }),
        TyKind::Pointer(..) | TyKind::Reference(..) => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::Tuple(items) => {
            if items.is_empty() {
                None
            } else {
                let fields: Vec<BasicTypeEnum<'llvm>> = items
                    .iter()
                    .filter_map(|t| lower_type(context, *t))
                    .collect();
                Some(context.struct_type(&fields, false).into())
            }
        }
        TyKind::FnPointer { .. } => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::Infer(_) | TyKind::Error => unreachable!(),
    }
}

fn int_from_kind<'llvm>(context: &'llvm Context, ty: IntTy) -> IntType<'llvm> {
    match ty {
        IntTy::I8 => context.i8_type(),
        IntTy::I16 => context.i16_type(),
        IntTy::I32 => context.i32_type(),
        IntTy::I64 | IntTy::ISize => context.i64_type(),
    }
}

fn uint_from_kind<'llvm>(context: &'llvm Context, ty: UIntTy) -> IntType<'llvm> {
    match ty {
        UIntTy::U8 => context.i8_type(),
        UIntTy::U16 => context.i16_type(),
        UIntTy::U32 => context.i32_type(),
        UIntTy::U64 | UIntTy::USize => context.i64_type(),
    }
}

fn is_signed(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Int(_) | TyKind::Rune)
}

fn mangle(gcx: GlobalContext, id: hir::DefinitionID) -> String {
    let ident = gcx.definition_ident(id);
    format!("{}__{}", gcx.config.identifier, ident.symbol.as_str())
}
