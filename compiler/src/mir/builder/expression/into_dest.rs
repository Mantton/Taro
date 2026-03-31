use crate::{
    compile::context::Gcx,
    hir::StdItem,
    mir::{
        self, AggregateKind, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, CastKind,
        Category, Constant, LocalId, Operand, Place, PlaceElem, Rvalue, RvalueFunc, TerminatorKind,
        builder::MirBuilder,
        optimize::async_transform::{
            AsyncRuntimeFn, find_or_register_async_runtime_function, find_std_function,
            raw_ptr_ty,
        },
    },
    sema::{
        models::{GenericArgument, GenericArguments, TyKind},
        resolve::models::DefinitionKind,
    },
    span::Span,
    thir::{self, ExprId, ExprKind, FieldIndex},
    unpack,
    utils::intern::List,
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn expr_into_dest(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<()> {
        let expr = &self.thir.exprs[expr_id];
        let block_and = match &expr.kind {
            ExprKind::Local(..) => {
                let place = unpack!(block = self.as_place(block, expr_id));
                let operand = if self.is_type_copyable(expr.ty) {
                    Operand::Copy(place)
                } else {
                    Operand::Move(place)
                };
                let rvalue = Rvalue::Use(operand);
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Reference {
                mutable,
                expr: ref_expr,
            } => {
                // Take the address of the place, preserving mutability.
                let place = unpack!(block = self.as_place(block, *ref_expr));
                let rvalue = Rvalue::Ref {
                    mutable: *mutable,
                    place,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Logical { op, lhs, rhs } => {
                // Short-circuiting logical ops.
                let lhs_op = unpack!(block = self.as_operand(block, *lhs));
                let then_block = self.new_block_with_note("logical-then".into());
                let else_block = self.new_block_with_note("logical-else".into());
                self.terminate(
                    block,
                    expr.span,
                    TerminatorKind::if_(lhs_op, then_block, else_block),
                );

                // For `&&`: false short-circuits; true continues to RHS.
                // For `||`: true short-circuits; false continues to RHS.
                let (short_block, cont_block, short_val) = match op {
                    mir::LogicalOperator::And => (else_block, then_block, false),
                    mir::LogicalOperator::Or => (then_block, else_block, true),
                };

                // Short-circuit path writes the known value.
                let short_const = Constant {
                    ty: expr.ty,
                    value: mir::ConstantKind::Bool(short_val),
                };
                self.push_assign(
                    short_block,
                    destination.clone(),
                    Rvalue::Use(Operand::Constant(short_const)),
                    expr.span,
                );

                // Continue with RHS evaluation.
                let rhs_block = self
                    .expr_into_dest(destination.clone(), cont_block, *rhs)
                    .into_block();

                // Join both paths.
                let join = self.new_block_with_note("logical-join".into());
                let rhs_incoming = self.goto_if_fallthrough(rhs_block, join, expr.span);
                let short_incoming = self.goto_if_fallthrough(short_block, join, expr.span);
                if !rhs_incoming && !short_incoming {
                    self.terminate(join, expr.span, TerminatorKind::Unreachable);
                }
                join.unit()
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let destination_then = destination.clone();
                let (then_end, mut else_blk) = self.in_if_then_scope(expr.span, |this| {
                    let then_blk = this.then_else_break(block, *cond).into_block();
                    this.expr_into_dest(destination_then, then_blk, *then_expr)
                });

                if let Some(&expr) = else_expr.as_ref() {
                    else_blk = self
                        .expr_into_dest(destination, else_blk, expr)
                        .into_block();
                } else {
                    self.push_assign_unit(else_blk, expr.span, destination, self.gcx);
                }

                let join_block = self.new_block_with_note("Join Block".into());
                let then_incoming = self.goto_if_fallthrough(then_end, join_block, expr.span);
                let else_incoming = self.goto_if_fallthrough(else_blk, join_block, expr.span);
                if !then_incoming && !else_incoming {
                    self.terminate(join_block, expr.span, TerminatorKind::Unreachable);
                }
                join_block.unit()
            }
            ExprKind::Match {
                scrutinee, arms, ..
            } => self.lower_match_expr(destination, block, expr_id, *scrutinee, arms),
            ExprKind::Return { value } => {
                let place = Place::from_local(self.body.return_local);
                if let Some(&value) = value.as_ref() {
                    block = self.expr_into_dest(place, block, value).into_block();
                } else {
                    self.push_assign_unit(block, expr.span, place, self.gcx);
                }
                self.record_return_edge(block, expr.span)
            }
            ExprKind::Break => self.record_break_edge(block, expr.span),
            ExprKind::Continue => self.record_continue_edge(block, expr.span),
            ExprKind::Assign { .. } | ExprKind::AssignOp { .. } => {
                block = self.lower_statement_expression(block, expr_id).into_block();
                self.push_assign_unit(block, expr.span, destination, self.gcx);
                block.unit()
            }
            ExprKind::Call {
                callee,
                args,
                is_async,
            } => self.lower_call_into_dest(destination, block, *callee, args, *is_async, expr.span),
            ExprKind::ListLiteral {
                elements,
                element_ty,
            } => {
                block = self.lower_list_literal(
                    block,
                    destination,
                    elements,
                    expr.ty,
                    *element_ty,
                    expr.span,
                );
                block.unit()
            }
            ExprKind::BoxExistential { value, .. } => {
                let operand = unpack!(block = self.as_operand(block, *value));
                let rvalue = Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::BoxExistential,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::ExistentialUpcast { value, .. } => {
                let operand = unpack!(block = self.as_operand(block, *value));
                let rvalue = Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::ExistentialUpcast,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Make { value } => {
                let value_ty = self.thir.exprs[*value].ty;
                let ptr_local = self.new_temp_with_ty(
                    self.gcx
                        .store
                        .interners
                        .intern_ty(crate::sema::models::TyKind::Pointer(
                            value_ty,
                            crate::hir::Mutability::Immutable,
                        )),
                    expr.span,
                );
                let alloc_rvalue = Rvalue::Alloc { ty: value_ty };
                self.push_assign(block, Place::from_local(ptr_local), alloc_rvalue, expr.span);

                // Evaluate initializer into a temp first so calls never write
                // directly into fresh pointee memory.
                let tmp_local = self.new_temp_with_ty(value_ty, expr.span);
                block = self
                    .expr_into_dest(Place::from_local(tmp_local), block, *value)
                    .into_block();

                // Initialize *ptr_local using an init+take copy.
                let dest_place = Place {
                    local: ptr_local,
                    projection: vec![mir::PlaceElem::Deref],
                };
                let init_value = Rvalue::Use(Operand::copy_with(
                    Place::from_local(tmp_local),
                    mir::CopyModifiers {
                        init: true,
                        take: true,
                    },
                ));
                self.push_assign(block, dest_place, init_value, expr.span);

                // Return the pointer.
                let rvalue = Rvalue::Use(Operand::Copy(Place::from_local(ptr_local)));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Block(block_id) => self.lower_block(destination, block, *block_id),
            ExprKind::Adt(adt_expression) => {
                // Evaluate each field into an operand in declaration order.
                let field_count = match adt_expression.definition.kind {
                    crate::sema::models::AdtKind::Struct => {
                        let def = self.gcx.get_struct_definition(adt_expression.definition.id);
                        def.fields.len()
                    }
                    crate::sema::models::AdtKind::Enum => {
                        let Some(variant_index) = adt_expression.variant_index else {
                            unreachable!()
                        };
                        let variant = self
                            .gcx
                            .enum_variant_by_index(adt_expression.definition.id, variant_index);
                        match variant.kind {
                            crate::sema::models::EnumVariantKind::Unit => 0,
                            crate::sema::models::EnumVariantKind::Tuple(enum_variant_fields) => {
                                enum_variant_fields.len()
                            }
                        }
                    }
                };

                let mut tmp: Vec<Option<Operand<'ctx>>> = vec![None; field_count];
                for field in &adt_expression.fields {
                    let operand = unpack!(block = self.as_operand(block, field.expression));
                    tmp[field.index.index()] = Some(operand);
                }
                let fields: IndexVec<FieldIndex, Operand<'ctx>> = IndexVec::from_vec(
                    tmp.into_iter()
                        .map(|o| o.expect("missing struct field operand"))
                        .collect(),
                );

                let rvalue = Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: adt_expression.definition.id,
                        variant_index: adt_expression.variant_index,
                        generic_args: adt_expression.generic_args,
                    },
                    fields,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Deref(..) | ExprKind::Field { .. } | ExprKind::Upvar { .. } => {
                debug_assert!(matches!(Category::of(&expr.kind), Category::Place));
                let place = unpack!(block = self.as_place(block, expr_id));
                let operand = if self.is_type_copyable(expr.ty) {
                    Operand::Copy(place)
                } else {
                    Operand::Move(place)
                };
                let rvalue = Rvalue::Use(operand);
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Closure {
                def_id, captures, ..
            } => {
                // Build closure environment by evaluating each capture expression
                let capture_operands: Vec<Operand<'ctx>> = captures
                    .iter()
                    .map(|cap| {
                        // For now, captures are empty, so this won't execute
                        unpack!(block = self.as_operand(block, cap.capture_expr))
                    })
                    .collect();

                let fields: IndexVec<FieldIndex, Operand<'ctx>> =
                    IndexVec::from_vec(capture_operands);

                let captured_generics = match expr.ty.kind() {
                    TyKind::Closure {
                        closure_def_id,
                        captured_generics,
                        ..
                    } => {
                        debug_assert!(
                            closure_def_id == *def_id,
                            "closure expression def_id should match closure type def_id"
                        );
                        captured_generics
                    }
                    _ => GenericArguments::empty(),
                };

                let rvalue = Rvalue::Aggregate {
                    kind: AggregateKind::Closure {
                        def_id: *def_id,
                        captured_generics,
                    },
                    fields,
                };

                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Await { future } => {
                if let ExprKind::Call {
                    callee,
                    args,
                    is_async: true,
                } = &self.thir.exprs[*future].kind
                {
                    if self.is_hidden_task_result_intrinsic(*callee) {
                        return self.lower_awaited_task_result(destination, block, args, expr.span);
                    }
                    if self.is_hidden_task_group_next_intrinsic(*callee) {
                        return self.lower_awaited_task_group_next(
                            destination,
                            block,
                            args,
                            expr.span,
                        );
                    }
                }
                let future_op = if matches!(
                    self.thir.exprs[*future].kind,
                    ExprKind::Call { is_async: true, .. }
                ) {
                    let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), expr.span);
                    block = self
                        .expr_into_dest(Place::from_local(handle_local), block, *future)
                        .into_block();
                    Operand::Copy(Place::from_local(handle_local))
                } else {
                    unpack!(block = self.as_operand(block, *future))
                };
                let resume = self.new_block_with_note("await-resume".into());
                self.terminate(
                    block,
                    expr.span,
                    TerminatorKind::Yield {
                        value: future_op,
                        resume,
                        resume_arg: destination.clone(),
                    },
                );
                resume.unit()
            }
            ExprKind::Tuple { .. }
            | ExprKind::Array { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Literal(..)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Cast { .. }
            | ExprKind::ExistentialTryCast { .. }
            | ExprKind::ExistentialTypeIs { .. }
            | ExprKind::ClosureToFnPointer { .. }
            | ExprKind::Zst { .. } => {
                debug_assert!(match Category::of(&expr.kind) {
                    // should be handled above
                    Category::Rvalue(RvalueFunc::Into) => false,

                    // must be handled above or else we get an
                    // infinite loop in the builder; see
                    // e.g., `ExprKind::VarRef` above
                    Category::Place => false,

                    _ => true,
                });

                let rvalue = unpack!(block = self.as_local_rvalue(block, expr_id));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
        };

        block_and
    }

    fn lower_call_into_dest(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        is_async: bool,
        span: Span,
    ) -> BlockAnd<()> {
        if self.is_hidden_spawn_intrinsic(callee) {
            return self.lower_spawn_call(destination, block, args, span);
        }
        if self.is_hidden_wait_readable_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::WaitReadable,
            );
        }
        if self.is_hidden_wait_writable_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::WaitWritable,
            );
        }
        if self.is_hidden_sleep_intrinsic(callee) {
            return self.lower_sleep_call(destination, block, args, span);
        }
        if self.is_hidden_is_task_cancelled_intrinsic(callee) {
            return self.lower_is_task_cancelled_call(destination, block, args, span);
        }
        if self.is_hidden_cancel_task_intrinsic(callee) {
            return self.lower_cancel_task_call(destination, block, args, span);
        }
        if self.is_hidden_task_result_intrinsic(callee) {
            return self.lower_task_result_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_create_intrinsic(callee) {
            return self.lower_task_group_create_call(destination, block, callee, args, span);
        }
        if self.is_hidden_task_group_spawn_intrinsic(callee) {
            return self.lower_task_group_spawn_call(destination, block, callee, args, span);
        }
        if self.is_hidden_task_group_next_intrinsic(callee) {
            return self.lower_task_group_next_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_close_intrinsic(callee) {
            return self.lower_task_group_close_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_cancel_intrinsic(callee) {
            return self.lower_task_group_cancel_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_destroy_intrinsic(callee) {
            return self.lower_task_group_destroy_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_destroy_and_rethrow_intrinsic(callee) {
            return self.lower_task_group_destroy_and_rethrow_call(destination, block, args, span);
        }
        if self.is_hidden_panic_payload_message_intrinsic(callee) {
            return self.lower_panic_payload_message_call(destination, block, args, span);
        }
        if self.is_hidden_panic_payload_rethrow_intrinsic(callee) {
            return self.lower_panic_payload_rethrow_call(destination, block, args, span);
        }

        let shadow_resync_locals = self.shadow_resync_locals_for_call(args);

        let mut variadic_split_idx = None;
        let callee_expr = &self.thir.exprs[callee];
        let is_known_variadic = match callee_expr.kind {
            ExprKind::Zst { id, .. } => {
                matches!(
                    self.gcx.try_definition_kind(id),
                    Some(
                        DefinitionKind::Function
                            | DefinitionKind::AssociatedFunction
                            | DefinitionKind::AssociatedOperator
                    )
                ) && self.gcx.get_signature(id).is_variadic
            }
            _ => false,
        };

        let callee_ty = callee_expr.ty;
        let closure_self_param_ty =
            if let crate::sema::models::TyKind::Closure { closure_def_id, .. } = callee_ty.kind() {
                self.gcx
                    .get_signature(closure_def_id)
                    .inputs
                    .first()
                    .map(|param| param.ty)
            } else if let crate::sema::models::TyKind::Parameter(_) = callee_ty.kind() {
                self.get_callable_trait_self_param_ty(callee_ty)
            } else {
                None
            };
        let callable_self_place = if closure_self_param_ty.is_some() {
            Some(unpack!(block = self.as_place(block, callee)))
        } else {
            None
        };

        let function = if let Some(place) = callable_self_place.clone() {
            Operand::Copy(place)
        } else if is_async {
            unpack!(block = self.async_callable_operand(block, callee, callee_ty))
        } else {
            unpack!(block = self.as_local_operand(block, callee))
        };

        let closure_self_arg: Option<Operand<'ctx>> =
            closure_self_param_ty.and_then(|self_param_ty| {
                let closure_place = callable_self_place.clone()?;
                match self_param_ty.kind() {
                    crate::sema::models::TyKind::Reference(_, mutability) => {
                        let ref_local = self.new_temp_with_ty(self_param_ty, span);
                        self.push_assign(
                            block,
                            Place::from_local(ref_local),
                            Rvalue::Ref {
                                mutable: matches!(mutability, crate::hir::Mutability::Mutable),
                                place: closure_place,
                            },
                            span,
                        );
                        Some(Operand::Copy(Place::from_local(ref_local)))
                    }
                    crate::sema::models::TyKind::Pointer(_, mutability) => {
                        let ref_ty = self.gcx.store.interners.intern_ty(
                            crate::sema::models::TyKind::Reference(callee_ty, mutability),
                        );
                        let ref_local = self.new_temp_with_ty(ref_ty, span);
                        self.push_assign(
                            block,
                            Place::from_local(ref_local),
                            Rvalue::Ref {
                                mutable: matches!(mutability, crate::hir::Mutability::Mutable),
                                place: closure_place,
                            },
                            span,
                        );

                        let ptr_local = self.new_temp_with_ty(self_param_ty, span);
                        self.push_assign(
                            block,
                            Place::from_local(ptr_local),
                            Rvalue::Cast {
                                kind: CastKind::Pointer,
                                operand: Operand::Copy(Place::from_local(ref_local)),
                                ty: self_param_ty,
                            },
                            span,
                        );

                        Some(Operand::Copy(Place::from_local(ptr_local)))
                    }
                    _ => Some(Operand::Move(closure_place)),
                }
            });
        if let crate::sema::models::TyKind::FnPointer { inputs, .. } = callee_ty.kind() {
            let param_count = inputs.len();
            if is_known_variadic && param_count > 0 {
                let list_idx = param_count - 1;
                if list_idx <= args.len() {
                    let needs_pack = if args.len() != param_count {
                        true
                    } else {
                        let last_param_ty = inputs[list_idx];
                        let last_arg_ty = self.thir.exprs[args[list_idx]].ty;
                        last_arg_ty != last_param_ty
                    };
                    if needs_pack {
                        variadic_split_idx = Some(list_idx);
                    }
                }
            } else if args.len() > param_count && param_count > 0 {
                variadic_split_idx = Some(param_count - 1);
            }
        }

        let fn_trait_args_ty = if let crate::sema::models::TyKind::Parameter(_) = callee_ty.kind() {
            self.get_fn_trait_args_type(callee_ty)
        } else {
            None
        };

        let (fixed_args, variadic_list_operand) = if let Some(split) = variadic_split_idx {
            let (fixed, var_args) = args.split_at(split);
            let inputs =
                if let crate::sema::models::TyKind::FnPointer { inputs, .. } = callee_ty.kind() {
                    inputs
                } else {
                    panic!("callee must be fn pointer");
                };
            let list_ty = inputs[inputs.len() - 1];
            let elem_ty = if let crate::sema::models::TyKind::Adt(_, args) = list_ty.kind() {
                if let Some(crate::sema::models::GenericArgument::Type(ty)) = args.get(0) {
                    *ty
                } else {
                    panic!("List must have generic arg");
                }
            } else {
                panic!("Variadic param must be List");
            };

            let list_operand = unpack!(
                block = self.lower_variadic_sequence(block, var_args, list_ty, elem_ty, span)
            );

            let fixed_operands: Vec<Operand<'ctx>> = fixed
                .iter()
                .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                .collect();
            (fixed_operands, Some(list_operand))
        } else if let Some(args_ty) = fn_trait_args_ty {
            if let crate::sema::models::TyKind::Tuple(elem_tys) = args_ty.kind() {
                if args.len() == 1 {
                    let arg_expr = &self.thir.exprs[args[0]];
                    if let ExprKind::Tuple { fields } = &arg_expr.kind {
                        let unpacked: Vec<Operand<'ctx>> = fields
                            .iter()
                            .map(|field| unpack!(block = self.as_operand(block, *field)))
                            .collect();
                        (unpacked, None)
                    } else if matches!(arg_expr.ty.kind(), crate::sema::models::TyKind::Tuple(_)) {
                        let tuple_place = unpack!(block = self.as_place(block, args[0]));
                        let unpacked: Vec<Operand<'ctx>> = elem_tys
                            .iter()
                            .enumerate()
                            .map(|(i, &ty)| {
                                let field_place = Place {
                                    local: tuple_place.local,
                                    projection: {
                                        let mut proj = tuple_place.projection.clone();
                                        proj.push(PlaceElem::Field(FieldIndex::from_usize(i), ty));
                                        proj
                                    },
                                };
                                Operand::Copy(field_place)
                            })
                            .collect();
                        (unpacked, None)
                    } else {
                        let all_args = args
                            .iter()
                            .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                            .collect();
                        (all_args, None)
                    }
                } else {
                    let all_args = args
                        .iter()
                        .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                        .collect();
                    (all_args, None)
                }
            } else {
                let all_args = args
                    .iter()
                    .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                    .collect();
                (all_args, None)
            }
        } else {
            let all_args = args
                .iter()
                .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                .collect();
            (all_args, None)
        };

        let mut final_args = Vec::new();
        if let Some(self_arg) = closure_self_arg {
            final_args.push(self_arg);
        }
        final_args.extend(fixed_args);
        if let Some(list) = variadic_list_operand {
            final_args.push(list);
        }

        let next = self.new_block();
        let unwind = self.call_unwind_for_callee(&function, span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: function,
                args: final_args,
                destination,
                target: next,
                unwind,
            },
        );
        self.push_shadow_resync(next, shadow_resync_locals, span);
        next.unit()
    }

    fn lower_spawn_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [thunk] = args else {
            panic!("ICE: spawn lowering expects exactly one thunk argument");
        };

        let task_ty = self.place_ty(&destination);
        let TyKind::Adt(def, task_args) = task_ty.kind() else {
            panic!("ICE: spawn destination must be Task[T]");
        };
        let Some(task_def_id) = self.gcx.std_item_def(StdItem::Task) else {
            panic!("ICE: Task std item missing");
        };
        assert_eq!(
            def.id, task_def_id,
            "ICE: spawn destination must be Task[T]"
        );
        let Some(GenericArgument::Type(task_output_ty)) = task_args.first().copied() else {
            panic!("ICE: Task[T] must carry its output type");
        };

        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        block = self
            .lower_call_into_dest(
                Place::from_local(handle_local),
                block,
                *thunk,
                &[],
                true,
                span,
            )
            .into_block();

        let size_local = unpack!(block = self.lower_size_of_type_to_local(block, task_output_ty, span));
        let task_token_local = self.new_temp_with_ty(self.gcx.types.uint, span);

        let executor_spawn_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::Spawn, span);
        let executor_spawn_ty = self.gcx.get_type(executor_spawn_id);
        let after_spawn = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: executor_spawn_ty,
                    value: mir::ConstantKind::Function(
                        executor_spawn_id,
                        GenericArguments::empty(),
                        executor_spawn_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(handle_local)),
                    Operand::Copy(Place::from_local(size_local)),
                ],
                destination: Place::from_local(task_token_local),
                target: after_spawn,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let fields = IndexVec::from_vec(vec![Operand::Copy(Place::from_local(task_token_local))]);
        self.push_assign(
            after_spawn,
            destination,
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: task_def_id,
                    variant_index: None,
                    generic_args: task_args,
                },
                fields,
            },
            span,
        );

        after_spawn.unit()
    }

    fn lower_sleep_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [duration] = args else {
            panic!("ICE: sleep lowering expects exactly one duration argument");
        };

        let destination_ty = self.place_ty(&destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: sleep intrinsic must lower into an async handle destination"
        );

        let duration_local = unpack!(block = self.as_temp(block, *duration));
        let duration_place = Place::from_local(duration_local);
        let sleep_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::Sleep, span);
        let sleep_ty = self.gcx.get_type(sleep_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: sleep_ty,
                    value: mir::ConstantKind::Function(
                        sleep_id,
                        GenericArguments::empty(),
                        sleep_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(duration_secs_place(self.gcx, duration_place.clone())),
                    Operand::Copy(duration_nanos_place(self.gcx, duration_place)),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_cancel_task_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [task] = args else {
            panic!("ICE: cancel task lowering expects exactly one task argument");
        };

        let token_local = unpack!(block = self.lower_task_token_local(block, *task, span));
        let cancel_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::CancelTask, span);
        let cancel_ty = self.gcx.get_type(cancel_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: cancel_ty,
                    value: mir::ConstantKind::Function(
                        cancel_id,
                        GenericArguments::empty(),
                        cancel_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_task_result_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [task] = args else {
            panic!("ICE: task result lowering expects exactly one task argument");
        };

        let destination_ty = self.place_ty(&destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: task result intrinsic must lower into an async handle destination"
        );

        let token_local = unpack!(block = self.lower_task_token_local(block, *task, span));
        let from_spawned_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::FromSpawnedChecked,
            span,
        );
        let from_spawned_ty = self.gcx.get_type(from_spawned_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: from_spawned_ty,
                    value: mir::ConstantKind::Function(
                        from_spawned_id,
                        GenericArguments::empty(),
                        from_spawned_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_awaited_task_result(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [task] = args else {
            panic!("ICE: awaited task result lowering expects exactly one task argument");
        };

        let destination_ty = self.place_ty(&destination);
        let TyKind::Adt(result_def, result_args) = destination_ty.kind() else {
            panic!("ICE: awaited task result destination must be Result[T, E]");
        };
        let ready_ty = result_args
            .first()
            .copied()
            .and_then(GenericArgument::ty)
            .unwrap_or_else(|| panic!("ICE: Result[T, E] is missing value type"));
        let ready_is_never = matches!(ready_ty.kind(), TyKind::Never);

        let token_local = unpack!(block = self.lower_task_token_local(block, *task, span));
        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let (ready_local, resume_local) = if ready_is_never {
            (
                None,
                self.new_temp_with_ty(self.gcx.types.uint8, span),
            )
        } else {
            let ready_local = self.new_temp_with_ty(ready_ty, span);
            (Some(ready_local), ready_local)
        };

        let from_spawned_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::FromSpawnedChecked,
            span,
        );
        let from_spawned_ty = self.gcx.get_type(from_spawned_id);
        let after_handle = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: from_spawned_ty,
                    value: mir::ConstantKind::Function(
                        from_spawned_id,
                        GenericArguments::empty(),
                        from_spawned_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(handle_local),
                target: after_handle,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let resume = self.new_block_with_note("task-result-resume".into());
        self.terminate(
            after_handle,
            span,
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(handle_local)),
                resume,
                resume_arg: Place::from_local(resume_local),
            },
        );

        let status_local = self.new_temp_with_ty(self.gcx.types.uint8, span);
        let status_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskCompletionStatus,
            span,
        );
        let status_ty = self.gcx.get_type(status_id);
        let after_status = self.new_block();
        self.terminate(
            resume,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: status_ty,
                    value: mir::ConstantKind::Function(
                        status_id,
                        GenericArguments::empty(),
                        status_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(status_local),
                target: after_status,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        // Take the panic payload pointer BEFORE reclaiming the slot (reclaim clears panic_info).
        let ptr_u8_mut_ty = raw_ptr_ty(self.gcx, self.gcx.types.uint8, crate::hir::Mutability::Mutable);
        let raw_ptr_local = self.new_temp_with_ty(ptr_u8_mut_ty, span);
        let take_panic_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TakeTaskPanicInfo,
            span,
        );
        let take_panic_ty = self.gcx.get_type(take_panic_id);
        let after_take_panic = self.new_block();
        self.terminate(
            after_status,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: take_panic_ty,
                    value: mir::ConstantKind::Function(
                        take_panic_id,
                        GenericArguments::empty(),
                        take_panic_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(raw_ptr_local),
                target: after_take_panic,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let reclaim_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::ReclaimSpawned, span);
        let reclaim_ty = self.gcx.get_type(reclaim_id);
        let reclaim_dest = self.new_temp_with_ty(self.gcx.types.void, span);
        let after_reclaim = self.new_block();
        self.terminate(
            after_take_panic,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: reclaim_ty,
                    value: mir::ConstantKind::Function(
                        reclaim_id,
                        GenericArguments::empty(),
                        reclaim_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(reclaim_dest),
                target: after_reclaim,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let ok_block = self.new_block_with_note("task-result-ok".into());
        let cancelled_block = self.new_block_with_note("task-result-cancelled".into());
        let panicked_block = self.new_block_with_note("task-result-panicked".into());
        let join_block = self.new_block_with_note("task-result-join".into());
        self.terminate(
            after_reclaim,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(status_local)),
                targets: vec![(1, ok_block), (2, cancelled_block)],
                otherwise: panicked_block,
            },
        );

        // ok branch: Result.ok(ready_value)
        if let Some(ready_local) = ready_local {
            self.push_assign(
                ok_block,
                destination.clone(),
                Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: result_def.id,
                        variant_index: Some(thir::VariantIndex::from_usize(0)),
                        generic_args: result_args,
                    },
                    fields: IndexVec::from_vec(vec![Operand::Move(Place::from_local(ready_local))]),
                },
                span,
            );
            self.goto(ok_block, join_block, span);
        } else {
            // `Task[!]` cannot complete with an `ok` value.
            self.terminate(ok_block, span, TerminatorKind::Unreachable);
        }

        let err_ty = result_args
            .get(1)
            .copied()
            .and_then(GenericArgument::ty)
            .unwrap_or_else(|| panic!("ICE: Result[T, E] is missing error type"));
        let TyKind::Adt(err_def, err_args) = err_ty.kind() else {
            panic!("ICE: Task.result() error type must be an enum");
        };

        // cancelled branch: Result.err(TaskError.cancelled)  [variant 0, no fields]
        let cancelled_error_local = self.new_temp_with_ty(err_ty, span);
        self.push_assign(
            cancelled_block,
            Place::from_local(cancelled_error_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: err_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(0)),
                    generic_args: err_args,
                },
                fields: IndexVec::new(),
            },
            span,
        );
        self.push_assign(
            cancelled_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: result_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: result_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Move(Place::from_local(cancelled_error_local))]),
            },
            span,
        );
        self.goto(cancelled_block, join_block, span);

        // panicked branch: Result.err(TaskError.panicked(PanicPayload { data: raw_ptr }))  [variant 1]
        let panic_payload_def_id = self.gcx.std_item_def(StdItem::PanicPayload)
            .unwrap_or_else(|| panic!("ICE: PanicPayload std item missing"));
        let panic_payload_ty = self.gcx.get_type(panic_payload_def_id);
        let TyKind::Adt(panic_payload_adt, panic_payload_args) = panic_payload_ty.kind() else {
            panic!("ICE: PanicPayload must be a struct");
        };
        let payload_local = self.new_temp_with_ty(panic_payload_ty, span);
        self.push_assign(
            panicked_block,
            Place::from_local(payload_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: panic_payload_adt.id,
                    variant_index: None,
                    generic_args: panic_payload_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Copy(Place::from_local(raw_ptr_local))]),
            },
            span,
        );
        let panicked_error_local = self.new_temp_with_ty(err_ty, span);
        self.push_assign(
            panicked_block,
            Place::from_local(panicked_error_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: err_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: err_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Move(Place::from_local(payload_local))]),
            },
            span,
        );
        self.push_assign(
            panicked_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: result_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: result_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Move(Place::from_local(panicked_error_local))]),
            },
            span,
        );
        self.goto(panicked_block, join_block, span);

        join_block.unit()
    }

    fn lower_task_group_create_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [cancel_on_panic] = args else {
            panic!("ICE: task group create lowering expects exactly one policy argument");
        };

        let result_ty = intrinsic_type_arg(self.thir, callee, 0);
        let policy_local =
            unpack!(block = self.lower_bool_to_u8_local(block, *cancel_on_panic, span));
        let size_local = unpack!(block = self.lower_size_of_type_to_local(block, result_ty, span));
        let create_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskGroupCreate,
            span,
        );
        let create_ty = self.gcx.get_type(create_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: create_ty,
                    value: mir::ConstantKind::Function(
                        create_id,
                        GenericArguments::empty(),
                        create_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(size_local)),
                    Operand::Copy(Place::from_local(policy_local)),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_task_group_spawn_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id, thunk] = args else {
            panic!("ICE: task group spawn lowering expects group id and thunk");
        };

        let result_ty = intrinsic_type_arg(self.thir, callee, 0);
        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        block = self
            .lower_call_into_dest(
                Place::from_local(handle_local),
                block,
                *thunk,
                &[],
                true,
                span,
            )
            .into_block();

        let size_local = unpack!(block = self.lower_size_of_type_to_local(block, result_ty, span));
        let token_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        let spawn_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::TaskGroupSpawn, span);
        let spawn_ty = self.gcx.get_type(spawn_id);
        let after_spawn = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: spawn_ty,
                    value: mir::ConstantKind::Function(
                        spawn_id,
                        GenericArguments::empty(),
                        spawn_ty,
                    ),
                }),
                args: vec![
                    group_operand,
                    Operand::Copy(Place::from_local(handle_local)),
                    Operand::Copy(Place::from_local(size_local)),
                ],
                destination: Place::from_local(token_local),
                target: after_spawn,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        self.push_assign_unit(after_spawn, span, destination, self.gcx);
        after_spawn.unit()
    }

    fn lower_task_group_next_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: task group next lowering expects exactly one group id argument");
        };

        let destination_ty = self.place_ty(&destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: task group next intrinsic must lower into an async handle destination"
        );

        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let next_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::GroupNext, span);
        let next_ty = self.gcx.get_type(next_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: next_ty,
                    value: mir::ConstantKind::Function(next_id, GenericArguments::empty(), next_ty),
                }),
                args: vec![group_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_awaited_task_group_next(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: awaited task group next lowering expects exactly one group id argument");
        };

        let destination_ty = self.place_ty(&destination);
        let TyKind::Adt(optional_def, optional_args) = destination_ty.kind() else {
            panic!("ICE: awaited task group next destination must be Optional[T]");
        };
        let ready_ty = optional_args
            .first()
            .copied()
            .and_then(GenericArgument::ty)
            .unwrap_or_else(|| panic!("ICE: Optional[T] is missing payload type"));

        let group_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        self.push_assign(
            block,
            Place::from_local(group_local),
            Rvalue::Use(group_operand),
            span,
        );

        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let ready_local = self.new_temp_with_ty(ready_ty, span);
        let next_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::GroupNext, span);
        let next_ty = self.gcx.get_type(next_id);
        let after_handle = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: next_ty,
                    value: mir::ConstantKind::Function(next_id, GenericArguments::empty(), next_ty),
                }),
                args: vec![Operand::Copy(Place::from_local(group_local))],
                destination: Place::from_local(handle_local),
                target: after_handle,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let resume = self.new_block_with_note("task-group-next-resume".into());
        self.terminate(
            after_handle,
            span,
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(handle_local)),
                resume,
                resume_arg: Place::from_local(ready_local),
            },
        );

        let status_local = self.new_temp_with_ty(self.gcx.types.uint8, span);
        let status_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskGroupNextStatus,
            span,
        );
        let status_ty = self.gcx.get_type(status_id);
        let after_status = self.new_block();
        self.terminate(
            resume,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: status_ty,
                    value: mir::ConstantKind::Function(
                        status_id,
                        GenericArguments::empty(),
                        status_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(group_local))],
                destination: Place::from_local(status_local),
                target: after_status,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let some_block = self.new_block_with_note("task-group-next-some".into());
        let none_block = self.new_block_with_note("task-group-next-none".into());
        let join_block = self.new_block_with_note("task-group-next-join".into());
        self.terminate(
            after_status,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(status_local)),
                targets: vec![(1, some_block)],
                otherwise: none_block,
            },
        );

        self.push_assign(
            some_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: optional_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(0)),
                    generic_args: optional_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Move(Place::from_local(ready_local))]),
            },
            span,
        );
        self.goto(some_block, join_block, span);

        self.push_assign(
            none_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: optional_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: optional_args,
                },
                fields: IndexVec::new(),
            },
            span,
        );
        self.goto(none_block, join_block, span);

        join_block.unit()
    }

    fn lower_task_group_close_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        self.lower_task_group_void_call(
            destination,
            block,
            args,
            span,
            AsyncRuntimeFn::TaskGroupClose,
        )
    }

    fn lower_task_group_cancel_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        self.lower_task_group_void_call(
            destination,
            block,
            args,
            span,
            AsyncRuntimeFn::TaskGroupCancelAll,
        )
    }

    fn lower_task_group_destroy_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        self.lower_task_group_void_call(
            destination,
            block,
            args,
            span,
            AsyncRuntimeFn::TaskGroupDestroy,
        )
    }

    fn lower_task_group_destroy_and_rethrow_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: task group runtime call expects exactly one group id argument");
        };

        let mut block = block;
        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let call_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskGroupDestroyAndRethrowPanic,
            span,
        );
        let call_ty = self.gcx.get_type(call_id);
        let next = self.new_block();
        let unwind = self.call_unwind_action(span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: call_ty,
                    value: mir::ConstantKind::Function(call_id, GenericArguments::empty(), call_ty),
                }),
                args: vec![group_operand],
                destination,
                target: next,
                // This runtime helper re-panics when a child panic was recorded,
                // so it must unwind through active cleanup/defer scopes.
                unwind,
            },
        );

        next.unit()
    }

    fn lower_task_group_void_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
        which: AsyncRuntimeFn,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: task group runtime call expects exactly one group id argument");
        };

        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let call_id = find_or_register_async_runtime_function(self.gcx, which, span);
        let call_ty = self.gcx.get_type(call_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: call_ty,
                    value: mir::ConstantKind::Function(call_id, GenericArguments::empty(), call_ty),
                }),
                args: vec![group_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_task_token_local(
        &mut self,
        mut block: BasicBlockId,
        task: ExprId,
        span: Span,
    ) -> BlockAnd<LocalId> {
        let mut task_place = unpack!(block = self.as_place(block, task));
        if matches!(
            self.thir.exprs[task].ty.kind(),
            TyKind::Reference(..) | TyKind::Pointer(..)
        ) {
            task_place.projection.push(PlaceElem::Deref);
        }
        let token_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        self.push_assign(
            block,
            Place::from_local(token_local),
            Rvalue::Use(Operand::Copy(task_token_place(self.gcx, task_place))),
            span,
        );
        block.and(token_local)
    }

    fn lower_size_of_type_to_local(
        &mut self,
        block: BasicBlockId,
        ty: crate::sema::models::Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<LocalId> {
        let size_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        if matches!(ty.kind(), TyKind::Never) {
            self.push_assign(
                block,
                Place::from_local(size_local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: self.gcx.types.uint,
                    value: mir::ConstantKind::Integer(0),
                })),
                span,
            );
            return block.and(size_local);
        }
        let size_of_id = find_std_function(self.gcx, "mem", "sizeOf", span)
            .unwrap_or_else(|_| panic!("lowering requires std.mem.sizeOf"));
        let size_of_ty = self.gcx.get_type(size_of_id);
        let after_size = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: size_of_ty,
                    value: mir::ConstantKind::Function(
                        size_of_id,
                        self.gcx
                            .store
                            .interners
                            .intern_generic_args(vec![GenericArgument::Type(ty)]),
                        size_of_ty,
                    ),
                }),
                args: vec![],
                destination: Place::from_local(size_local),
                target: after_size,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        after_size.and(size_local)
    }

    fn lower_bool_to_u8_local(
        &mut self,
        mut block: BasicBlockId,
        expr: ExprId,
        span: Span,
    ) -> BlockAnd<LocalId> {
        let policy_operand = unpack!(block = self.as_operand(block, expr));
        let policy_local = self.new_temp_with_ty(self.gcx.types.uint8, span);
        self.push_assign(
            block,
            Place::from_local(policy_local),
            Rvalue::Cast {
                operand: policy_operand,
                ty: self.gcx.types.uint8,
                kind: CastKind::Numeric,
            },
            span,
        );
        block.and(policy_local)
    }

    fn lower_io_wait_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
        which: AsyncRuntimeFn,
    ) -> BlockAnd<()> {
        let [source_id] = args else {
            panic!("ICE: async io wait lowering expects exactly one source id argument");
        };

        let destination_ty = self.place_ty(&destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: async io wait intrinsic must lower into an async handle destination"
        );

        let source_id_operand = unpack!(block = self.as_operand(block, *source_id));
        let wait_id = find_or_register_async_runtime_function(self.gcx, which, span);
        let wait_ty = self.gcx.get_type(wait_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: wait_ty,
                    value: mir::ConstantKind::Function(wait_id, GenericArguments::empty(), wait_ty),
                }),
                args: vec![source_id_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn is_hidden_spawn_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self.gcx.symbol_eq(
            self.gcx.definition_ident(id).symbol,
            "__intrinsic_spawn_async",
        )
    }

    fn is_hidden_is_task_cancelled_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_is_task_cancelled")
    }

    fn lower_is_task_cancelled_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [] = args else {
            panic!("ICE: task is_cancelled lowering expects no arguments");
        };
        let destination_ty = self.place_ty(&destination);
        assert_eq!(
            destination_ty, self.gcx.types.bool,
            "ICE: task is_cancelled intrinsic must lower into a bool destination"
        );
        let func_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::IsTaskCancelled,
            span,
        );
        let func_ty = self.gcx.get_type(func_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: func_ty,
                    value: mir::ConstantKind::Function(func_id, GenericArguments::empty(), func_ty),
                }),
                args: vec![],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn is_hidden_sleep_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self
            .gcx
            .symbol_eq(self.gcx.definition_ident(id).symbol, "__intrinsic_sleep")
    }

    fn is_hidden_wait_readable_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self.gcx.symbol_eq(
            self.gcx.definition_ident(id).symbol,
            "__intrinsic_wait_readable",
        )
    }

    fn is_hidden_wait_writable_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self.gcx.symbol_eq(
            self.gcx.definition_ident(id).symbol,
            "__intrinsic_wait_writable",
        )
    }

    fn is_hidden_intrinsic_named(&self, callee: ExprId, name: &str) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };
        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self
            .gcx
            .symbol_eq(self.gcx.definition_ident(id).symbol, name)
    }

    fn is_hidden_cancel_task_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_cancel_task")
    }

    fn is_hidden_task_result_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_result")
    }

    fn is_hidden_task_group_create_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_create")
    }

    fn is_hidden_task_group_spawn_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_spawn")
    }

    fn is_hidden_task_group_next_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_next")
    }

    fn is_hidden_task_group_close_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_close")
    }

    fn is_hidden_task_group_cancel_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_cancel")
    }

    fn is_hidden_task_group_destroy_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_destroy")
    }

    fn is_hidden_task_group_destroy_and_rethrow_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_destroy_and_rethrow")
    }

    fn is_hidden_panic_payload_message_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_panic_payload_message")
    }

    fn is_hidden_panic_payload_rethrow_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_panic_payload_rethrow")
    }

    fn lower_panic_payload_message_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [data_arg] = args else {
            panic!("ICE: panic_payload_message expects exactly one argument");
        };
        let data_operand = unpack!(block = self.as_local_operand(block, *data_arg));
        let msg_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::PanicPayloadMessage,
            span,
        );
        let msg_ty = self.gcx.get_type(msg_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: msg_ty,
                    value: mir::ConstantKind::Function(
                        msg_id,
                        GenericArguments::empty(),
                        msg_ty,
                    ),
                }),
                args: vec![data_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn lower_panic_payload_rethrow_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [data_arg] = args else {
            panic!("ICE: panic_payload_rethrow expects exactly one argument");
        };
        let data_operand = unpack!(block = self.as_local_operand(block, *data_arg));
        let rethrow_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::PanicPayloadRethrow,
            span,
        );
        let rethrow_ty = self.gcx.get_type(rethrow_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: rethrow_ty,
                    value: mir::ConstantKind::Function(
                        rethrow_id,
                        GenericArguments::empty(),
                        rethrow_ty,
                    ),
                }),
                args: vec![data_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn async_callable_operand(
        &mut self,
        block: BasicBlockId,
        callee: ExprId,
        callee_ty: crate::sema::models::Ty<'ctx>,
    ) -> BlockAnd<Operand<'ctx>> {
        let callee_expr = &self.thir.exprs[callee];
        match &callee_expr.kind {
            ExprKind::Zst { id, generic_args } if self.gcx.definition_is_async(*id) => {
                let async_callee_ty = match callee_ty.kind() {
                    crate::sema::models::TyKind::FnPointer { inputs, .. } => self
                        .gcx
                        .store
                        .interners
                        .intern_ty(crate::sema::models::TyKind::FnPointer {
                            inputs,
                            output: self.gcx.async_handle_ty(),
                        }),
                    _ => self.gcx.async_handle_ty(),
                };
                block.and(Operand::Constant(Constant {
                    ty: async_callee_ty,
                    value: mir::ConstantKind::Function(
                        *id,
                        generic_args.unwrap_or(GenericArguments::empty()),
                        async_callee_ty,
                    ),
                }))
            }
            _ => self.as_local_operand(block, callee),
        }
    }

    fn goto_if_fallthrough(
        &mut self,
        source: BasicBlockId,
        destination: BasicBlockId,
        span: Span,
    ) -> bool {
        if self.body.basic_blocks[source].terminator.is_none() {
            self.goto(source, destination, span);
            true
        } else {
            false
        }
    }

    fn lower_match_expr(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        expr_id: ExprId,
        scrutinee: ExprId,
        arms: &[thir::ArmId],
    ) -> BlockAnd<()> {
        let expr = &self.thir.exprs[expr_id];
        let scrutinee_place = unpack!(block = self.as_place(block, scrutinee));

        let mut owned_tree = None;
        let tree = match self.thir.match_trees.get(&expr_id) {
            Some(tree) => tree,
            None => {
                let report = thir::match_tree::compile_match(self.gcx, self.thir, scrutinee, arms);
                owned_tree = Some(report.tree);
                owned_tree.as_ref().expect("match tree")
            }
        };
        // Keep owned_tree alive for the duration of this function
        let _keep_alive = &owned_tree;

        let mut var_places: FxHashMap<usize, Place<'ctx>> = FxHashMap::default();
        var_places.insert(tree.root_var.id, scrutinee_place.clone());
        self.apply_deref_vars(&mut var_places, &tree.deref_vars);

        let join_block = self.new_block_with_note("match-join".into());
        let mut join_has_incoming = false;
        self.lower_match_decision(
            block,
            &tree.decision,
            &destination,
            join_block,
            &mut join_has_incoming,
            &var_places,
            expr.span,
            &tree.deref_vars,
        );
        if !join_has_incoming {
            self.terminate(join_block, expr.span, TerminatorKind::Unreachable);
        }
        join_block.unit()
    }

    fn apply_deref_vars(
        &self,
        var_places: &mut FxHashMap<usize, Place<'ctx>>,
        deref_vars: &[thir::match_tree::DerefVar],
    ) {
        for deref_var in deref_vars {
            if var_places.contains_key(&deref_var.deref) {
                continue;
            }
            let Some(base_place) = var_places.get(&deref_var.base) else {
                continue;
            };
            let mut proj = base_place.projection.clone();
            proj.push(PlaceElem::Deref);
            var_places.insert(
                deref_var.deref,
                Place {
                    local: base_place.local,
                    projection: proj,
                },
            );
        }
    }

    fn lower_match_decision(
        &mut self,
        mut block: BasicBlockId,
        decision: &thir::match_tree::Decision<'ctx>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        join_has_incoming: &mut bool,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
        deref_vars: &[thir::match_tree::DerefVar],
    ) {
        match decision {
            thir::match_tree::Decision::Success(body) => {
                let arm = &self.thir.arms[body.arm];
                let arm_block = self.new_block_with_note(format!("match-arm-{}", body.arm.index()));
                if !self.goto_if_fallthrough(block, arm_block, span) {
                    return;
                }
                let arm_block = self
                    .bind_match_bindings(arm_block, body.arm, &body.bindings, var_places)
                    .into_block();
                let arm_block = self
                    .expr_into_dest(destination.clone(), arm_block, arm.body)
                    .into_block();
                if self.goto_if_fallthrough(arm_block, join_block, arm.span) {
                    *join_has_incoming = true;
                }
            }
            thir::match_tree::Decision::Failure => {
                self.terminate(block, span, TerminatorKind::Unreachable);
            }
            thir::match_tree::Decision::Guard(guard_expr, body, fallback) => {
                let arm = &self.thir.arms[body.arm];
                let guard_block =
                    self.new_block_with_note(format!("match-guard-{}", body.arm.index()));
                if !self.goto_if_fallthrough(block, guard_block, span) {
                    return;
                }
                block = self
                    .bind_match_bindings(guard_block, body.arm, &body.bindings, var_places)
                    .into_block();
                let guard_operand = unpack!(block = self.as_operand(block, *guard_expr));
                let then_block =
                    self.new_block_with_note(format!("match-arm-{}", body.arm.index()));
                let else_block = self.new_block_with_note("match-guard-fallback".into());
                self.terminate(
                    block,
                    arm.span,
                    TerminatorKind::if_(guard_operand, then_block, else_block),
                );
                let then_block = self
                    .expr_into_dest(destination.clone(), then_block, arm.body)
                    .into_block();
                if self.goto_if_fallthrough(then_block, join_block, arm.span) {
                    *join_has_incoming = true;
                }
                self.lower_match_decision(
                    else_block,
                    fallback,
                    destination,
                    join_block,
                    join_has_incoming,
                    var_places,
                    span,
                    deref_vars,
                );
            }
            thir::match_tree::Decision::Switch(branch_var, cases, fallback) => {
                let Some(branch_place) = var_places.get(&branch_var.id) else {
                    self.terminate(block, span, TerminatorKind::Unreachable);
                    return;
                };

                let Some(first_case) = cases.first() else {
                    if let Some(fallback) = fallback {
                        self.lower_match_decision(
                            block,
                            fallback,
                            destination,
                            join_block,
                            join_has_incoming,
                            var_places,
                            span,
                            deref_vars,
                        );
                    } else {
                        self.terminate(block, span, TerminatorKind::Unreachable);
                    }
                    return;
                };

                match &first_case.constructor {
                    thir::match_tree::Constructor::Tuple(_) => {
                        if cases.len() != 1 {
                            self.terminate(block, span, TerminatorKind::Unreachable);
                            return;
                        }
                        let case = &cases[0];
                        let mut case_places = var_places.clone();
                        self.add_tuple_case_places(&mut case_places, branch_place, &case.arguments);
                        self.apply_deref_vars(&mut case_places, deref_vars);
                        self.lower_match_decision(
                            block,
                            &case.body,
                            destination,
                            join_block,
                            join_has_incoming,
                            &case_places,
                            span,
                            deref_vars,
                        );
                    }
                    thir::match_tree::Constructor::Literal(
                        thir::match_tree::LiteralKey::Float(_),
                    )
                    | thir::match_tree::Constructor::Literal(
                        thir::match_tree::LiteralKey::String(_),
                    ) => {
                        self.lower_match_literal_chain(
                            block,
                            branch_place,
                            branch_var.ty,
                            cases,
                            fallback.as_deref(),
                            destination,
                            join_block,
                            join_has_incoming,
                            var_places,
                            span,
                            deref_vars,
                        );
                    }
                    _ => {
                        let discr = match &first_case.constructor {
                            thir::match_tree::Constructor::Variant { .. } => {
                                unpack!(
                                    block =
                                        self.enum_discriminant_operand(block, branch_place, span)
                                )
                            }
                            _ => Operand::Copy(branch_place.clone()),
                        };

                        let mut targets = Vec::with_capacity(cases.len());
                        for case in cases {
                            let case_block = self.new_block_with_note("match-case".into());
                            let mut case_places = var_places.clone();

                            let value = match &case.constructor {
                                thir::match_tree::Constructor::Bool(b) => {
                                    if *b {
                                        1u128
                                    } else {
                                        0u128
                                    }
                                }
                                thir::match_tree::Constructor::Variant { name, index } => {
                                    let variant_index = thir::VariantIndex::from_usize(*index);
                                    self.add_variant_case_places(
                                        &mut case_places,
                                        branch_place,
                                        *name,
                                        variant_index,
                                        &case.arguments,
                                    );
                                    self.apply_deref_vars(&mut case_places, deref_vars);
                                    *index as u128
                                }
                                thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::Integer(i),
                                ) => *i as u128,
                                thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::Rune(r),
                                ) => *r as u32 as u128,
                                thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::Float(_),
                                )
                                | thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::String(_),
                                )
                                | thir::match_tree::Constructor::Tuple(_) => {
                                    self.terminate(block, span, TerminatorKind::Unreachable);
                                    return;
                                }
                            };

                            self.lower_match_decision(
                                case_block,
                                &case.body,
                                destination,
                                join_block,
                                join_has_incoming,
                                &case_places,
                                span,
                                deref_vars,
                            );
                            targets.push((value, case_block));
                        }

                        let otherwise_block = if let Some(fallback) = fallback.as_deref() {
                            let fallback_block = self.new_block_with_note("match-fallback".into());
                            self.lower_match_decision(
                                fallback_block,
                                fallback,
                                destination,
                                join_block,
                                join_has_incoming,
                                var_places,
                                span,
                                deref_vars,
                            );
                            fallback_block
                        } else {
                            let unreachable = self.new_block_with_note("match-unreachable".into());
                            self.terminate(unreachable, span, TerminatorKind::Unreachable);
                            unreachable
                        };

                        self.terminate(
                            block,
                            span,
                            TerminatorKind::SwitchInt {
                                discr,
                                targets,
                                otherwise: otherwise_block,
                            },
                        );
                    }
                }
            }
        }
    }

    fn lower_match_literal_chain(
        &mut self,
        mut block: BasicBlockId,
        branch_place: &Place<'ctx>,
        branch_ty: crate::sema::models::Ty<'ctx>,
        cases: &[thir::match_tree::Case<'ctx>],
        fallback: Option<&thir::match_tree::Decision<'ctx>>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        join_has_incoming: &mut bool,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
        deref_vars: &[thir::match_tree::DerefVar],
    ) {
        if cases.is_empty() {
            if let Some(fallback) = fallback {
                self.lower_match_decision(
                    block,
                    fallback,
                    destination,
                    join_block,
                    join_has_incoming,
                    var_places,
                    span,
                    deref_vars,
                );
            } else {
                self.terminate(block, span, TerminatorKind::Unreachable);
            }
            return;
        }

        let fallback_block = fallback.map(|decision| {
            let fb = self.new_block_with_note("match-fallback".into());
            self.lower_match_decision(
                fb,
                decision,
                destination,
                join_block,
                join_has_incoming,
                var_places,
                span,
                deref_vars,
            );
            fb
        });

        for (idx, case) in cases.iter().enumerate() {
            let is_last = idx + 1 == cases.len();
            let next_block = if is_last {
                fallback_block.unwrap_or_else(|| {
                    let bb = self.new_block_with_note("match-unreachable".into());
                    self.terminate(bb, span, TerminatorKind::Unreachable);
                    bb
                })
            } else {
                self.new_block_with_note("match-next".into())
            };

            let case_block = self.new_block_with_note("match-case".into());
            let cond = unpack!(
                block = self.build_literal_eq_operand(
                    block,
                    branch_place,
                    branch_ty,
                    &case.constructor,
                    span
                )
            );

            self.terminate(
                block,
                span,
                TerminatorKind::if_(cond, case_block, next_block),
            );

            self.lower_match_decision(
                case_block,
                &case.body,
                destination,
                join_block,
                join_has_incoming,
                var_places,
                span,
                deref_vars,
            );

            block = next_block;
        }
    }

    fn build_literal_eq_operand(
        &mut self,
        mut block: BasicBlockId,
        branch_place: &Place<'ctx>,
        branch_ty: crate::sema::models::Ty<'ctx>,
        constructor: &thir::match_tree::Constructor,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        let literal = match constructor {
            thir::match_tree::Constructor::Literal(key) => key,
            _ => {
                return block.and(Operand::Constant(Constant {
                    ty: self.gcx.types.bool,
                    value: mir::ConstantKind::Bool(false),
                }));
            }
        };

        if let thir::match_tree::LiteralKey::String(s) = literal {
            let string_eq_id = self.find_function_in_std("string", "stringEq", span);
            let string_eq_ty = self.gcx.get_type(string_eq_id);
            let bool_ty = match string_eq_ty.kind() {
                crate::sema::models::TyKind::FnPointer { output, .. } => output,
                _ => panic!("stringEq must be a function"),
            };
            let string_eq_func = Operand::Constant(Constant {
                ty: string_eq_ty,
                value: mir::ConstantKind::Function(string_eq_id, List::empty(), string_eq_ty),
            });
            let rhs = Operand::Constant(Constant {
                ty: branch_ty,
                value: mir::ConstantKind::String(*s),
            });
            let temp = self.new_temp_with_ty(bool_ty, span);
            let destination = Place::from_local(temp);
            let next_block = self.new_block();
            let unwind = self.call_unwind_for_callee(&string_eq_func, span);
            self.terminate(
                block,
                span,
                TerminatorKind::Call {
                    func: string_eq_func,
                    args: vec![Operand::Copy(branch_place.clone()), rhs],
                    destination: destination.clone(),
                    target: next_block,
                    unwind,
                },
            );
            block = next_block;
            return block.and(Operand::Copy(destination));
        }

        let value = match literal {
            thir::match_tree::LiteralKey::Integer(i) => mir::ConstantKind::Integer(*i),
            thir::match_tree::LiteralKey::Float(bits) => {
                mir::ConstantKind::Float(f64::from_bits(*bits))
            }
            thir::match_tree::LiteralKey::Rune(r) => mir::ConstantKind::Rune(*r),
            thir::match_tree::LiteralKey::String(_) => unreachable!(),
        };

        let constant = Constant {
            ty: branch_ty,
            value,
        };
        let temp = self.new_temp_with_ty(self.gcx.types.bool, span);
        let rvalue = Rvalue::BinaryOp {
            op: BinaryOperator::Eql,
            lhs: Operand::Copy(branch_place.clone()),
            rhs: Operand::Constant(constant),
        };
        self.push_assign(block, Place::from_local(temp), rvalue, span);
        block.and(Operand::Copy(Place::from_local(temp)))
    }

    /// Allocates a GC-tracked buffer and fills it with the given element expressions.
    /// Returns (block, buf_ptr_u8_place, buf_ptr_t_local, len_const).
    fn fill_element_buffer(
        &mut self,
        mut block: BasicBlockId,
        args: &[ExprId],
        elem_ty: crate::sema::models::Ty<'ctx>,
        span: Span,
    ) -> (BasicBlockId, Place<'ctx>, LocalId, Operand<'ctx>) {
        let count = args.len();
        let usize_ty = self.gcx.types.uint;

        let makebuf_id = self.find_function_in_std("mem", "__gc__makebuf", span);
        let desc_fn_id = self.find_function_in_std("intrinsic", "__intrinsic_gc_desc", span);
        let ptr_add_id = self.find_function_in_std("intrinsic", "__intrinsic_ptr_add", span);

        // 1. Call __intrinsic_gc_desc[T]().
        let generics = vec![crate::sema::models::GenericArgument::Type(elem_ty)];
        let generics = self.gcx.store.interners.intern_generic_args(generics);
        let desc_fn_ty = self.gcx.get_type(desc_fn_id);
        let desc_output = match desc_fn_ty.kind() {
            crate::sema::models::TyKind::FnPointer { output, .. } => output,
            _ => panic!("__intrinsic_gc_desc must be a function"),
        };
        let desc_func_op = Operand::Constant(Constant {
            ty: desc_fn_ty,
            value: mir::ConstantKind::Function(desc_fn_id, generics, desc_fn_ty),
        });

        let next_block = self.new_block();
        let desc_dest = Place::from_local(self.new_temp_with_ty(desc_output, span));

        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: desc_func_op,
                args: vec![],
                destination: desc_dest.clone(),
                target: next_block,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        block = next_block;

        // 2. Call __gc__makebuf(desc, count, count)
        let makebuf_fn_ty = self.gcx.get_type(makebuf_id);
        let makebuf_output = match makebuf_fn_ty.kind() {
            crate::sema::models::TyKind::FnPointer { output, .. } => output,
            _ => panic!("__gc__makebuf must be a function"),
        };

        let len_const = Operand::Constant(Constant {
            ty: usize_ty,
            value: mir::ConstantKind::Integer(count as u64),
        });

        let makebuf_generic_args = self.gcx.store.interners.intern_generic_args(vec![]);
        let makebuf_func = Operand::Constant(Constant {
            ty: makebuf_fn_ty,
            value: mir::ConstantKind::Function(makebuf_id, makebuf_generic_args, makebuf_fn_ty),
        });

        let buf_ptr_dest = Place::from_local(self.new_temp_with_ty(makebuf_output, span));
        let next_block_2 = self.new_block();
        let makebuf_unwind = self.call_unwind_action(span);

        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: makebuf_func,
                args: vec![
                    Operand::Copy(desc_dest),
                    len_const.clone(),
                    len_const.clone(),
                ],
                destination: buf_ptr_dest.clone(),
                target: next_block_2,
                unwind: makebuf_unwind,
            },
        );
        block = next_block_2;

        // 3. Cast *mut u8 to *mut T.
        let ptr_t_ty = crate::sema::models::Ty::new(
            crate::sema::models::TyKind::Pointer(elem_ty, crate::hir::Mutability::Mutable),
            self.gcx,
        );
        let buf_ptr_t = self.new_temp_with_ty(ptr_t_ty, span);

        self.push_assign(
            block,
            Place::from_local(buf_ptr_t),
            Rvalue::Cast {
                kind: CastKind::Pointer,
                operand: Operand::Copy(buf_ptr_dest.clone()),
                ty: ptr_t_ty,
            },
            span,
        );

        // 4. Fill buffer.
        let ptr_add_generics = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(elem_ty)]);

        let ptr_add_ty = self.gcx.get_type(ptr_add_id);
        let ptr_add_output = match ptr_add_ty.kind() {
            crate::sema::models::TyKind::FnPointer { output, .. } => {
                crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                    self.gcx,
                    output,
                    ptr_add_generics,
                )
            }
            _ => panic!("__intrinsic_ptr_add must be a function"),
        };

        let ptr_add_func = Operand::Constant(Constant {
            ty: ptr_add_ty,
            value: mir::ConstantKind::Function(ptr_add_id, ptr_add_generics, ptr_add_ty),
        });

        for (i, arg_expr_id) in args.iter().enumerate() {
            let arg_operand = unpack!(block = self.as_operand(block, *arg_expr_id));

            let offset_ptr_place = if i == 0 {
                Place::from_local(buf_ptr_t)
            } else {
                let next_block_loop = self.new_block();
                let temp_ptr = self.new_temp_with_ty(ptr_add_output, span);
                let idx_op = Operand::Constant(Constant {
                    ty: usize_ty,
                    value: mir::ConstantKind::Integer(i as u64),
                });

                self.terminate(
                    block,
                    span,
                    TerminatorKind::Call {
                        func: ptr_add_func.clone(),
                        args: vec![Operand::Copy(Place::from_local(buf_ptr_t)), idx_op],
                        destination: Place::from_local(temp_ptr),
                        target: next_block_loop,
                        unwind: mir::CallUnwindAction::Terminate,
                    },
                );
                block = next_block_loop;

                let temp_mut_ptr = self.new_temp_with_ty(ptr_t_ty, span);
                self.push_assign(
                    block,
                    Place::from_local(temp_mut_ptr),
                    Rvalue::Cast {
                        kind: CastKind::Pointer,
                        operand: Operand::Copy(Place::from_local(temp_ptr)),
                        ty: ptr_t_ty,
                    },
                    span,
                );

                Place::from_local(temp_mut_ptr)
            };

            let dest = Place {
                local: offset_ptr_place.local,
                projection: vec![PlaceElem::Deref],
            };
            self.push_assign(block, dest, Rvalue::Use(arg_operand), span);
        }

        (block, buf_ptr_dest, buf_ptr_t, len_const)
    }

    fn lower_variadic_sequence(
        &mut self,
        mut block: BasicBlockId,
        args: &[ExprId],
        span_ty: crate::sema::models::Ty<'ctx>,
        elem_ty: crate::sema::models::Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        let (new_block, _buf_ptr_dest, buf_ptr_t, len_const) =
            self.fill_element_buffer(block, args, elem_ty, span);
        block = new_block;

        // Cast *mut T to *const T for Span's ptr field.
        let ptr_const_t_ty = crate::sema::models::Ty::new(
            crate::sema::models::TyKind::Pointer(elem_ty, crate::hir::Mutability::Immutable),
            self.gcx,
        );
        let buf_ptr_const_t = self.new_temp_with_ty(ptr_const_t_ty, span);
        self.push_assign(
            block,
            Place::from_local(buf_ptr_const_t),
            Rvalue::Cast {
                kind: CastKind::Pointer,
                operand: Operand::Copy(Place::from_local(buf_ptr_t)),
                ty: ptr_const_t_ty,
            },
            span,
        );

        // Aggregate Span { ptr, len }.
        let fields = IndexVec::from_vec(vec![
            Operand::Copy(Place::from_local(buf_ptr_const_t)),
            len_const.clone(),
        ]);

        let (span_def_id, generic_args) =
            if let crate::sema::models::TyKind::Adt(def, args) = span_ty.kind() {
                (def.id, args)
            } else {
                unreachable!()
            };

        let span_temp = self.new_temp_with_ty(span_ty, span);

        self.push_assign(
            block,
            Place::from_local(span_temp),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: span_def_id,
                    variant_index: None,
                    generic_args,
                },
                fields,
            },
            span,
        );

        block.and(Operand::Copy(Place::from_local(span_temp)))
    }

    fn lower_list_literal(
        &mut self,
        mut block: BasicBlockId,
        destination: Place<'ctx>,
        args: &[ExprId],
        _list_ty: crate::sema::models::Ty<'ctx>,
        elem_ty: crate::sema::models::Ty<'ctx>,
        span: Span,
    ) -> BasicBlockId {
        let (new_block, buf_ptr_dest, _buf_ptr_t, len_const) =
            self.fill_element_buffer(block, args, elem_ty, span);
        block = new_block;

        // Call __list_from_raw_parts[Element](buffer, len, cap).
        let list_fn_id = self.find_function_in_std("collections", "__list_from_raw_parts", span);
        let list_fn_generics = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(elem_ty)]);
        let list_fn_ty = self.gcx.get_type(list_fn_id);
        let list_func = Operand::Constant(Constant {
            ty: list_fn_ty,
            value: mir::ConstantKind::Function(list_fn_id, list_fn_generics, list_fn_ty),
        });

        let unwind = self.call_unwind_action(span);
        let next_block = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: list_func,
                args: vec![
                    Operand::Copy(buf_ptr_dest),
                    len_const.clone(),
                    len_const.clone(),
                ],
                destination,
                target: next_block,
                unwind,
            },
        );

        next_block
    }

    fn find_function_in_std(
        &self,
        module: &str,
        name: &str,
        _span: Span,
    ) -> crate::hir::DefinitionID {
        let std_pkg = self.gcx.std_package_index().expect("std package found");
        let output = self.gcx.resolution_output(std_pkg);

        let in_module = |id: crate::hir::DefinitionID| {
            let mut current = id;
            while let Some(parent) = output.definition_to_parent.get(&current).cloned() {
                if parent == current {
                    break;
                }
                current = parent;
                if matches!(
                    output.definition_to_kind.get(&current),
                    Some(DefinitionKind::Module)
                ) {
                    if let Some(ident) = output.definition_to_ident.get(&current) {
                        if self.gcx.symbol_eq(ident.symbol, module) {
                            return true;
                        }
                    }
                }
            }
            false
        };

        // Linear scan for now (slow but works)
        let mut fallback = None;
        for (id, ident) in output.definition_to_ident.iter() {
            if self.gcx.symbol_eq(ident.symbol, name) {
                if !matches!(
                    output.definition_to_kind.get(id),
                    Some(DefinitionKind::Function)
                ) {
                    continue;
                }
                let has_sig = self
                    .gcx
                    .with_type_database(id.package(), |db| db.def_to_fn_sig.contains_key(id));
                if !has_sig {
                    continue;
                }
                if in_module(*id) {
                    return *id;
                }
                fallback = Some(*id);
            }
        }
        if let Some(id) = fallback {
            return id;
        }
        panic!(
            "Standard library function {} not found in std.{}",
            name, module
        );
    }

    fn call_unwind_for_callee(
        &mut self,
        callee: &Operand<'ctx>,
        span: Span,
    ) -> mir::CallUnwindAction {
        if self.is_nounwind_callee(callee) {
            mir::CallUnwindAction::Terminate
        } else {
            self.call_unwind_action(span)
        }
    }

    fn is_nounwind_callee(&self, callee: &Operand<'ctx>) -> bool {
        let Operand::Constant(c) = callee else {
            return false;
        };
        let mir::ConstantKind::Function(def_id, _, _) = c.value else {
            return false;
        };
        matches!(
            self.gcx.get_signature(def_id).abi,
            Some(crate::hir::Abi::Intrinsic)
        )
    }

    fn enum_discriminant_operand(
        &mut self,
        block: BasicBlockId,
        place: &Place<'ctx>,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        let temp = self.new_temp_with_ty(self.gcx.types.uint, span);
        self.push_assign(
            block,
            Place::from_local(temp),
            Rvalue::Discriminant {
                place: place.clone(),
            },
            span,
        );
        block.and(Operand::Copy(Place::from_local(temp)))
    }

    fn add_tuple_case_places(
        &self,
        places: &mut FxHashMap<usize, Place<'ctx>>,
        base_place: &Place<'ctx>,
        args: &[thir::match_tree::Variable<'ctx>],
    ) {
        for (idx, var) in args.iter().enumerate() {
            let mut proj = base_place.projection.clone();
            proj.push(PlaceElem::Field(FieldIndex::from_usize(idx), var.ty));
            places.insert(
                var.id,
                Place {
                    local: base_place.local,
                    projection: proj,
                },
            );
        }
    }

    fn add_variant_case_places(
        &self,
        places: &mut FxHashMap<usize, Place<'ctx>>,
        base_place: &Place<'ctx>,
        name: crate::span::Symbol,
        index: thir::VariantIndex,
        args: &[thir::match_tree::Variable<'ctx>],
    ) {
        for (idx, var) in args.iter().enumerate() {
            let mut proj = base_place.projection.clone();
            proj.push(PlaceElem::VariantDowncast { name: name, index });
            proj.push(PlaceElem::Field(FieldIndex::from_usize(idx), var.ty));
            places.insert(
                var.id,
                Place {
                    local: base_place.local,
                    projection: proj,
                },
            );
        }
    }

    /// Binds match pattern variables using the precomputed var_places mapping.
    /// This correctly handles or-patterns by using the exact places computed
    /// during match tree traversal.
    ///
    /// For or-patterns, multiple alternatives may bind the same name. We ensure
    /// all alternatives share the same MIR local by tracking (arm_id, name) -> local.
    fn bind_match_bindings(
        &mut self,
        block: BasicBlockId,
        arm_id: thir::ArmId,
        bindings: &[thir::match_tree::Binding<'ctx>],
        var_places: &FxHashMap<usize, Place<'ctx>>,
    ) -> BlockAnd<()> {
        for binding in bindings {
            // Look up the place for this binding's variable
            let Some(src_place) = var_places.get(&binding.variable.id) else {
                // Variable not found in var_places - this shouldn't happen
                // but we'll skip it rather than crash
                continue;
            };

            // Get or create the MIR local for this binding.
            // For or-patterns, all alternatives with the same binding name share
            // the same local so the body can reference it consistently.
            let key = (arm_id, binding.name);
            let local = if let Some(&existing) = self.arm_binding_locals.get(&key) {
                existing
            } else {
                let new_local = self.push_local(
                    binding.ty,
                    mir::LocalKind::User,
                    true, // Match bindings are mutable for now to allow pattern binding operations
                    Some(binding.name),
                    binding.span,
                );
                self.arm_binding_locals.insert(key, new_local);
                new_local
            };

            // Map the pattern's NodeID to the MIR local.
            // This ensures the body can find the local regardless of which
            // alternative's NodeID it references.
            self.locals.insert(binding.local, local);

            let is_deref_place = src_place
                .projection
                .iter()
                .any(|p| matches!(p, PlaceElem::Deref));
            if matches!(binding.mode, crate::hir::BindingMode::ByValue) && is_deref_place {
                self.place_bindings.insert(binding.local, src_place.clone());
                continue;
            }

            // Generate the appropriate rvalue based on binding mode
            let rvalue = match binding.mode {
                crate::hir::BindingMode::ByValue => {
                    let operand = if self.is_type_copyable(binding.ty) {
                        Operand::Copy(src_place.clone())
                    } else {
                        Operand::Move(src_place.clone())
                    };
                    Rvalue::Use(operand)
                }
                crate::hir::BindingMode::ByRef(mutability) => {
                    // Take a reference to the place
                    Rvalue::Ref {
                        mutable: mutability == crate::hir::Mutability::Mutable,
                        place: src_place.clone(),
                    }
                }
            };

            self.push_assign(block, Place::from_local(local), rvalue, binding.span);
        }
        block.unit()
    }
}

fn task_token_place<'ctx>(gcx: Gcx<'ctx>, task_place: Place<'ctx>) -> Place<'ctx> {
    let mut projection = task_place.projection;
    projection.push(PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.uint));
    Place {
        local: task_place.local,
        projection,
    }
}

fn intrinsic_type_arg<'ctx, 'thir>(
    thir: &'thir thir::ThirFunction<'ctx>,
    callee: ExprId,
    index: usize,
) -> crate::sema::models::Ty<'ctx> {
    let ExprKind::Zst { generic_args, .. } = thir.exprs[callee].kind else {
        panic!("ICE: intrinsic type arg requested from non-ZST callee");
    };
    generic_args
        .unwrap_or(GenericArguments::empty())
        .get(index)
        .copied()
        .and_then(GenericArgument::ty)
        .unwrap_or_else(|| panic!("ICE: intrinsic missing type argument {index}"))
}

fn duration_secs_place<'ctx>(gcx: Gcx<'ctx>, duration_place: Place<'ctx>) -> Place<'ctx> {
    let mut projection = duration_place.projection;
    projection.push(PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.uint64));
    Place {
        local: duration_place.local,
        projection,
    }
}

fn duration_nanos_place<'ctx>(gcx: Gcx<'ctx>, duration_place: Place<'ctx>) -> Place<'ctx> {
    let mut projection = duration_place.projection;
    projection.push(PlaceElem::Field(FieldIndex::from_raw(1), gcx.types.uint32));
    Place {
        local: duration_place.local,
        projection,
    }
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    fn then_else_break(&mut self, mut block: BasicBlockId, condition: ExprId) -> BlockAnd<()> {
        let place = unpack!(block = self.as_temp(block, condition));
        let operand = if self.is_type_copyable(self.thir.exprs[condition].ty) {
            Operand::Copy(Place::from_local(place))
        } else {
            Operand::Move(Place::from_local(place))
        };

        let then_block = self.new_block_with_note("then block".into());
        let else_block = self.new_block_with_note("else block".into());

        let expr = &self.thir.exprs[condition];
        self.terminate(
            block,
            expr.span,
            TerminatorKind::if_(operand, then_block, else_block),
        );
        self.break_for_else(else_block, expr.span);
        then_block.unit()
    }

    pub fn push_assign_unit(
        &mut self,
        block: BasicBlockId,
        span: Span,
        place: Place<'ctx>,
        gcx: Gcx<'ctx>,
    ) {
        self.push_assign(
            block,
            place,
            Rvalue::Use(Operand::Constant(Constant {
                ty: gcx.types.void,
                value: mir::ConstantKind::Unit,
            })),
            span,
        );
    }
}
