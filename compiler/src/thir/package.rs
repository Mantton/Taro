use crate::{
    compile::{context::GlobalContext, entry::validate_entry_point},
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, Mutability, Resolution},
    mir::{self, LogicalOperator},
    sema::{
        models::{AdtKind, ConstKind, ConstValue, Ty, TyKind},
        resolve::models::VariantCtorKind,
        tycheck::{
            results::TypeCheckResults, solve::Adjustment,
            utils::instantiate::instantiate_signature_with_args,
        },
    },
    thir::{
        self, Block, BlockId, ClosureCapture, Constant, ConstantKind, Expr, ExprId, ExprKind,
        FieldIndex, Param, Stmt, StmtId, StmtKind, ThirFunction, ThirPackage, VariantIndex,
        pattern::pattern_from_hir,
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: TypeCheckResults<'ctx>,
) -> CompileResult<ThirPackage<'ctx>> {
    let entry = validate_entry_point(&package, gcx)?;
    let mut package = Actor::run(package, gcx, results, entry)?;
    thir::passes::exhaustiveness::run(&mut package, gcx)?;
    Ok(package)
}

struct Actor<'ctx> {
    gcx: GlobalContext<'ctx>,
    results: std::rc::Rc<TypeCheckResults<'ctx>>,
    functions: FxHashMap<DefinitionID, ThirFunction<'ctx>>,
    entry: Option<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn new(
        gcx: GlobalContext<'ctx>,
        results: TypeCheckResults<'ctx>,
        entry: Option<DefinitionID>,
    ) -> Self {
        Actor {
            gcx,
            results: std::rc::Rc::new(results),
            functions: FxHashMap::default(),
            entry,
        }
    }

    fn run(
        package: &hir::Package,
        gcx: GlobalContext<'ctx>,
        results: TypeCheckResults<'ctx>,
        entry: Option<DefinitionID>,
    ) -> CompileResult<ThirPackage<'ctx>> {
        let mut actor = Actor::new(gcx, results, entry);
        hir::walk_package(&mut actor, package);

        // Synthesize THIR for any registered synthetic methods (e.g., derived Clone)
        let synthetic_functions = crate::thir::synthesize::synthesize_all(gcx);
        for func in synthetic_functions {
            actor.functions.insert(func.id, func);
        }

        // Synthesize default value providers
        let default_exprs = gcx.store.default_value_exprs.borrow();
        for (id, expr) in default_exprs.iter() {
            if id.package() != gcx.package_index() {
                continue;
            }
            let func = FunctionLower::lower_default_provider(gcx, actor.results.clone(), *id, expr);
            actor.functions.insert(*id, func);
        }

        let pkg = ThirPackage {
            functions: actor.functions,
            entry: actor.entry,
        };
        gcx.dcx().ok()?;
        Ok(pkg)
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        let (func, nested_closures) =
            FunctionLower::lower(self.gcx, self.results.clone(), id, node);
        self.functions.insert(id, func);
        // Insert any nested closure bodies
        for closure_func in nested_closures {
            self.functions.insert(closure_func.id, closure_func);
        }
        hir::walk_function(self, id, node, fn_ctx);
    }
}

struct FunctionLower<'ctx> {
    gcx: GlobalContext<'ctx>,
    results: std::rc::Rc<TypeCheckResults<'ctx>>,
    func: ThirFunction<'ctx>,
    /// Nested closure bodies collected during lowering
    nested_closures: Vec<ThirFunction<'ctx>>,
    /// For closure bodies: maps captured variable source_ids to (field_index, capture_kind)
    captures_map:
        Option<FxHashMap<crate::hir::NodeID, (FieldIndex, crate::sema::models::CaptureKind)>>,
}

impl<'ctx> FunctionLower<'ctx> {
    fn lower(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        node: &hir::Function,
    ) -> (ThirFunction<'ctx>, Vec<ThirFunction<'ctx>>) {
        let mut lower = FunctionLower {
            gcx,
            results,
            func: ThirFunction {
                id,
                body: None,
                span: node.signature.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_trees: FxHashMap::default(),
            },
            nested_closures: Vec::new(),
            captures_map: None,
        };

        lower.lower_params(node);
        lower.lower_body(node);
        (lower.func, lower.nested_closures)
    }

    fn lower_default_provider(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        expr: &hir::Expression,
    ) -> ThirFunction<'ctx> {
        let mut lower = FunctionLower {
            gcx,
            results,
            func: ThirFunction {
                id,
                body: None,
                span: expr.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_trees: FxHashMap::default(),
            },
            nested_closures: Vec::new(),
            captures_map: None,
        };

        let expr_id = lower.lower_expr(expr);

        let block_id = BlockId::from_raw(lower.func.blocks.len() as u32);
        lower.func.blocks.push(Block {
            id: block_id,
            stmts: vec![],
            expr: Some(expr_id),
        });

        lower.func.body = Some(block_id);
        // Note: nested_closures from default providers are ignored for now
        lower.func
    }

    fn lower_call_args(
        &mut self,
        arguments: &[hir::ExpressionArgument],
        leading_args: &[ExprId],
    ) -> Vec<ExprId> {
        let mut args = Vec::with_capacity(arguments.len() + leading_args.len());
        args.extend_from_slice(leading_args);
        args.extend(arguments.iter().map(|arg| self.lower_expr(&arg.expression)));
        args
    }

    fn match_arguments_to_parameters(
        &self,
        signature: &crate::sema::models::LabeledFunctionSignature<'ctx>,
        param_offset: usize,
        arguments: &[hir::ExpressionArgument],
    ) -> Option<(Vec<Option<usize>>, Vec<usize>)> {
        if signature.inputs.len() < param_offset {
            return None;
        }

        let params = &signature.inputs[param_offset..];
        let mut param_to_arg: Vec<Option<usize>> = vec![None; params.len()];
        let mut variadic_args: Vec<usize> = Vec::new();
        let mut used_args = vec![false; arguments.len()];

        // First pass: match labeled arguments.
        for (arg_idx, arg) in arguments.iter().enumerate() {
            if let Some(label) = &arg.label {
                let mut found = false;
                for (param_idx, param) in params.iter().enumerate() {
                    if param.label.as_ref() == Some(&label.identifier.symbol) {
                        if param_to_arg[param_idx].is_some() {
                            return None;
                        }
                        param_to_arg[param_idx] = Some(arg_idx);
                        used_args[arg_idx] = true;
                        found = true;
                        break;
                    }
                }
                if !found {
                    return None;
                }
            }
        }

        // Second pass: match positional arguments.
        let mut param_idx = 0;
        for (arg_idx, arg) in arguments.iter().enumerate() {
            if used_args[arg_idx] || arg.label.is_some() {
                continue;
            }

            while param_idx < params.len() && param_to_arg[param_idx].is_some() {
                param_idx += 1;
            }

            if param_idx >= params.len() {
                if signature.is_variadic {
                    variadic_args.push(arg_idx);
                    used_args[arg_idx] = true;
                    continue;
                }
                return None;
            }

            if params[param_idx].label.is_some() {
                return None;
            }

            param_to_arg[param_idx] = Some(arg_idx);
            used_args[arg_idx] = true;
            param_idx += 1;
        }

        Some((param_to_arg, variadic_args))
    }

    fn lower_call_args_with_defaults(
        &mut self,
        signature: &crate::sema::models::LabeledFunctionSignature<'ctx>,
        callee_generic_node: hir::NodeID,
        arguments: &[hir::ExpressionArgument],
        leading_args: &[ExprId],
        span: crate::span::Span,
    ) -> Option<Vec<ExprId>> {
        let generic_args = self.results.instantiation(callee_generic_node);
        let signature = if let Some(args) = generic_args {
            instantiate_signature_with_args(self.gcx, signature, args)
        } else {
            signature.clone()
        };

        let param_offset = leading_args.len();
        let (param_to_arg, variadic_args) =
            self.match_arguments_to_parameters(&signature, param_offset, arguments)?;

        let total_capacity = signature.inputs.len() + variadic_args.len();
        let mut final_args = Vec::with_capacity(total_capacity);
        final_args.extend_from_slice(leading_args);

        for (param_idx, arg_opt) in param_to_arg.iter().enumerate() {
            let param = &signature.inputs[param_offset + param_idx];
            if let Some(arg_idx) = arg_opt {
                final_args.push(self.lower_expr(&arguments[*arg_idx].expression));
            } else if let Some(provider_id) = param.default_provider {
                let inputs = self.gcx.store.interners.intern_ty_list(Vec::new());
                let provider_ty = self.gcx.store.interners.intern_ty(TyKind::FnPointer {
                    inputs,
                    output: param.ty,
                });
                let provider = self.push_expr(
                    ExprKind::Zst {
                        id: provider_id,
                        generic_args,
                    },
                    provider_ty,
                    span,
                );
                let call = self.push_expr(
                    ExprKind::Call {
                        callee: provider,
                        args: vec![],
                    },
                    param.ty,
                    span,
                );
                final_args.push(call);
            } else {
                let is_variadic_param = signature.is_variadic
                    && (param_offset + param_idx + 1 == signature.inputs.len());
                if is_variadic_param {
                    continue;
                }
                return None;
            }
        }

        for arg_idx in variadic_args {
            final_args.push(self.lower_expr(&arguments[arg_idx].expression));
        }

        Some(final_args)
    }

    fn resolve_direct_callee_id(&self, callee: &hir::Expression) -> Option<DefinitionID> {
        let hir::ExpressionKind::Path(path) = &callee.kind else {
            return None;
        };

        let resolution = if let Some(def_id) = self.results.overload_source(callee.id) {
            Resolution::Definition(def_id, self.gcx.definition_kind(def_id))
        } else if let Some(resolution) = self.results.value_resolution(callee.id) {
            resolution
        } else {
            match path {
                hir::ResolvedPath::Resolved(path) => path.resolution.clone(),
                _ => Resolution::Error,
            }
        };

        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::Function | DefinitionKind::AssociatedFunction,
            ) => Some(id),
            _ => None,
        }
    }

    fn lower_params(&mut self, node: &hir::Function) {
        let signature = self.gcx.get_signature(self.func.id);
        self.func.params = node
            .signature
            .prototype
            .inputs
            .iter()
            .zip(signature.inputs.iter())
            .map(|(param, lowered)| Param {
                id: param.id,
                name: param.name.symbol,
                ty: lowered.ty,
                span: param.span,
            })
            .collect();
    }

    fn lower_body(&mut self, node: &hir::Function) {
        if let Some(block) = &node.block {
            let block_id = self.lower_block(block);
            self.func.body = Some(block_id);
        }
    }

    fn lower_block(&mut self, block: &hir::Block) -> BlockId {
        let id = BlockId::from_raw(self.func.blocks.len() as u32);
        self.func.blocks.push(Block {
            id,
            stmts: vec![],
            expr: None,
        });

        let stmts: Vec<_> = block
            .statements
            .iter()
            .filter_map(|stmt| self.lower_statement(stmt).map(|s| self.push_stmt(s)))
            .collect();
        let expr = block.tail.as_deref().map(|expr| self.lower_expr(expr));

        self.func.blocks[id].stmts = stmts;
        self.func.blocks[id].expr = expr;
        id
    }

    fn lower_statement(&mut self, stmt: &hir::Statement) -> Option<Stmt<'ctx>> {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => None,
            hir::StatementKind::Expression(expr) => {
                let expr_id = self.lower_expr(expr);
                Some(Stmt {
                    kind: StmtKind::Expr(expr_id),
                    span: stmt.span,
                })
            }
            hir::StatementKind::Variable(local) => Some(self.lower_local(local)),
            hir::StatementKind::Break => Some(Stmt {
                kind: StmtKind::Break,
                span: stmt.span,
            }),
            hir::StatementKind::Continue => Some(Stmt {
                kind: StmtKind::Continue,
                span: stmt.span,
            }),
            hir::StatementKind::Return(value) => {
                let expr_id = value.as_deref().map(|expr| self.lower_expr(expr));
                Some(Stmt {
                    kind: StmtKind::Return { value: expr_id },
                    span: stmt.span,
                })
            }
            hir::StatementKind::Loop { block, .. } => {
                let block_id = self.lower_block(block);
                Some(Stmt {
                    kind: StmtKind::Loop { block: block_id },
                    span: stmt.span,
                })
            }
            hir::StatementKind::Defer(block) => {
                let block_id = self.lower_block(block);
                Some(Stmt {
                    kind: StmtKind::Defer(block_id),
                    span: stmt.span,
                })
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                let cond = self.lower_expr(condition);
                let else_block_id = self.lower_block(else_block);

                let unit = Constant {
                    ty: self.gcx.types.void,
                    value: ConstantKind::Unit,
                };
                let then_expr =
                    self.push_expr(ExprKind::Literal(unit), self.gcx.types.void, stmt.span);
                let else_expr = self.push_expr(
                    ExprKind::Block(else_block_id),
                    self.gcx.types.void,
                    stmt.span,
                );
                let if_expr = self.push_expr(
                    ExprKind::If {
                        cond,
                        then_expr,
                        else_expr: Some(else_expr),
                    },
                    self.gcx.types.void,
                    stmt.span,
                );

                Some(Stmt {
                    kind: StmtKind::Expr(if_expr),
                    span: stmt.span,
                })
            }
        }
    }

    fn lower_local(&mut self, local: &hir::Local) -> Stmt<'ctx> {
        let ty = self.results.node_type(local.id);
        let expr = local
            .initializer
            .as_deref()
            .map(|expr| self.lower_expr(expr));

        Stmt {
            kind: StmtKind::Let {
                id: local.id,
                pattern: pattern_from_hir(self.gcx, self.results.as_ref(), &local.pattern),
                expr,
                ty,
                mutable: local.mutability == hir::Mutability::Mutable,
            },
            span: local.pattern.span,
        }
    }

    pub fn lower_expr(&mut self, expr: &hir::Expression) -> ExprId {
        self.lower_expr_inner(expr)
    }

    fn lower_expr_inner(&mut self, expr: &hir::Expression) -> ExprId {
        let mut thir_expr = self.lower_expr_unadjusted(expr);
        // Apply adjustments if any
        if let Some(adjustments) = self
            .results
            .node_adjustments(expr.id)
            .map(|adj| adj.to_vec())
        {
            for adjustment in adjustments {
                thir_expr = self.apply_adjustment(expr.id, thir_expr, adjustment, expr.span);
            }
        }
        self.push_expr(thir_expr.kind, thir_expr.ty, thir_expr.span)
    }

    fn apply_adjustment(
        &mut self,
        _hir_id: hir::NodeID,
        expr: Expr<'ctx>,
        adjustment: Adjustment<'ctx>,
        span: crate::span::Span,
    ) -> Expr<'ctx> {
        let ty = expr.ty;
        match adjustment {
            Adjustment::Dereference => {
                let inner = match ty.kind() {
                    TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
                    // Logic error if we try to deref non-derefable type.
                    _ => return expr,
                };

                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::Deref(inner_id),
                    ty: inner,
                    span,
                }
            }
            Adjustment::BorrowMutable => {
                let ty = self
                    .gcx
                    .store
                    .interners
                    .intern_ty(TyKind::Reference(ty, Mutability::Mutable));

                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::Reference {
                        mutable: true,
                        expr: inner_id,
                    },
                    ty,
                    span,
                }
            }
            Adjustment::BorrowImmutable => {
                let ty = self
                    .gcx
                    .store
                    .interners
                    .intern_ty(TyKind::Reference(ty, Mutability::Immutable));
                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::Reference {
                        mutable: false,
                        expr: inner_id,
                    },
                    ty,
                    span,
                }
            }
            Adjustment::BoxExistential { .. } => {
                let Adjustment::BoxExistential { interfaces, .. } = adjustment else {
                    unreachable!()
                };
                let boxed_ty = Ty::new(TyKind::BoxedExistential { interfaces }, self.gcx);
                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::BoxExistential {
                        value: inner_id,
                        interfaces,
                    },
                    ty: boxed_ty,
                    span,
                }
            }
            Adjustment::ExistentialUpcast { .. } => {
                let Adjustment::ExistentialUpcast { to, .. } = adjustment else {
                    unreachable!()
                };
                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::ExistentialUpcast {
                        value: inner_id,
                        to,
                    },
                    ty: to,
                    span,
                }
            }
            Adjustment::OptionalWrap {
                is_some,
                generic_args,
            } => {
                let opt_id = self
                    .gcx
                    .find_std_type("Optional")
                    .expect("Optional type must exist");
                let enum_def = self.gcx.get_enum_definition(opt_id);
                let adt_def = enum_def.adt_def;

                let (variant_index, fields) = if is_some {
                    let some_idx = enum_def
                        .variants
                        .iter()
                        .position(|v| v.name.as_str() == "some")
                        .expect("Optional.some variant");
                    let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);
                    (
                        some_idx,
                        vec![thir::FieldExpression {
                            index: FieldIndex::from_usize(0),
                            expression: inner_id,
                        }],
                    )
                } else {
                    let none_idx = enum_def
                        .variants
                        .iter()
                        .position(|v| v.name.as_str() == "none")
                        .expect("Optional.none variant");
                    (none_idx, vec![])
                };

                let opt_ty = Ty::new(TyKind::Adt(adt_def, generic_args), self.gcx);
                Expr {
                    kind: ExprKind::Adt(thir::AdtExpression {
                        definition: adt_def,
                        variant_index: Some(VariantIndex::from_usize(variant_index)),
                        generic_args,
                        fields,
                    }),
                    ty: opt_ty,
                    span,
                }
            }
            Adjustment::Ignore(_) => expr,
            Adjustment::ClosureToFnPointer { closure_def_id } => {
                // Get the fn pointer type from the target type (set by type inference)
                // The closure expression is converted to a ClosureToFnPointer expression
                let closure_expr_id = self.push_expr(expr.kind, expr.ty, expr.span);

                // The result type should be the function pointer type.
                // Since this adjustment is only applied when coercing closure -> fn pointer,
                // the expected type from the coercion context provides the fn pointer type.
                // For now, we derive it from the closure's signature.
                let fn_ptr_ty = match expr.ty.kind() {
                    TyKind::Closure { inputs, output, .. } => {
                        Ty::new(TyKind::FnPointer { inputs, output }, self.gcx)
                    }
                    _ => expr.ty, // fallback, shouldn't happen
                };

                Expr {
                    kind: ExprKind::ClosureToFnPointer {
                        closure: closure_expr_id,
                        closure_def_id,
                    },
                    ty: fn_ptr_ty,
                    span,
                }
            }
        }
    }

    fn lower_expr_unadjusted(&mut self, expr: &hir::Expression) -> Expr<'ctx> {
        let ty = self.results.node_type(expr.id);
        let span = expr.span;
        let kind = match &expr.kind {
            hir::ExpressionKind::Literal(lit) => {
                let value = self.lower_literal(lit);
                ExprKind::Literal(Constant { ty, value })
            }
            hir::ExpressionKind::Array(items) => {
                let elements: Vec<_> = items.iter().map(|e| self.lower_expr(e)).collect();
                ExprKind::Array { elements }
            }
            hir::ExpressionKind::Repeat { value, count: _ } => {
                let element = self.lower_expr(value);
                let count = match ty.kind() {
                    TyKind::Array { len, .. } => match len.kind {
                        ConstKind::Value(ConstValue::Integer(i)) => {
                            debug_assert!(
                                i >= 0,
                                "repeat count should be validated during typechecking"
                            );
                            usize::try_from(i).unwrap_or(0)
                        }
                        _ => {
                            debug_assert!(
                                false,
                                "repeat count should be a concrete integer const after typechecking"
                            );
                            0
                        }
                    },
                    _ => {
                        debug_assert!(
                            false,
                            "repeat expressions should typecheck to array types before THIR lowering"
                        );
                        0
                    }
                };
                ExprKind::Repeat { element, count }
            }
            hir::ExpressionKind::Path(path) => {
                let res = if let Some(def_id) = self.results.overload_source(expr.id) {
                    Resolution::Definition(def_id, self.gcx.definition_kind(def_id))
                } else if let Some(resolution) = self.results.value_resolution(expr.id) {
                    resolution
                } else {
                    match path {
                        hir::ResolvedPath::Resolved(path) => path.resolution.clone(),
                        hir::ResolvedPath::Relative(..) => {
                            self.gcx.dcx().emit_error(
                                "unresolved relative path (typecheck should have resolved this)"
                                    .into(),
                                Some(expr.span),
                            );
                            Resolution::Error
                        }
                    }
                };
                self.lower_path_expression(expr, res)
            }
            hir::ExpressionKind::InferredMember { .. } => {
                let res = if let Some(def_id) = self.results.overload_source(expr.id) {
                    Resolution::Definition(def_id, self.gcx.definition_kind(def_id))
                } else if let Some(resolution) = self.results.value_resolution(expr.id) {
                    resolution
                } else {
                    self.gcx.dcx().emit_error(
                        "unresolved inferred member (typecheck should have resolved this)".into(),
                        Some(expr.span),
                    );
                    Resolution::Error
                };
                self.lower_path_expression(expr, res)
            }
            hir::ExpressionKind::Call { callee, arguments } => {
                // Builtin make: lower to ExprKind::Make.
                if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &callee.kind
                    && matches!(
                        path.resolution,
                        hir::Resolution::Foundation(hir::StdType::Make)
                    )
                {
                    if arguments.len() != 1 {
                        self.gcx.dcx().emit_error(
                            "`make` expects exactly one argument".into(),
                            Some(expr.span),
                        );
                        return Expr {
                            kind: ExprKind::Literal(Constant {
                                ty: self.gcx.types.error,
                                value: ConstantKind::Unit,
                            }),
                            ty: self.gcx.types.error,
                            span: expr.span,
                        };
                    }
                    let value = self.lower_expr(&arguments[0].expression);
                    return Expr {
                        kind: ExprKind::Make { value },
                        ty,
                        span,
                    };
                }
                if let Some(ctor_id) = self.variant_ctor_callee(callee) {
                    let (definition, variant_index) = self.enum_variant_from_ctor(ctor_id);
                    let TyKind::Adt(_, generic_args) = ty.kind() else {
                        self.gcx
                            .dcx()
                            .emit_info(format!("Type is {}", ty.format(self.gcx)), Some(expr.span));
                        unreachable!()
                    };
                    let fields = arguments
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| thir::FieldExpression {
                            index: FieldIndex::from_usize(index),
                            expression: self.lower_expr(&arg.expression),
                        })
                        .collect();
                    return Expr {
                        kind: ExprKind::Adt(thir::AdtExpression {
                            definition,
                            variant_index: Some(variant_index),
                            generic_args,
                            fields,
                        }),
                        ty,
                        span,
                    };
                }

                // Normal function call
                let thir_callee = self.lower_expr(callee);
                let final_args = if let Some(def_id) = self.resolve_direct_callee_id(callee) {
                    let signature = self.gcx.get_signature(def_id);
                    self.lower_call_args_with_defaults(
                        signature,
                        callee.id,
                        arguments,
                        &[],
                        expr.span,
                    )
                    .unwrap_or_else(|| {
                        debug_assert!(
                            false,
                            "failed to match direct call arguments for default values"
                        );
                        self.lower_call_args(arguments, &[])
                    })
                } else {
                    // Indirect call - just lower args as provided (no defaults).
                    self.lower_call_args(arguments, &[])
                };

                ExprKind::Call {
                    callee: thir_callee,
                    args: final_args,
                }
            }
            hir::ExpressionKind::Binary(op, lhs, rhs) => {
                // Check if this is an operator method call
                if let Some(def_id) = self.results.overload_source(expr.id) {
                    // Lower as a method call
                    let lhs_expr = self.lower_expr(lhs);
                    let rhs_expr = self.lower_expr(rhs);
                    let callee_ty = self.gcx.get_type(def_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: def_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        callee,
                        args: vec![lhs_expr, rhs_expr],
                    }
                } else {
                    match op {
                        hir::BinaryOperator::BoolAnd => ExprKind::Logical {
                            op: LogicalOperator::And,
                            lhs: self.lower_expr(lhs),
                            rhs: self.lower_expr(rhs),
                        },
                        hir::BinaryOperator::BoolOr => ExprKind::Logical {
                            op: LogicalOperator::Or,
                            lhs: self.lower_expr(lhs),
                            rhs: self.lower_expr(rhs),
                        },
                        hir::BinaryOperator::PtrEq => todo!(),
                        _ => {
                            let lhs = self.lower_expr(lhs);
                            let rhs = self.lower_expr(rhs);
                            let op = bin_op(*op);
                            ExprKind::Binary { op, lhs, rhs }
                        }
                    }
                }
            }
            hir::ExpressionKind::Unary(unary_op, operand) => {
                // Check if this is an operator method call
                if let Some(def_id) = self.results.overload_source(expr.id) {
                    // Lower as a method call
                    let operand_expr = self.lower_expr(operand);
                    let callee_ty = self.gcx.get_type(def_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: def_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        callee,
                        args: vec![operand_expr],
                    }
                } else {
                    let operand = self.lower_expr(operand);
                    let op = match unary_op {
                        hir::UnaryOperator::LogicalNot => mir::UnaryOperator::LogicalNot,
                        hir::UnaryOperator::Negate => mir::UnaryOperator::Negate,
                        hir::UnaryOperator::BitwiseNot => mir::UnaryOperator::BitwiseNot,
                    };
                    ExprKind::Unary { op, operand }
                }
            }
            hir::ExpressionKind::CastAs(value, _) => {
                let value = self.lower_expr(value);
                ExprKind::Cast { value }
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                let target = self.lower_expr(lhs);
                let value = self.lower_expr(rhs);
                ExprKind::Assign { target, value }
            }
            hir::ExpressionKind::AssignOp(op, lhs, rhs) => {
                // Check if this is an operator method call (e.g., AddAssign)
                if let Some(def_id) = self.results.overload_source(expr.id) {
                    // Lower as a method call
                    let lhs_expr = self.lower_expr(lhs);
                    let rhs_expr = self.lower_expr(rhs);
                    let callee_ty = self.gcx.get_type(def_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: def_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        callee,
                        args: vec![lhs_expr, rhs_expr],
                    }
                } else {
                    // Intrinsic compound assignment
                    let target = self.lower_expr(lhs);
                    let value = self.lower_expr(rhs);
                    let op = bin_op(*op);
                    ExprKind::AssignOp { op, target, value }
                }
            }
            hir::ExpressionKind::If(node) => {
                let cond = self.lower_expr(&node.condition);
                let then_expr = self.lower_expr(&node.then_block);
                let else_expr = node.else_block.as_deref().map(|expr| self.lower_expr(expr));
                ExprKind::If {
                    cond,
                    then_expr,
                    else_expr,
                }
            }
            hir::ExpressionKind::Match(node) => {
                let scrutinee = self.lower_expr(&node.value);
                let arms = node
                    .arms
                    .iter()
                    .map(|arm| self.lower_match_arm(arm))
                    .collect();
                ExprKind::Match { scrutinee, arms }
            }
            hir::ExpressionKind::Block(block) => {
                let block_id = self.lower_block(block);
                ExprKind::Block(block_id)
            }
            hir::ExpressionKind::UnsafeBlock(block) => {
                let block_id = self.lower_block(block);
                ExprKind::Block(block_id)
            }
            hir::ExpressionKind::Dereference(inner) => {
                let operand = self.lower_expr(inner);
                ExprKind::Deref(operand)
            }
            hir::ExpressionKind::Reference(inner, mutbl) => {
                let operand = self.lower_expr(inner);
                ExprKind::Reference {
                    mutable: *mutbl == hir::Mutability::Mutable,
                    expr: operand,
                }
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                name: _,
                arguments,
            } => {
                let Some(def_id) = self.results.overload_source(expr.id) else {
                    self.gcx.dcx().emit_error(
                        "failed to lower method call (no resolved target)".into(),
                        Some(expr.span),
                    );
                    return Expr {
                        kind: ExprKind::Literal(Constant {
                            ty: self.gcx.types.error,
                            value: ConstantKind::Unit,
                        }),
                        ty: self.gcx.types.error,
                        span: expr.span,
                    };
                };

                let recv = self.lower_expr(receiver);
                let receiver_args = [recv];
                let signature = self.gcx.get_signature(def_id);
                let final_args = self
                    .lower_call_args_with_defaults(
                        signature,
                        expr.id,
                        arguments,
                        &receiver_args,
                        expr.span,
                    )
                    .unwrap_or_else(|| {
                        debug_assert!(
                            false,
                            "failed to match method call arguments for default values"
                        );
                        self.lower_call_args(arguments, &receiver_args)
                    });

                let callee_ty = self.gcx.get_type(def_id);
                let generic_args = self.results.instantiation(expr.id);
                let callee = self.push_expr(
                    ExprKind::Zst {
                        id: def_id,
                        generic_args,
                    },
                    callee_ty,
                    expr.span,
                );
                ExprKind::Call {
                    callee,
                    args: final_args,
                }
            }

            hir::ExpressionKind::StructLiteral(literal) => {
                let TyKind::Adt(definition, generic_args) = ty.kind() else {
                    unreachable!()
                };

                if !matches!(definition.kind, AdtKind::Struct) {
                    unreachable!()
                }

                let node = thir::AdtExpression {
                    definition,
                    variant_index: None,
                    generic_args,
                    fields: literal
                        .fields
                        .iter()
                        .map(|f| thir::FieldExpression {
                            expression: self.lower_expr(&f.expression),
                            index: FieldIndex::from_usize(
                                self.results
                                    .field_index(f.expression.id)
                                    .expect("Field Index"),
                            ),
                        })
                        .collect(),
                };

                ExprKind::Adt(node)
            }
            hir::ExpressionKind::Member { target, .. } => {
                let lhs = self.lower_expr(target);
                ExprKind::Field {
                    lhs,
                    index: FieldIndex::from_usize(
                        self.results.field_index(expr.id).expect("Field Index"),
                    ),
                }
            }
            hir::ExpressionKind::Tuple(elems) => {
                let fields = elems.iter().map(|e| self.lower_expr(&e)).collect();
                ExprKind::Tuple { fields }
            }
            hir::ExpressionKind::TupleAccess(target, ..) => {
                let lhs = self.lower_expr(target);
                ExprKind::Field {
                    lhs,
                    index: FieldIndex::from_usize(
                        self.results.field_index(expr.id).expect("Field Index"),
                    ),
                }
            }
            hir::ExpressionKind::PatternBinding(condition) => {
                // Lower `case pattern = expr` to a match that returns true if the pattern matches.
                // match expr { case pattern => true, case _ => false }
                let scrutinee = self.lower_expr(&condition.expression);
                let pattern = pattern_from_hir(self.gcx, self.results.as_ref(), &condition.pattern);

                // Create the "true" arm for when the pattern matches
                let true_lit = self.push_expr(
                    ExprKind::Literal(Constant {
                        ty: self.gcx.types.bool,
                        value: ConstantKind::Bool(true),
                    }),
                    self.gcx.types.bool,
                    condition.span,
                );
                let true_arm_id = {
                    let id = thir::ArmId::from_raw(self.func.arms.len() as u32);
                    self.func.arms.push(thir::Arm {
                        pattern: Box::new(pattern),
                        guard: None,
                        body: true_lit,
                        span: condition.span,
                    });
                    id
                };

                // Create the "false" arm (wildcard) for when the pattern doesn't match
                let false_lit = self.push_expr(
                    ExprKind::Literal(Constant {
                        ty: self.gcx.types.bool,
                        value: ConstantKind::Bool(false),
                    }),
                    self.gcx.types.bool,
                    condition.span,
                );
                let wild_pattern = thir::Pattern {
                    ty: self.results.node_type(condition.expression.id),
                    span: condition.span,
                    kind: thir::PatternKind::Wild,
                };
                let false_arm_id = {
                    let id = thir::ArmId::from_raw(self.func.arms.len() as u32);
                    self.func.arms.push(thir::Arm {
                        pattern: Box::new(wild_pattern),
                        guard: None,
                        body: false_lit,
                        span: condition.span,
                    });
                    id
                };

                ExprKind::Match {
                    scrutinee,
                    arms: vec![true_arm_id, false_arm_id],
                }
            }
            hir::ExpressionKind::Closure(closure) => {
                // Get closure capture information from type checking phase
                let captures_info = self.gcx.get_closure_captures(closure.def_id);
                let kind = captures_info
                    .as_ref()
                    .map(|c| c.kind)
                    .unwrap_or(crate::sema::models::ClosureKind::Fn);

                // Build capture expressions for each captured variable
                let mut captures = vec![];
                if let Some(ref caps) = captures_info {
                    for cap in &caps.captures {
                        // Check if this capture is itself an upvar in our current closure scope
                        // (needed for nested closures)
                        let base_expr_kind = if let Some(captures_map) = &self.captures_map {
                            if let Some(&(outer_field_index, outer_capture_kind)) =
                                captures_map.get(&cap.source_id)
                            {
                                // Variable is captured from outer closure - generate Upvar
                                ExprKind::Upvar {
                                    field_index: outer_field_index,
                                    capture_kind: outer_capture_kind,
                                }
                            } else {
                                ExprKind::Local(cap.source_id)
                            }
                        } else {
                            ExprKind::Local(cap.source_id)
                        };

                        let mut capture_expr_id = self.func.exprs.push(Expr {
                            kind: base_expr_kind,
                            ty: cap.ty,
                            span,
                        });

                        // For by-ref captures, wrap the local in a reference expression.
                        if let crate::sema::models::CaptureKind::ByRef { mutable } =
                            cap.capture_kind
                        {
                            let mutability = if mutable {
                                crate::hir::Mutability::Mutable
                            } else {
                                crate::hir::Mutability::Immutable
                            };
                            let ref_ty = Ty::new(
                                crate::sema::models::TyKind::Reference(cap.ty, mutability),
                                self.gcx,
                            );
                            capture_expr_id = self.func.exprs.push(Expr {
                                kind: ExprKind::Reference {
                                    mutable,
                                    expr: capture_expr_id,
                                },
                                ty: ref_ty,
                                span,
                            });
                        }

                        captures.push(ClosureCapture {
                            source_id: cap.source_id,
                            capture_expr: capture_expr_id,
                            capture_kind: cap.capture_kind,
                            field_index: cap.field_index,
                        });
                    }
                }

                // Generate THIR function for the closure body
                let closure_func = self.lower_closure_body(closure);
                self.nested_closures.push(closure_func);

                ExprKind::Closure {
                    def_id: closure.def_id,
                    captures,
                    kind,
                }
            }
            hir::ExpressionKind::Malformed => {
                unreachable!("malformed expression should not reach THIR lowering");
            }
        };

        Expr { kind, ty, span }
    }

    fn lower_literal(&self, lit: &hir::Literal) -> ConstantKind {
        match lit {
            hir::Literal::Bool(b) => ConstantKind::Bool(*b),
            hir::Literal::Rune(r) => ConstantKind::Rune(*r),
            hir::Literal::String(s) => ConstantKind::String(*s),
            hir::Literal::Integer(i) => ConstantKind::Integer(*i),
            hir::Literal::Float(f) => ConstantKind::Float(*f),
            hir::Literal::Nil => ConstantKind::Unit,
        }
    }

    /// Lower a closure body into a separate THIR function
    fn lower_closure_body(&mut self, closure: &hir::ClosureExpr) -> ThirFunction<'ctx> {
        // Get captures for this closure
        let captures = self.gcx.get_closure_captures(closure.def_id);

        // Build the captures_map: source_id -> (field_index, type)
        let captures_map = captures.as_ref().map(|caps| {
            caps.captures
                .iter()
                .map(|cap| (cap.source_id, (cap.field_index, cap.capture_kind)))
                .collect::<FxHashMap<_, _>>()
        });

        // Generate a synthetic node ID for the self parameter
        // Use a high value based on the closure def_id's package to avoid collisions
        let self_param_id = crate::hir::NodeID::from_raw(
            closure
                .def_id
                .package()
                .raw()
                .wrapping_mul(0x10000)
                .wrapping_add(0xFFFF0000),
        );

        // Create a new FunctionLower for the closure body
        let mut closure_lower = FunctionLower {
            gcx: self.gcx,
            results: self.results.clone(),
            func: ThirFunction {
                id: closure.def_id,
                body: None,
                span: closure.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_trees: FxHashMap::default(),
            },
            nested_closures: Vec::new(),
            captures_map,
        };

        // Get the full signature (self pointer + explicit params)
        let signature = self.gcx.get_signature(closure.def_id);

        // Add the self parameter (pointer to closure struct)
        // This is the first parameter in the signature - MIR will place it at _1
        if !signature.inputs.is_empty() {
            let self_sig_param = &signature.inputs[0];
            closure_lower.func.params.push(Param {
                id: self_param_id, // Synthetic ID, not referenced by body
                name: self_sig_param.name,
                ty: self_sig_param.ty,
                span: closure.span,
            });
        }

        // Add explicit closure parameters (after self in the signature)
        for (param, sig_param) in closure.params.iter().zip(signature.inputs.iter().skip(1)) {
            closure_lower.func.params.push(Param {
                id: param.id,
                name: sig_param.name,
                ty: sig_param.ty,
                span: param.span,
            });
        }

        // Lower the closure body expression
        let body_expr_id = closure_lower.lower_expr(&closure.body);

        // Create a block containing just the body expression
        let block_id = BlockId::from_raw(closure_lower.func.blocks.len() as u32);
        closure_lower.func.blocks.push(Block {
            id: block_id,
            stmts: vec![],
            expr: Some(body_expr_id),
        });
        closure_lower.func.body = Some(block_id);

        // Collect any nested closures from within this closure
        self.nested_closures.extend(closure_lower.nested_closures);

        closure_lower.func
    }

    fn lower_path_expression(
        &mut self,
        expr: &hir::Expression,
        resolution: Resolution,
    ) -> thir::ExprKind<'ctx> {
        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::Function | DefinitionKind::AssociatedFunction,
            ) => ExprKind::Zst {
                id,
                generic_args: self.results.instantiation(expr.id),
            },
            Resolution::Definition(
                id,
                DefinitionKind::Constant | DefinitionKind::AssociatedConstant,
            ) => {
                let Some(constant) = self.gcx.try_get_const(id) else {
                    self.gcx
                        .dcx()
                        .emit_error("constant value is not available".into(), Some(expr.span));
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                let Some(value) = self.const_kind_to_thir(constant.kind) else {
                    self.gcx.dcx().emit_error(
                        "const parameter values are not supported here".into(),
                        Some(expr.span),
                    );
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                ExprKind::Literal(Constant {
                    ty: constant.ty,
                    value,
                })
            }
            Resolution::Definition(id, DefinitionKind::ConstParameter) => {
                let ty = self.results.node_type(expr.id);
                let Some(owner) = self.gcx.definition_parent(id) else {
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                let generics = self.gcx.generics_of(owner);
                let Some(def) = generics.parameters.iter().find(|p| p.id == id) else {
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                let param = crate::sema::models::GenericParameter {
                    index: def.index,
                    name: def.name,
                };
                ExprKind::Literal(Constant {
                    ty,
                    value: ConstantKind::ConstParam(param),
                })
            }
            Resolution::Definition(
                id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Function),
            ) => ExprKind::Zst {
                id,
                generic_args: self.results.instantiation(expr.id),
            },
            Resolution::Definition(
                ctor_id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
            ) => {
                let (definition, variant_index) = self.enum_variant_from_ctor(ctor_id);
                let ty = self.results.node_type(expr.id);
                let TyKind::Adt(_, generic_args) = ty.kind() else {
                    unreachable!()
                };
                ExprKind::Adt(thir::AdtExpression {
                    definition,
                    variant_index: Some(variant_index),
                    generic_args,
                    fields: Vec::new(),
                })
            }
            Resolution::LocalVariable(id) => {
                // Check if this is a captured variable that needs to be accessed via upvar
                if let Some(captures_map) = &self.captures_map {
                    if let Some(&(field_index, capture_kind)) = captures_map.get(&id) {
                        // This is a captured variable - generate Upvar access
                        return ExprKind::Upvar {
                            field_index,
                            capture_kind,
                        };
                    }
                }
                // Not a capture - regular local variable
                ExprKind::Local(id)
            }
            _ => unreachable!(),
        }
    }

    fn const_kind_to_thir(&self, kind: ConstKind) -> Option<ConstantKind> {
        match kind {
            ConstKind::Value(value) => Some(match value {
                ConstValue::Bool(b) => ConstantKind::Bool(b),
                ConstValue::Rune(r) => ConstantKind::Rune(r),
                ConstValue::String(s) => ConstantKind::String(s),
                ConstValue::Integer(i) => ConstantKind::Integer(i as u64),
                ConstValue::Float(f) => ConstantKind::Float(f),
                ConstValue::Unit => ConstantKind::Unit,
            }),
            ConstKind::Param(p) => Some(ConstantKind::ConstParam(p)),
            ConstKind::Infer(_) => None,
        }
    }

    fn push_expr(&mut self, kind: ExprKind<'ctx>, ty: Ty<'ctx>, span: crate::span::Span) -> ExprId {
        let id = ExprId::from_raw(self.func.exprs.len() as u32);
        self.func.exprs.push(Expr { kind, ty, span });
        id
    }

    fn variant_ctor_callee(&self, callee: &hir::Expression) -> Option<DefinitionID> {
        let resolution = if let Some(def_id) = self.results.overload_source(callee.id) {
            Some(Resolution::Definition(
                def_id,
                self.gcx.definition_kind(def_id),
            ))
        } else {
            match &callee.kind {
                hir::ExpressionKind::Path(path) => match path {
                    hir::ResolvedPath::Resolved(path) => Some(path.resolution.clone()),
                    hir::ResolvedPath::Relative(..) => self.results.value_resolution(callee.id),
                },
                hir::ExpressionKind::InferredMember { .. } => {
                    self.results.value_resolution(callee.id)
                }
                _ => None,
            }
        }?;

        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Function),
            ) => Some(id),
            _ => None,
        }
    }

    fn enum_variant_from_ctor(
        &self,
        ctor_id: DefinitionID,
    ) -> (crate::sema::models::AdtDef, VariantIndex) {
        let Some(parent_id) = self.gcx.definition_parent(ctor_id) else {
            unreachable!()
        };

        let enum_id = match self.gcx.definition_kind(parent_id) {
            DefinitionKind::Enum => parent_id,
            DefinitionKind::Variant => match self.gcx.definition_parent(parent_id) {
                Some(enum_id) => enum_id,
                None => {
                    unreachable!()
                }
            },
            _ => {
                unreachable!()
            }
        };

        let def = self.gcx.get_enum_definition(enum_id);
        let Some((index, _)) = def
            .variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.ctor_def_id == ctor_id)
        else {
            unreachable!()
        };

        (def.adt_def, VariantIndex::from_usize(index))
    }

    fn lower_match_arm(&mut self, arm: &hir::MatchArm) -> thir::ArmId {
        let guard = arm.guard.as_deref().map(|expr| self.lower_expr(expr));
        let body = self.lower_expr(&arm.body);
        let pattern = pattern_from_hir(self.gcx, self.results.as_ref(), &arm.pattern);
        let id = thir::ArmId::from_raw(self.func.arms.len() as u32);
        self.func.arms.push(thir::Arm {
            pattern: Box::new(pattern),
            guard,
            body,
            span: arm.span,
        });
        id
    }

    fn push_stmt(&mut self, stmt: Stmt<'ctx>) -> StmtId {
        let id = StmtId::from_raw(self.func.stmts.len() as u32);
        self.func.stmts.push(stmt);
        id
    }
}

fn bin_op(op: hir::BinaryOperator) -> mir::BinaryOperator {
    match op {
        hir::BinaryOperator::Add => mir::BinaryOperator::Add,
        hir::BinaryOperator::Sub => mir::BinaryOperator::Sub,
        hir::BinaryOperator::Mul => mir::BinaryOperator::Mul,
        hir::BinaryOperator::Div => mir::BinaryOperator::Div,
        hir::BinaryOperator::Rem => mir::BinaryOperator::Rem,
        hir::BinaryOperator::BitOr => mir::BinaryOperator::BitOr,
        hir::BinaryOperator::BitXor => mir::BinaryOperator::BitXor,
        hir::BinaryOperator::BitShl => mir::BinaryOperator::BitShl,
        hir::BinaryOperator::BitShr => mir::BinaryOperator::BitShr,
        hir::BinaryOperator::Eql => mir::BinaryOperator::Eql,
        hir::BinaryOperator::Lt => mir::BinaryOperator::Lt,
        hir::BinaryOperator::Gt => mir::BinaryOperator::Gt,
        hir::BinaryOperator::Leq => mir::BinaryOperator::Leq,
        hir::BinaryOperator::Geq => mir::BinaryOperator::Geq,
        hir::BinaryOperator::Neq => mir::BinaryOperator::Neq,
        _ => {
            unreachable!()
        }
    }
}
