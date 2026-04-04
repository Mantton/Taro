use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, HirVisitor, NodeID},
    sema::{
        models::{
            Const, ConstKind, ConstValue, GenericArgument, GenericArguments, GenericParameter,
            GenericParameterDefinition, GenericParameterDefinitionKind, IntTy, InterfaceReference,
            Ty, TyKind, UIntTy,
        },
        resolve::models::{DefinitionKind, TypeHead, VariantCtorKind},
        tycheck::{
            check::{checker::Checker, gather::GatherLocalsVisitor},
            infer::InferCtx,
            lower::lowerer::TypeLowerer,
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, AssignOpGoalData, BinOpGoalData,
                BindOverloadGoalData, ConstraintSystem, DerefGoalData, DisjunctionBranch, Goal,
                InferredStaticMemberGoalData, MemberGoalData, MethodCallData, StructLiteralField,
                StructLiteralGoalData, TupleAccessGoalData, UnOpGoalData,
                match_arguments_to_parameters, validate_arity,
            },
            utils::{
                const_eval::eval_const_expression,
                generics::GenericsBuilder,
                instantiate::{
                    instantiate_const_with_args, instantiate_interface_ref_with_args,
                    instantiate_signature_with_args, instantiate_ty_with_args,
                },
                type_head_from_value_ty,
            },
        },
    },
    span::{Span, Symbol},
};
use rustc_hash::FxHashSet;
use std::rc::Rc;

#[derive(Clone, Copy)]
struct ArgumentExpectation<'ctx> {
    ty: Ty<'ctx>,
    expects_async_callable: bool,
}

#[derive(Clone, Copy)]
struct ResolvedCallableBound<'ctx> {
    fn_signature_ty: Ty<'ctx>,
    expects_async_callable: bool,
}

impl<'ctx> Checker<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.context
    }

    pub fn check_constant(&mut self, id: DefinitionID, node: &hir::Constant) {
        let gcx = self.gcx();
        let expected = gcx.get_type(id);
        let Some(expr) = &node.expr else {
            gcx.dcx().emit_error(
                "constant declarations must have an initializer".into(),
                Some(node.identifier.span),
            );
            return;
        };

        let provided = self.top_level_check(expr, Some(expected));
        if provided.is_error() {
            return;
        }

        let Some(value) = eval_const_expression(gcx, expr) else {
            return;
        };

        gcx.cache_const(
            id,
            Const {
                ty: expected,
                kind: ConstKind::Value(value),
            },
        );
    }

    pub fn check_static_variable(&mut self, id: DefinitionID, node: &hir::StaticVariable) {
        let gcx = self.gcx();
        let expected = gcx.get_type(id);

        let provided = self.top_level_check(&node.initializer, Some(expected));
        if provided.is_error() {
            return;
        }

        let value = match self.results.borrow().value_resolution(node.initializer.id) {
            Some(hir::Resolution::Definition(
                ctor_id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
            )) => Some(ConstValue::EnumUnitVariant(ctor_id)),
            _ => eval_const_expression(gcx, &node.initializer),
        };
        let Some(value) = value else {
            return;
        };

        gcx.cache_static_initializer(
            id,
            Const {
                ty: expected,
                kind: ConstKind::Value(value),
            },
        );
    }

    pub fn check_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        _: hir::FunctionContext,
    ) {
        let gcx = self.gcx();
        let signature = gcx.get_signature(id);
        let identity_args = GenericsBuilder::identity_for_item(gcx, id);
        let signature = instantiate_signature_with_args(gcx, signature, identity_args);
        let signature = Ty::from_labeled_signature(gcx, &signature);
        let (param_tys, return_ty) = match signature.kind() {
            TyKind::FnPointer { inputs, output, .. } => (inputs, output),
            _ => unreachable!("function signature must be of function pointer type"),
        };

        let body_return_ty = if node.is_async {
            gcx.function_body_output(id)
        } else {
            return_ty
        };

        self.return_ty.set(Some(body_return_ty));

        let param_ids: Vec<NodeID> = node
            .signature
            .prototype
            .inputs
            .iter()
            .map(|param| param.id)
            .collect();
        let param_symbols: Vec<Symbol> = node
            .signature
            .prototype
            .inputs
            .iter()
            .map(|param| param.name.symbol)
            .collect();

        // Add Parameters To Locals Map
        for (parameter, parameter_ty) in node
            .signature
            .prototype
            .inputs
            .iter()
            .zip(param_tys.iter().cloned())
        {
            self.locals.borrow_mut().insert(
                parameter.id,
                crate::sema::tycheck::check::checker::LocalBinding {
                    ty: parameter_ty,
                    mutable: false,
                },
            );

            if let Some(expr) = &parameter.default_value {
                let mut checker = DefaultParamRefChecker {
                    param_ids: &param_ids,
                    param_symbols: &param_symbols,
                    found: false,
                };
                hir::walk_expression(&mut checker, expr);
                if checker.found {
                    gcx.dcx().emit_error(
                        "default parameter values cannot reference parameters".into(),
                        Some(expr.span),
                    );
                }
                self.with_return_ty(Some(parameter_ty), || {
                    self.top_level_check(expr, Some(parameter_ty));
                });
            }
        }

        let Some(body) = &node.block else {
            // Extern function declaration.
            return;
        };

        // Async functions introduce an async context for their body.
        if node.is_async {
            self.async_depth.set(1);
        }

        if let Some(body) = hir::is_expression_bodied(body) {
            // --- single-expression body ---
            self.check_return(Some(body), body.span, None);
        } else {
            // --- regular block body ---
            self.check_block(body, None);
        }

        if node.is_async {
            self.async_depth.set(0);
        }
    }
}

impl<'ctx> Checker<'ctx> {
    fn check_statement(&self, node: &hir::Statement, mut cs: Option<&mut Cs<'ctx>>) {
        match &node.kind {
            hir::StatementKind::Declaration(decl) => {
                self.check_local_declaration(decl);
            }
            hir::StatementKind::Expression(node) => {
                if let Some(cs) = cs.as_mut() {
                    self.synth_with_expectation(node, None, cs);
                } else {
                    self.top_level_check(node, None);
                }
            }
            hir::StatementKind::Variable(node) => {
                if let Some(cs) = cs.as_mut() {
                    self.check_local_in_block(node, cs);
                } else {
                    self.check_local(node);
                }
            }
            hir::StatementKind::Loop { block, .. } => {
                self.check_loop(block, cs);
            }
            hir::StatementKind::Defer(block) => {
                self.check_defer(block, cs.as_deref_mut());
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                self.check_guard(condition, else_block, cs.as_deref_mut());
            }
        }
    }

    fn check_local_declaration(&self, decl: &hir::Declaration) {
        match &decl.kind {
            hir::DeclarationKind::Function(node) => {
                let mut checker = Checker::new(self.context, decl.id, self.results.clone());
                checker.check_function(decl.id, node, hir::FunctionContext::Free);
            }
            hir::DeclarationKind::Constant(node) => {
                let mut checker = Checker::new(self.context, decl.id, self.results.clone());
                checker.check_constant(decl.id, node);
            }
            _ => {}
        }
    }

    fn check_return(
        &self,
        expression: Option<&hir::Expression>,
        span: Span,
        mut cs: Option<&mut Cs<'ctx>>,
    ) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`return` is not allowed inside a defer block".into(),
                Some(span),
            );
        }

        let Some(expression) = expression else {
            return;
        };

        let Some(expectation) = self.return_ty.get() else {
            unreachable!("ICE: return check called outside function body")
        };
        if let Some(cs) = cs.as_deref_mut() {
            let provided = self.synth_with_expectation(expression, Some(expectation), cs);
            cs.add_goal(
                Goal::Coerce {
                    node_id: expression.id,
                    from: provided,
                    to: expectation,
                },
                expression.span,
            );
        } else {
            self.top_level_check(expression, Some(expectation));
        }
    }

    fn check_defer(&self, node: &hir::Block, mut cs: Option<&mut Cs<'ctx>>) {
        let depth = self.defer_depth.get();
        self.defer_depth.set(depth + 1);
        self.check_block(node, cs.as_deref_mut());
        self.defer_depth.set(depth);
    }

    fn check_block(&self, node: &hir::Block, mut cs: Option<&mut Cs<'ctx>>) {
        for statement in &node.statements {
            self.check_statement(statement, cs.as_deref_mut());
        }
        if let Some(tail) = node.tail.as_deref() {
            if let Some(cs) = cs.as_deref_mut() {
                self.synth_with_expectation(tail, None, cs);
            } else {
                self.top_level_check(tail, None);
            }
        }
    }

    fn check_guard(
        &self,
        condition: &hir::Expression,
        else_block: &hir::Block,
        mut cs: Option<&mut Cs<'ctx>>,
    ) {
        // Else block is not allowed to see bindings introduced by the guard condition.
        self.check_block(else_block, cs.as_deref_mut());

        if let Some(cs) = cs.as_deref_mut() {
            let cond_ty = self.synth(condition, cs);
            cs.equal(self.gcx().types.bool, cond_ty, condition.span);
        } else {
            self.top_level_check(condition, Some(self.gcx().types.bool));
        }
    }
    fn check_opaque_type_usage(&self, ty: Ty<'ctx>, span: Span, behind_pointer: bool) {
        match ty.kind() {
            TyKind::Opaque(def_id) => {
                if !behind_pointer {
                    let ident = self.gcx().definition_ident(def_id);
                    self.gcx().dcx().emit_error(
                        format!(
                            "opaque type `{}` can only be used behind a pointer",
                            self.gcx().symbol_text(ident.symbol)
                        ),
                        Some(span),
                    );
                }
            }
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                self.check_opaque_type_usage(inner, span, true);
            }
            TyKind::Tuple(items) => {
                for item in items.iter() {
                    self.check_opaque_type_usage(*item, span, false);
                }
            }
            TyKind::Array { element, .. } => {
                self.check_opaque_type_usage(element, span, false);
            }
            _ => {}
        }
    }

    fn check_local(&self, node: &hir::Local) {
        let mut cs = self.new_cs();
        self.with_infer_ctx(cs.infer_cx.clone(), || {
            GatherLocalsVisitor::from_local(&cs, &self, node);
            let local_ty = self.get_local(node.id).ty;
            if let Some(annotation) = node.ty.as_deref() {
                self.check_opaque_type_usage(local_ty, annotation.span, false);
                self.add_type_constraints(local_ty, annotation.span, &mut cs);
            }

            if let Some(expression) = node.initializer.as_ref() {
                let init_ty = self.synth_with_expectation(expression, Some(local_ty), &mut cs);
                if node.ty.is_none()
                    && matches!(node.pattern.kind, hir::PatternKind::Wildcard)
                    && matches!(
                        cs.infer_cx.resolve_vars_if_possible(init_ty).kind(),
                        TyKind::Never
                    )
                {
                    cs.equal(local_ty, init_ty, expression.span);
                } else {
                    cs.add_goal(
                        Goal::Coerce {
                            node_id: expression.id,
                            from: init_ty,
                            to: local_ty,
                        },
                        expression.span,
                    );
                }
            }

            let scrutinee_id = node.initializer.as_ref().map(|e| e.id).unwrap_or(node.id);
            self.check_pattern(&node.pattern, local_ty, scrutinee_id, &mut cs);
            cs.solve_all();

            self.commit_constraint_results(&cs);
        });
    }

    fn check_local_in_block(&self, node: &hir::Local, cs: &mut Cs<'ctx>) {
        GatherLocalsVisitor::from_local(cs, self, node);
        let local_ty = self.get_local(node.id).ty;
        if let Some(annotation) = node.ty.as_deref() {
            self.check_opaque_type_usage(local_ty, annotation.span, false);
            self.add_type_constraints(local_ty, annotation.span, cs);
        }

        if let Some(expression) = node.initializer.as_ref() {
            let init_ty = self.synth_with_expectation(expression, Some(local_ty), cs);
            if node.ty.is_none()
                && matches!(node.pattern.kind, hir::PatternKind::Wildcard)
                && matches!(
                    cs.infer_cx.resolve_vars_if_possible(init_ty).kind(),
                    TyKind::Never
                )
            {
                cs.equal(local_ty, init_ty, expression.span);
            } else {
                cs.add_goal(
                    Goal::Coerce {
                        node_id: expression.id,
                        from: init_ty,
                        to: local_ty,
                    },
                    expression.span,
                );
            }
        }

        let scrutinee_id = node.initializer.as_ref().map(|e| e.id).unwrap_or(node.id);
        self.check_pattern(&node.pattern, local_ty, scrutinee_id, cs);
    }

    fn check_loop(&self, block: &hir::Block, mut cs: Option<&mut Cs<'ctx>>) {
        let depth = self.loop_depth.get();
        self.loop_depth.set(depth + 1);
        self.check_block(block, cs.as_deref_mut());
        self.loop_depth.set(depth);
    }

    fn check_break(&self, span: Span) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`break` is not allowed inside a defer block".into(),
                Some(span),
            );
            return;
        }

        if self.loop_depth.get() == 0 {
            self.gcx()
                .dcx()
                .emit_error("`break` used outside of a loop".into(), Some(span));
        }
    }

    fn check_continue(&self, span: Span) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`continue` is not allowed inside a defer block".into(),
                Some(span),
            );
            return;
        }

        if self.loop_depth.get() == 0 {
            self.gcx()
                .dcx()
                .emit_error("`continue` used outside of a loop".into(), Some(span));
        }
    }
}

impl<'ctx> Checker<'ctx> {
    fn top_level_check(
        &self,
        expression: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
    ) -> Ty<'ctx> {
        let mut cs = self.new_cs();
        let result = self.with_infer_ctx(cs.infer_cx.clone(), || {
            let provided = self.synth_with_expectation(expression, expectation, &mut cs);
            if let Some(expectation) = expectation {
                self.add_type_constraints(expectation, expression.span, &mut cs);
                cs.add_goal(
                    Goal::Coerce {
                        node_id: expression.id,
                        from: provided,
                        to: expectation,
                    },
                    expression.span,
                );
            }
            cs.solve_all();

            self.commit_constraint_results(&cs);

            let provided = cs.infer_cx.resolve_vars_if_possible(provided);
            if provided.is_infer() {
                return Ty::error(self.gcx());
            }
            provided
        });
        result
    }

    fn new_cs(&self) -> Cs<'ctx> {
        if let Some(infer_cx) = self.infer_ctx() {
            Cs::with_infer_ctx(
                self.context,
                self.current_def,
                infer_cx,
                self.visible_traits.clone(),
            )
        } else {
            Cs::with_infer_ctx(
                self.context,
                self.current_def,
                Rc::new(InferCtx::new(self.context)),
                self.visible_traits.clone(),
            )
        }
    }

    /// Commits all resolved results from a constraint system to the checker's results.
    /// Used when solving sub-expressions in separate constraint systems (e.g., match scrutinee).
    fn commit_constraint_results(&self, cs: &Cs<'ctx>) {
        for (id, ty) in cs.resolved_expr_types() {
            let ty = cs.infer_cx.resolve_vars_or_error(ty);
            self.results.borrow_mut().record_node_type(id, ty);

            // FIX: Update closure signature with resolved types to ensure codegen sees concrete types
            if let TyKind::Closure { closure_def_id, .. } = ty.kind() {
                self.update_closure_signature(closure_def_id, ty);
            }
        }
        for (id, adjustments) in cs.resolved_adjustments() {
            let adjustments: Vec<_> = adjustments
                .into_iter()
                .map(|adjustment| self.resolve_adjustment(cs, adjustment))
                .collect();
            self.results
                .borrow_mut()
                .record_node_adjustments(id, adjustments);
        }
        for (id, info) in cs.resolved_interface_calls() {
            self.results.borrow_mut().record_interface_call(id, info);
        }
        for (id, def_id) in cs.resolved_overload_sources() {
            self.results.borrow_mut().record_overload_source(id, def_id);
        }
        for (id, resolution) in cs.resolved_value_resolutions() {
            self.results
                .borrow_mut()
                .record_value_resolution(id, resolution);
        }
        for (id, index) in cs.resolved_field_indices() {
            self.results.borrow_mut().record_field_index(id, index);
        }
        for (id, info) in cs.resolved_property_reads() {
            self.results.borrow_mut().record_property_read(id, info);
        }
        for (id, info) in cs.resolved_property_writes() {
            self.results.borrow_mut().record_property_write(id, info);
        }
        for (id, args) in cs.resolved_instantiations() {
            let resolved_args = cs.infer_cx.resolve_args_if_possible(args);
            self.results
                .borrow_mut()
                .record_instantiation(id, resolved_args);
        }
        for (id, ty) in cs.resolved_local_types() {
            let ty = cs.infer_cx.resolve_vars_or_error(ty);
            self.finalize_local(id, ty);
            self.results.borrow_mut().record_node_type(id, ty);
        }

        self.finalize_deferred_async_call_surface_checks(cs);
        self.finalize_deferred_async_property_surface_checks(cs);
    }

    fn resolve_adjustment(&self, cs: &Cs<'ctx>, adjustment: Adjustment<'ctx>) -> Adjustment<'ctx> {
        match adjustment {
            Adjustment::BoxExistential { from, interfaces } => Adjustment::BoxExistential {
                from: cs.infer_cx.resolve_vars_or_error(from),
                interfaces: self.resolve_interface_refs_for_adjustment(cs, interfaces),
            },
            Adjustment::ExistentialUpcast { from, to } => Adjustment::ExistentialUpcast {
                from: cs.infer_cx.resolve_vars_or_error(from),
                to: cs.infer_cx.resolve_vars_or_error(to),
            },
            Adjustment::OptionalWrap {
                is_some,
                generic_args,
            } => Adjustment::OptionalWrap {
                is_some,
                generic_args: self.resolve_generic_args_or_error(cs, generic_args),
            },
            other => other,
        }
    }

    fn resolve_interface_refs_for_adjustment(
        &self,
        cs: &Cs<'ctx>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
    ) -> &'ctx [InterfaceReference<'ctx>] {
        if interfaces.is_empty() {
            return interfaces;
        }

        let resolved: Vec<_> = interfaces
            .iter()
            .map(|iface| {
                let arguments = self.resolve_generic_args_or_error(cs, iface.arguments);
                let bindings: Vec<_> = iface
                    .bindings
                    .iter()
                    .map(|binding| crate::sema::models::AssociatedTypeBinding {
                        name: binding.name,
                        ty: cs.infer_cx.resolve_vars_or_error(binding.ty),
                    })
                    .collect();
                let bindings = self.gcx().store.arenas.global.alloc_slice_clone(&bindings);

                InterfaceReference {
                    id: iface.id,
                    arguments,
                    bindings,
                }
            })
            .collect();

        self.gcx().store.arenas.global.alloc_slice_clone(&resolved)
    }

    fn resolve_generic_args_or_error(
        &self,
        cs: &Cs<'ctx>,
        args: GenericArguments<'ctx>,
    ) -> GenericArguments<'ctx> {
        if args.is_empty() {
            return args;
        }

        let resolved: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => {
                    GenericArgument::Type(cs.infer_cx.resolve_vars_or_error(*ty))
                }
                GenericArgument::Const(c) => {
                    GenericArgument::Const(cs.infer_cx.resolve_const_if_possible(*c))
                }
            })
            .collect();

        self.gcx().store.interners.intern_generic_args(resolved)
    }
}

type Cs<'c> = ConstraintSystem<'c>;
impl<'ctx> Checker<'ctx> {
    fn add_type_constraints(&self, ty: Ty<'ctx>, span: Span, cs: &mut Cs<'ctx>) {
        let ty = cs.infer_cx.resolve_vars_if_possible(ty);
        match ty.kind() {
            TyKind::Adt(def, args) => {
                cs.add_constraints_for_def(def.id, Some(args), span);
                for arg in args.iter() {
                    if let GenericArgument::Type(ty) = arg {
                        self.add_type_constraints(*ty, span, cs);
                    }
                }
            }
            TyKind::Alias { def_id, args, .. } => {
                cs.add_constraints_for_def(def_id, Some(args), span);
                let normalized = crate::sema::tycheck::utils::normalize_aliases(self.gcx(), ty);
                if normalized != ty {
                    self.add_type_constraints(normalized, span, cs);
                }
            }
            TyKind::BoxedExistential { interfaces } => {
                for iface in interfaces.iter() {
                    cs.add_constraints_for_def(iface.id, Some(iface.arguments), span);
                }
            }
            TyKind::Array { element, .. } => self.add_type_constraints(element, span, cs),
            TyKind::Tuple(items) => {
                for item in items.iter() {
                    self.add_type_constraints(*item, span, cs);
                }
            }
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                self.add_type_constraints(inner, span, cs);
            }
            TyKind::FnPointer { inputs, output } => {
                for input in inputs.iter() {
                    self.add_type_constraints(*input, span, cs);
                }
                self.add_type_constraints(output, span, cs);
            }
            _ => {}
        }
    }

    fn synth_with_needs(
        &self,
        node: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        needs: Needs,
        cs: &mut Cs<'ctx>,
    ) -> (Ty<'ctx>, bool) {
        let ty = self.synth_with_expectation(node, expectation, cs);
        let ok = match needs {
            Needs::None => true,
            Needs::MutPlace => self.require_mut_place(node, cs),
        };
        (ty, ok)
    }

    fn synth_with_expectation(
        &self,
        node: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let ty = self.synth_expression_kind(node, expectation, cs);
        cs.record_expr_ty(node.id, ty);
        // self.gcx().dcx().emit_info(
        //     format!("Checked {}", ty.format(self.gcx())),
        //     Some(node.span),
        // );
        ty
    }

    fn synth(&self, node: &hir::Expression, cs: &mut Cs<'ctx>) -> Ty<'ctx> {
        self.synth_with_expectation(node, None, cs)
    }

    fn synth_expression_kind(
        &self,
        expression: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match &expression.kind {
            hir::ExpressionKind::Literal(node) => {
                if let hir::Literal::Integer { value, .. } = node {
                    cs.record_integer_literal(expression.id, *value);
                }
                self.synth_expression_literal(node, expression.span, expectation, cs)
            }
            hir::ExpressionKind::Path(path) => {
                self.synth_path_expression(expression, path, expectation, cs)
            }
            hir::ExpressionKind::Call { callee, arguments } => {
                self.synth_call_expression(expression, callee, arguments, expectation, cs)
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                name,
                arguments,
            } => self.synth_method_call_expression(
                expression,
                receiver,
                name,
                arguments,
                expectation,
                cs,
            ),
            hir::ExpressionKind::Member { target, name } => {
                self.synth_member_expression(expression, target, name, expectation, cs)
            }
            hir::ExpressionKind::InferredMember { name } => {
                self.synth_inferred_member_expression(expression, name, expectation, cs)
            }
            hir::ExpressionKind::Array(elements) => {
                self.synth_array_expression(expression, elements, expectation, cs)
            }
            hir::ExpressionKind::Repeat { value, count } => {
                self.synth_repeat_expression(expression, value, count, expectation, cs)
            }
            hir::ExpressionKind::Tuple(elements) => {
                self.synth_tuple_expression(expression, elements, expectation, cs)
            }
            hir::ExpressionKind::If(expr) => {
                self.synth_if_expression(expression, expr, expectation, cs)
            }
            hir::ExpressionKind::Match(expr) => {
                self.synth_match_expression(expression, expr, expectation, cs)
            }
            hir::ExpressionKind::Return { value } => {
                self.check_return(value.as_deref(), expression.span, Some(cs));
                Ty::new(TyKind::Never, self.gcx())
            }
            hir::ExpressionKind::Break { .. } => {
                self.check_break(expression.span);
                Ty::new(TyKind::Never, self.gcx())
            }
            hir::ExpressionKind::Continue { .. } => {
                self.check_continue(expression.span);
                Ty::new(TyKind::Never, self.gcx())
            }
            hir::ExpressionKind::Reference(inner, mutability) => {
                let inner_ty = self.synth_with_expectation(inner, None, cs);
                if inner_ty.is_error() {
                    return Ty::error(self.gcx());
                }
                if *mutability == hir::Mutability::Mutable {
                    if !self.require_mut_borrow(inner, cs) {
                        return Ty::error(self.gcx());
                    }
                }
                Ty::new(TyKind::Reference(inner_ty, *mutability), self.gcx())
            }
            hir::ExpressionKind::Dereference(inner) => {
                let ptr_ty = self.synth_with_expectation(inner, None, cs);
                if ptr_ty.is_error() {
                    return Ty::error(self.gcx());
                }
                let result_ty = cs.infer_cx.next_ty_var(expression.span);

                cs.add_goal(
                    Goal::Deref(DerefGoalData {
                        operand_ty: ptr_ty,
                        result_ty,
                        span: expression.span,
                    }),
                    expression.span,
                );

                result_ty
            }
            hir::ExpressionKind::Binary(op, lhs, rhs) => {
                self.synth_binary_expression(expression, *op, lhs, rhs, expectation, cs)
            }
            hir::ExpressionKind::Unary(op, operand) => {
                self.synth_unary_expression(expression, *op, operand, expectation, cs)
            }
            hir::ExpressionKind::TupleAccess(receiver, index) => {
                self.synth_tuple_access_expression(expression, receiver, index, expectation, cs)
            }
            hir::ExpressionKind::AssignOp(op, lhs, rhs) => {
                self.synth_assign_op_expression(expression, *op, lhs, rhs, cs)
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                self.synth_assign_expression(expression, lhs, rhs, cs)
            }
            hir::ExpressionKind::CastAs(value, ty) => {
                self.synth_cast_expression(expression, value, ty, expectation, cs)
            }
            hir::ExpressionKind::CastAsTry(value, ty) => {
                self.synth_try_cast_expression(expression, value, ty, expectation, cs)
            }
            hir::ExpressionKind::TypeIs(value, ty) => {
                self.synth_type_is_expression(expression, value, ty, expectation, cs)
            }
            hir::ExpressionKind::PatternBinding(condition) => {
                self.synth_pattern_binding_expression(expression, condition, cs)
            }
            hir::ExpressionKind::Block(block) => {
                self.synth_block_expression(block, expectation, cs)
            }
            hir::ExpressionKind::UnsafeBlock(block) => {
                self.synth_unsafe_block_expression(block, expectation, cs)
            }
            hir::ExpressionKind::Propagate(inner) => {
                self.synth_propagate_expression(expression, inner, cs)
            }
            hir::ExpressionKind::StructLiteral(lit) => {
                self.synth_struct_literal(expression, lit, cs)
            }
            hir::ExpressionKind::Closure(closure) => {
                self.synth_closure_expression(expression, closure, expectation, cs)
            }
            hir::ExpressionKind::Await(inner) => {
                self.synth_await_expression(inner, expression.span, cs)
            }
            hir::ExpressionKind::Malformed => {
                unreachable!("ICE: trying to typecheck a malformed expression node")
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Needs {
    #[allow(unused)]
    None,
    MutPlace,
}

impl<'ctx> Checker<'ctx> {
    fn synth_cast_expression(
        &self,
        expression: &hir::Expression,
        value: &hir::Expression,
        target: &hir::Type,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let target_ty = self.lower_type(target);
        self.add_type_constraints(target_ty, target.span, cs);
        let value_ty = self.synth(value, cs);

        if target_ty.is_error() || value_ty.is_error() {
            return Ty::error(self.gcx());
        }

        let is_unsafe = self.unsafe_depth.get() > 0;
        cs.add_goal(
            Goal::Cast {
                node_id: expression.id,
                from: value_ty,
                to: target_ty,
                is_unsafe,
            },
            expression.span,
        );

        if let Some(expectation) = expectation {
            cs.add_goal(
                Goal::ConstraintEqual(expectation, target_ty),
                expression.span,
            );
        }

        target_ty
    }

    fn synth_try_cast_expression(
        &self,
        expression: &hir::Expression,
        value: &hir::Expression,
        target: &hir::Type,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let target_ty = self.lower_type(target);
        self.add_type_constraints(target_ty, target.span, cs);
        let value_ty = self.synth(value, cs);

        if target_ty.is_error() || value_ty.is_error() {
            return Ty::error(gcx);
        }

        let (optional_ty, _) = self.mk_optional_type(target_ty);
        if let Some(expectation) = expectation {
            cs.add_goal(
                Goal::ConstraintEqual(expectation, optional_ty),
                expression.span,
            );
        }
        optional_ty
    }

    fn synth_type_is_expression(
        &self,
        expression: &hir::Expression,
        value: &hir::Expression,
        target: &hir::Type,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let target_ty = self.lower_type(target);
        self.add_type_constraints(target_ty, target.span, cs);
        let value_ty = self.synth(value, cs);

        if target_ty.is_error() || value_ty.is_error() {
            return Ty::error(gcx);
        }

        if let Some(expectation) = expectation {
            cs.add_goal(
                Goal::ConstraintEqual(expectation, gcx.types.bool),
                expression.span,
            );
        }

        gcx.types.bool
    }

    fn lookup_member_property_on_base_ty(
        &self,
        base_ty: Ty<'ctx>,
        name: Symbol,
    ) -> Option<crate::compile::context::ComputedPropertyEntry<'ctx>> {
        let head = type_head_from_value_ty(base_ty)?;
        let mut property = self.gcx().lookup_computed_property(head, name)?;
        if !self
            .gcx()
            .is_visibility_allowed(property.visibility, self.current_def)
        {
            return None;
        }

        if let TyKind::Adt(_, args) = base_ty.kind()
            && !args.is_empty()
            && property.ty.needs_instantiation()
        {
            property.ty = instantiate_ty_with_args(self.gcx(), property.ty, args);
        }

        Some(property)
    }

    fn mutable_binding_for_resolution(&self, resolution: &hir::Resolution) -> Option<bool> {
        match resolution {
            hir::Resolution::LocalVariable(id) => Some(self.get_local(*id).mutable),
            hir::Resolution::Definition(id, DefinitionKind::ModuleVariable) => self
                .gcx()
                .try_get_static_mutability(*id)
                .map(|m| m == hir::Mutability::Mutable),
            _ => None,
        }
    }

    fn require_mut_place(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                match &path.resolution {
                    hir::Resolution::LocalVariable(_)
                    | hir::Resolution::Definition(_, DefinitionKind::ModuleVariable) => {
                        let mutable = self
                            .mutable_binding_for_resolution(&path.resolution)
                            .unwrap_or(false);
                        if !mutable {
                            let message = if matches!(
                                &path.resolution,
                                hir::Resolution::Definition(_, DefinitionKind::ModuleVariable)
                            ) {
                                "cannot assign to an immutable static variable"
                            } else {
                                "cannot assign to an immutable binding"
                            };
                            self.gcx().dcx().emit_error(message.into(), Some(expr.span));
                        }
                        true
                    }
                    _ => {
                        self.gcx().dcx().emit_error(
                            "left-hand side of assignment is not assignable".into(),
                            Some(expr.span),
                        );
                        false
                    }
                }
            }
            hir::ExpressionKind::Dereference(inner) => {
                let Some(ptr_ty) = cs.expr_ty(inner.id) else {
                    self.gcx()
                        .dcx()
                        .emit_error("missing type for deref operand".into(), Some(expr.span));
                    return false;
                };

                let ptr_ty = cs.infer_cx.resolve_vars_if_possible(ptr_ty);
                if ptr_ty.contains_inference() {
                    return true;
                }
                match ptr_ty.kind() {
                    TyKind::Pointer(_, mutbl) | TyKind::Reference(_, mutbl) => {
                        if mutbl != hir::Mutability::Mutable {
                            self.gcx().dcx().emit_error(
                                "cannot assign through an immutable pointer/reference".into(),
                                Some(expr.span),
                            );
                        }
                        true
                    }
                    _ => {
                        self.gcx().dcx().emit_error(
                            format!(
                                "cannot assign through a non-pointer/reference value type {}",
                                ptr_ty.format(self.gcx())
                            ),
                            Some(expr.span),
                        );
                        false
                    }
                }
            }
            hir::ExpressionKind::Member { target, name } => {
                let Some(receiver_ty) = cs.expr_ty(target.id) else {
                    self.gcx()
                        .dcx()
                        .emit_error("missing type for member receiver".into(), Some(expr.span));
                    return false;
                };

                // Mutability through pointer/reference.
                let receiver_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
                if receiver_ty.contains_inference() {
                    return true;
                }
                let (base_ty, via_ptr_mut) = match receiver_ty.kind() {
                    TyKind::Pointer(inner, mutbl) | TyKind::Reference(inner, mutbl) => {
                        (inner, mutbl == hir::Mutability::Mutable)
                    }
                    _ => (receiver_ty, true),
                };

                if !via_ptr_mut {
                    self.gcx().dcx().emit_error(
                        "cannot assign through an immutable pointer/reference".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                // Ensure the receiver expression is an assignable place (e.g. `self`, local var).
                let receiver_is_place = match &target.kind {
                    hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                        if matches!(
                            &path.resolution,
                            hir::Resolution::LocalVariable(_)
                                | hir::Resolution::Definition(_, DefinitionKind::ModuleVariable)
                        ) =>
                    {
                        let binding_mutable = self
                            .mutable_binding_for_resolution(&path.resolution)
                            .unwrap_or(false);
                        if !binding_mutable && !via_ptr_mut {
                            let message = if matches!(
                                &path.resolution,
                                hir::Resolution::Definition(_, DefinitionKind::ModuleVariable)
                            ) {
                                "cannot assign through an immutable static variable"
                            } else {
                                "cannot assign through an immutable binding"
                            };
                            self.gcx()
                                .dcx()
                                .emit_error(message.into(), Some(target.span));
                            false
                        } else {
                            true
                        }
                    }
                    hir::ExpressionKind::Dereference(_) => true,
                    _ => {
                        self.gcx().dcx().emit_error(
                            "left-hand side of assignment is not assignable".into(),
                            Some(expr.span),
                        );
                        false
                    }
                };

                if !receiver_is_place {
                    return false;
                }

                if let TyKind::Adt(def, args) = base_ty.kind()
                    && self.gcx().definition_kind(def.id) == DefinitionKind::Struct
                {
                    let struct_def = self.gcx().get_struct_definition(def.id);
                    let struct_def = crate::sema::tycheck::utils::instantiate::
                        instantiate_struct_definition_with_args(self.gcx(), struct_def, args);
                    if let Some(field) = struct_def.fields.iter().find(|field| field.name == name.symbol)
                    {
                        if field.mutability != hir::Mutability::Mutable {
                            self.gcx().dcx().emit_error(
                                "cannot assign to an immutable field".into(),
                                Some(expr.span),
                            );
                            return false;
                        }
                        return true;
                    }
                }

                if let Some(property) = self.lookup_member_property_on_base_ty(base_ty, name.symbol)
                {
                    if property.setter_id.is_none() {
                        self.gcx()
                            .dcx()
                            .emit_error("cannot assign to a read-only property".into(), Some(expr.span));
                        return false;
                    }
                    return true;
                }

                self.gcx().dcx().emit_error(
                    format!("unknown field '{}'", self.gcx().symbol_text(name.symbol)),
                    Some(expr.span),
                );
                false
            }
            hir::ExpressionKind::TupleAccess(target, _) => {
                let Some(receiver_ty) = cs.expr_ty(target.id) else {
                    return false;
                };

                match cs.infer_cx.resolve_vars_if_possible(receiver_ty).kind() {
                    TyKind::Pointer(_, mutbl) | TyKind::Reference(_, mutbl) => {
                        mutbl == hir::Mutability::Mutable
                    }
                    _ => self.require_mut_place(target, cs),
                }
            }
            _ => {
                if let Some(ty) = cs.expr_ty(expr.id) {
                    if ty.is_error() {
                        return true;
                    }
                }
                self.gcx().dcx().emit_error(
                    "left-hand side of assignment is not assignable".into(),
                    Some(expr.span),
                );
                false
            }
        }
    }

    fn can_mutably_borrow_receiver(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        if let Some(expr_ty) = cs.expr_ty(expr.id) {
            let expr_ty = cs.infer_cx.resolve_vars_if_possible(expr_ty);
            match expr_ty.kind() {
                TyKind::Error => return true,
                TyKind::Pointer(_, hir::Mutability::Mutable)
                | TyKind::Reference(_, hir::Mutability::Mutable) => return true,
                _ => {}
            }
        }

        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                match &path.resolution {
                    hir::Resolution::LocalVariable(_)
                    | hir::Resolution::Definition(_, DefinitionKind::ModuleVariable) => {
                        if matches!(
                            &path.resolution,
                            hir::Resolution::LocalVariable(id) if self.get_local(*id).ty.is_error()
                        ) {
                            return true;
                        }
                        self.mutable_binding_for_resolution(&path.resolution)
                            .unwrap_or(false)
                    }
                    _ => false,
                }
            }
            hir::ExpressionKind::Dereference(inner) => {
                let Some(ptr_ty) = cs.expr_ty(inner.id) else {
                    return false;
                };

                let ptr_ty = cs.infer_cx.resolve_vars_if_possible(ptr_ty);
                if ptr_ty.contains_inference() {
                    return true;
                }

                match ptr_ty.kind() {
                    TyKind::Error => true,
                    TyKind::Pointer(_, mutbl) | TyKind::Reference(_, mutbl) => {
                        mutbl == hir::Mutability::Mutable
                    }
                    _ => false,
                }
            }
            hir::ExpressionKind::Member { target, name } => {
                let Some(receiver_ty) = cs.expr_ty(target.id) else {
                    return false;
                };

                let receiver_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
                if receiver_ty.contains_inference() {
                    return true;
                }

                let base_ty = match receiver_ty.kind() {
                    TyKind::Error => return true,
                    TyKind::Pointer(inner, mutbl) | TyKind::Reference(inner, mutbl) => {
                        if mutbl != hir::Mutability::Mutable {
                            return false;
                        }
                        inner
                    }
                    _ => {
                        if !self.can_mutably_borrow_receiver(target, cs) {
                            return false;
                        }
                        receiver_ty
                    }
                };

                if let TyKind::Adt(def, args) = base_ty.kind()
                    && self.gcx().definition_kind(def.id) == DefinitionKind::Struct
                {
                    let struct_def = self.gcx().get_struct_definition(def.id);
                    let struct_def = crate::sema::tycheck::utils::instantiate::
                        instantiate_struct_definition_with_args(self.gcx(), struct_def, args);
                    if struct_def
                        .fields
                        .iter()
                        .any(|field| field.name == name.symbol)
                    {
                        return true;
                    }
                }

                if self
                    .lookup_member_property_on_base_ty(base_ty, name.symbol)
                    .is_some()
                {
                    return false;
                }

                false
            }
            hir::ExpressionKind::TupleAccess(target, _) => {
                let Some(receiver_ty) = cs.expr_ty(target.id) else {
                    return false;
                };

                let receiver_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
                if receiver_ty.contains_inference() {
                    return true;
                }

                match receiver_ty.kind() {
                    TyKind::Error => true,
                    TyKind::Pointer(_, mutbl) | TyKind::Reference(_, mutbl) => {
                        mutbl == hir::Mutability::Mutable
                    }
                    _ => self.can_mutably_borrow_receiver(target, cs),
                }
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                name,
                arguments,
            } => {
                let Some(receiver_ty) = cs.expr_ty(receiver.id) else {
                    return false;
                };

                self.can_mutably_borrow_receiver(receiver, cs)
                    && self.method_call_can_yield_mutable_reference(
                        receiver_ty,
                        name,
                        arguments.len(),
                        cs,
                    )
            }
            _ => false,
        }
    }

    fn require_mut_borrow(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                if let hir::Resolution::LocalVariable(_)
                | hir::Resolution::Definition(_, DefinitionKind::ModuleVariable) =
                    &path.resolution
                {
                    if matches!(&path.resolution, hir::Resolution::LocalVariable(id) if self.get_local(*id).ty.is_error())
                    {
                        return true;
                    }
                    let mutable = self
                        .mutable_binding_for_resolution(&path.resolution)
                        .unwrap_or(false);
                    if !mutable {
                        let message = if matches!(
                            &path.resolution,
                            hir::Resolution::Definition(_, DefinitionKind::ModuleVariable)
                        ) {
                            "cannot take a mutable reference to an immutable static variable"
                        } else {
                            "cannot take a mutable reference to an immutable binding"
                        };
                        self.gcx().dcx().emit_error(message.into(), Some(expr.span));
                        return false;
                    }
                }
                true
            }
            hir::ExpressionKind::Dereference(inner) => {
                let Some(ptr_ty) = cs.expr_ty(inner.id) else {
                    self.gcx()
                        .dcx()
                        .emit_error("missing type for deref operand".into(), Some(expr.span));
                    return false;
                };

                let ptr_ty = cs.infer_cx.resolve_vars_if_possible(ptr_ty);
                if ptr_ty.contains_inference() {
                    return true;
                }
                match ptr_ty.kind() {
                    TyKind::Error => true,
                    TyKind::Pointer(_, mutbl) | TyKind::Reference(_, mutbl) => {
                        if mutbl != hir::Mutability::Mutable {
                            self.gcx().dcx().emit_error(
                                "cannot borrow through an immutable pointer/reference".into(),
                                Some(expr.span),
                            );
                        }
                        true
                    }
                    _ => {
                        self.gcx().dcx().emit_error(
                            "cannot borrow through a non-pointer/reference value".into(),
                            Some(expr.span),
                        );
                        false
                    }
                }
            }
            hir::ExpressionKind::Member { target, name } => {
                let Some(receiver_ty) = cs.expr_ty(target.id) else {
                    self.gcx()
                        .dcx()
                        .emit_error("missing type for member receiver".into(), Some(expr.span));
                    return false;
                };

                let receiver_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
                if receiver_ty.contains_inference() {
                    return true;
                }

                let (base_ty, via_ptr_mut, via_ptr) =
                    if let hir::ExpressionKind::Dereference(inner) = &target.kind {
                        let Some(ptr_ty) = cs.expr_ty(inner.id) else {
                            self.gcx().dcx().emit_error(
                                "missing type for deref operand".into(),
                                Some(expr.span),
                            );
                            return false;
                        };

                        let ptr_ty = cs.infer_cx.resolve_vars_if_possible(ptr_ty);
                        if ptr_ty.contains_inference() {
                            return true;
                        }

                        match ptr_ty.kind() {
                            TyKind::Error => return true,
                            TyKind::Pointer(inner, mutbl) | TyKind::Reference(inner, mutbl) => {
                                (inner, mutbl == hir::Mutability::Mutable, true)
                            }
                            _ => {
                                self.gcx().dcx().emit_error(
                                    "cannot borrow through a non-pointer/reference value".into(),
                                    Some(expr.span),
                                );
                                return false;
                            }
                        }
                    } else {
                        match receiver_ty.kind() {
                            TyKind::Error => return true,
                            TyKind::Pointer(inner, mutbl) | TyKind::Reference(inner, mutbl) => {
                                (inner, mutbl == hir::Mutability::Mutable, true)
                            }
                            _ => (receiver_ty, true, false),
                        }
                    };

                if !via_ptr_mut {
                    self.gcx().dcx().emit_error(
                        "cannot borrow through an immutable pointer/reference".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                if !via_ptr {
                    if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) =
                        &target.kind
                    {
                        if matches!(
                            &path.resolution,
                            hir::Resolution::LocalVariable(_)
                                | hir::Resolution::Definition(_, DefinitionKind::ModuleVariable)
                        ) {
                            let mutable = self
                                .mutable_binding_for_resolution(&path.resolution)
                                .unwrap_or(false);
                            if !mutable {
                                let message = if matches!(
                                    &path.resolution,
                                    hir::Resolution::Definition(_, DefinitionKind::ModuleVariable)
                                ) {
                                    "cannot take a mutable reference to an immutable static variable"
                                } else {
                                    "cannot take a mutable reference to an immutable binding"
                                };
                                self.gcx()
                                    .dcx()
                                    .emit_error(message.into(), Some(target.span));
                                return false;
                            }
                        }
                    }
                }

                if let TyKind::Adt(def, args) = base_ty.kind()
                    && self.gcx().definition_kind(def.id) == DefinitionKind::Struct
                {
                    let struct_def = self.gcx().get_struct_definition(def.id);
                    let struct_def = crate::sema::tycheck::utils::instantiate::
                        instantiate_struct_definition_with_args(self.gcx(), struct_def, args);
                    if let Some(field) = struct_def.fields.iter().find(|field| field.name == name.symbol)
                    {
                        if field.mutability != hir::Mutability::Mutable {
                            self.gcx().dcx().emit_error(
                                "cannot take a mutable reference to an immutable field".into(),
                                Some(expr.span),
                            );
                            return false;
                        }
                        return true;
                    }
                }

                if self
                    .lookup_member_property_on_base_ty(base_ty, name.symbol)
                    .is_some()
                {
                    self.gcx().dcx().emit_error(
                        "cannot take a mutable reference to a computed property".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                if matches!(base_ty.kind(), TyKind::Adt(def, _) if self.gcx().definition_kind(def.id) == DefinitionKind::Struct)
                {
                    self.gcx().dcx().emit_error(
                        format!("unknown field '{}'", self.gcx().symbol_text(name.symbol)),
                        Some(expr.span),
                    );
                    return false;
                }

                self.gcx().dcx().emit_error(
                    "cannot borrow a member of a non-struct value".into(),
                    Some(expr.span),
                );
                false
            }
            hir::ExpressionKind::TupleAccess(target, _) => {
                let Some(receiver_ty) = cs.expr_ty(target.id) else {
                    return false;
                };

                match receiver_ty.kind() {
                    TyKind::Error => true,
                    TyKind::Pointer(_, mutbl) | TyKind::Reference(_, mutbl) => {
                        if mutbl != hir::Mutability::Mutable {
                            self.gcx().dcx().emit_error(
                                "cannot borrow through an immutable pointer/reference".into(),
                                Some(expr.span),
                            );
                        }
                        true
                    }
                    _ => {
                        if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) =
                            &target.kind
                        {
                            if matches!(
                                &path.resolution,
                                hir::Resolution::LocalVariable(_)
                                    | hir::Resolution::Definition(
                                        _,
                                        DefinitionKind::ModuleVariable
                                    )
                            ) {
                                let mutable = self
                                    .mutable_binding_for_resolution(&path.resolution)
                                    .unwrap_or(false);
                                if !mutable {
                                    let message = if matches!(
                                        &path.resolution,
                                        hir::Resolution::Definition(
                                            _,
                                            DefinitionKind::ModuleVariable
                                        )
                                    ) {
                                        "cannot take a mutable reference to an immutable static variable"
                                    } else {
                                        "cannot take a mutable reference to an immutable binding"
                                    };
                                    self.gcx()
                                        .dcx()
                                        .emit_error(message.into(), Some(target.span));
                                    return false;
                                }
                            }
                        }
                        true
                    }
                }
            }
            _ => true,
        }
    }

    fn synth_assign_expression(
        &self,
        expr: &hir::Expression,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Type-check the LHS as an expression, then require it be a mutable place.
        let (lhs_ty, ok) = self.synth_with_needs(lhs, None, Needs::MutPlace, cs);
        if !ok {
            return Ty::error(self.gcx());
        }

        // Type-check the RHS against the LHS type.
        let rhs_ty = self.synth_with_expectation(rhs, Some(lhs_ty), cs);
        if lhs_ty.is_error() || rhs_ty.is_error() {
            return Ty::error(self.gcx());
        }

        if let hir::ExpressionKind::Member { target, name } = &lhs.kind
            && let Some(receiver_ty) = cs.expr_ty(target.id)
        {
            let receiver_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
            let base_ty = match receiver_ty.kind() {
                TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => inner,
                _ => receiver_ty,
            };

            if let Some(property) = self.lookup_member_property_on_base_ty(base_ty, name.symbol)
                && let Some(setter_id) = property.setter_id
            {
                cs.record_property_write(
                    expr.id,
                    crate::sema::tycheck::solve::ResolvedPropertyWrite {
                        property_id: property.property_id,
                        setter_id,
                        ty: property.ty,
                    },
                );
            }
        }

        cs.add_goal(
            crate::sema::tycheck::solve::Goal::Coerce {
                node_id: rhs.id,
                from: rhs_ty,
                to: lhs_ty,
            },
            expr.span,
        );
        // Assignments evaluate to unit.
        self.gcx().types.void
    }

    fn synth_block_expression(
        &self,
        block: &hir::Block,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        for stmt in &block.statements {
            self.check_statement(stmt, Some(cs));
        }

        if let Some(tail) = block.tail.as_deref() {
            self.synth_with_expectation(tail, expectation, cs)
        } else {
            self.gcx().types.void
        }
    }

    fn synth_closure_expression(
        &self,
        expression: &hir::Expression,
        closure: &hir::ClosureExpr,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let effective_async = closure.is_async || self.is_forced_async_closure_expr(expression.id);

        // Collect closure parameter IDs (these are NOT captures)
        let param_ids: rustc_hash::FxHashSet<NodeID> =
            closure.params.iter().map(|p| p.id).collect();

        // Extract expected input/output types from the expectation (for type inference)
        let expected_inputs =
            expectation.and_then(|ty| self.extract_closure_expected_inputs(ty, cs));
        let expected_output =
            expectation.and_then(|ty| self.extract_closure_expected_output(ty, cs));

        // Collect parameter types
        let mut param_tys = Vec::with_capacity(closure.params.len());

        for (index, param) in closure.params.iter().enumerate() {
            // Check if there's an explicit type annotation (not an inferred placeholder)
            let has_explicit_type = param
                .ty
                .as_ref()
                .map_or(false, |ty| !matches!(ty.kind, hir::TypeKind::Infer));

            // Use explicit type annotation, or infer from expectation, or create infer var
            let param_ty = if has_explicit_type {
                // Explicit type annotation - lower it
                let explicit_ty = self.lower_type(param.ty.as_ref().unwrap());
                if let Some(ref inputs) = expected_inputs {
                    if let Some(&expected_ty) = inputs.get(index) {
                        cs.equal(expected_ty, explicit_ty, param.span);
                    }
                }
                explicit_ty
            } else if let Some(ref inputs) = expected_inputs {
                // Infer from expected type (e.g., from Fn bound)
                if let Some(&expected_ty) = inputs.get(index) {
                    expected_ty
                } else {
                    // More params than expected - create infer var
                    cs.infer_cx.next_ty_var(param.span)
                }
            } else {
                // No expectation available - create inference variable
                cs.infer_cx.next_ty_var(param.span)
            };

            param_tys.push(param_ty);

            // Register the parameter as a local binding
            self.set_local(
                param.id,
                super::checker::LocalBinding {
                    mutable: false,
                    ty: param_ty,
                },
            );
        }

        let expected_return = if let Some(ret_ty) = &closure.return_ty {
            self.lower_type(ret_ty)
        } else if let Some(expected_return) = expected_output {
            expected_return
        } else {
            cs.infer_cx.next_ty_var(closure.body.span)
        };

        // Type check the closure body under the closure's own return context so
        // explicit `return expr` participates in the same output inference as a
        // tail expression.
        let (return_ty, body_ty) = self.with_return_ty(Some(expected_return), || {
            let prev_async_depth = self.async_depth.get();
            if effective_async {
                self.async_depth.set(prev_async_depth + 1);
            }

            let body_ty = match &closure.body.kind {
                hir::ExpressionKind::Block(block) | hir::ExpressionKind::UnsafeBlock(block) => {
                    for statement in &block.statements {
                        self.check_statement(statement, Some(cs));
                    }

                    if let Some(tail) = block.tail.as_deref() {
                        if matches!(tail.kind, hir::ExpressionKind::Return { .. }) {
                            self.synth_with_expectation(tail, None, cs)
                        } else {
                            let actual_return =
                                self.synth_with_expectation(tail, Some(expected_return), cs);
                            let resolved_actual =
                                cs.infer_cx.resolve_vars_if_possible(actual_return);
                            let resolved_expected =
                                cs.infer_cx.resolve_vars_if_possible(expected_return);
                            if matches!(resolved_actual.kind(), TyKind::Never)
                                && resolved_expected.is_infer()
                            {
                                cs.equal(expected_return, actual_return, tail.span);
                            } else {
                                cs.add_goal(
                                    Goal::Coerce {
                                        node_id: tail.id,
                                        from: actual_return,
                                        to: expected_return,
                                    },
                                    tail.span,
                                );
                            }
                            actual_return
                        }
                    } else if !closure_body_has_explicit_return(&closure.body) {
                        cs.equal(expected_return, self.gcx().types.void, closure.body.span);
                        self.gcx().types.void
                    } else {
                        self.gcx().types.void
                    }
                }
                hir::ExpressionKind::Return { .. } => {
                    self.synth_with_expectation(&closure.body, None, cs)
                }
                _ => {
                    let actual_return =
                        self.synth_with_expectation(&closure.body, Some(expected_return), cs);
                    let resolved_actual = cs.infer_cx.resolve_vars_if_possible(actual_return);
                    let resolved_expected = cs.infer_cx.resolve_vars_if_possible(expected_return);
                    if matches!(resolved_actual.kind(), TyKind::Never)
                        && resolved_expected.is_infer()
                    {
                        cs.equal(expected_return, actual_return, closure.body.span);
                    } else {
                        cs.add_goal(
                            Goal::Coerce {
                                node_id: closure.body.id,
                                from: actual_return,
                                to: expected_return,
                            },
                            closure.body.span,
                        );
                    }
                    actual_return
                }
            };

            if effective_async {
                self.async_depth.set(prev_async_depth);
            }

            (expected_return, body_ty)
        });
        cs.record_expr_ty(closure.body.id, body_ty);

        // Resolve what we can so we don't cache infer vars in closure signatures.
        cs.solve_intermediate();
        let adjustments = cs.resolved_adjustments();
        let return_ty = cs.infer_cx.resolve_vars_if_possible(return_ty);
        let param_tys: Vec<_> = param_tys
            .into_iter()
            .map(|ty| cs.infer_cx.resolve_vars_if_possible(ty))
            .collect();

        // Perform capture analysis - collect free variables from the closure body
        let mut collector = CaptureCollector {
            param_ids: &param_ids,
            local_decls: rustc_hash::FxHashSet::default(),
            order: Vec::new(),
            info: rustc_hash::FxHashMap::default(),
            checker: self,
            adjustments: &adjustments,
        };
        collector.collect_expr(&closure.body, UseContext::Value);

        // Build capture list with types and capture kinds
        let mut captures = Vec::new();
        for (field_index, node_id) in collector.order.iter().enumerate() {
            if param_ids.contains(node_id) {
                continue;
            }
            let info = collector
                .info
                .get(node_id)
                .expect("capture info should exist");
            // Get the type of the captured variable from local bindings
            let binding = self.get_local(*node_id);
            let ty = cs.infer_cx.resolve_vars_if_possible(binding.ty);
            let capture_kind = classify_capture_kind(gcx, self.current_def, ty, info.usage);

            captures.push(crate::sema::models::CapturedVar {
                source_id: *node_id,
                name: info.name,
                ty,
                capture_kind,
                field_index: crate::thir::FieldIndex::from_raw(field_index as u32),
            });
        }

        let closure_kind = infer_closure_kind(effective_async, &captures);

        gcx.cache_closure_captures(
            closure.def_id,
            crate::sema::models::ClosureCaptures {
                captures: captures.clone(),
                kind: closure_kind,
            },
        );

        // Create the closure type (with user-visible parameter types only)
        let inputs = gcx.store.interners.intern_ty_list(param_tys.clone());
        let captured_generics = GenericsBuilder::identity_for_item(gcx, self.current_def);

        // Create the closure type first (we need it for the body function signature)
        let closure_ty = Ty::new(
            TyKind::Closure {
                closure_def_id: closure.def_id,
                kind: closure_kind,
                captured_generics,
                inputs,
                output: return_ty,
            },
            gcx,
        );
        if effective_async {
            gcx.cache_async_body_output(closure.def_id, return_ty);
        }

        let self_ty = closure_self_ty(gcx, closure_ty, closure_kind);

        let mut sig_inputs = vec![crate::sema::models::LabeledFunctionParameter {
            label: None,
            name: gcx.intern_symbol("self"),
            ty: self_ty,
            default_provider: None,
        }];

        // Add the explicit closure parameters after self
        sig_inputs.extend(
            closure
                .params
                .iter()
                .zip(param_tys.iter())
                .map(|(param, &ty)| {
                    let name = match &param.pattern.kind {
                        hir::PatternKind::Binding { name, .. } => name.symbol,
                        _ => gcx.intern_symbol("_"),
                    };
                    crate::sema::models::LabeledFunctionParameter {
                        label: None,
                        name,
                        ty,
                        default_provider: None,
                    }
                }),
        );

        gcx.cache_signature(
            closure.def_id,
            crate::sema::models::LabeledFunctionSignature {
                inputs: sig_inputs,
                output: return_ty,
                is_variadic: false,
                abi: None,
            },
        );

        closure_ty
    }
}

impl<'ctx> Checker<'ctx> {
    fn synth_unsafe_block_expression(
        &self,
        block: &hir::Block,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let prev = self.unsafe_depth.get();
        self.unsafe_depth.set(prev + 1);
        let ty = self.synth_block_expression(block, expectation, cs);
        self.unsafe_depth.set(prev);
        ty
    }

    /// `await expr` — verify expr is a direct async call, then return its ready type.
    fn synth_await_expression(
        &self,
        inner: &hir::Expression,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        if matches!(inner.kind, hir::ExpressionKind::Propagate(_)) {
            gcx.dcx().emit_error(
                "use `(await expr)!` to propagate an awaited Optional or Result".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        if self.defer_depth.get() > 0 {
            gcx.dcx().emit_error(
                "`await` is not allowed inside a defer block".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        // await is only valid inside an async context
        if self.async_depth.get() == 0 {
            gcx.dcx().emit_error(
                "`await` can only be used inside an `async` function".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        let future_ty = self.with_direct_await_operand(inner.id, || self.synth(inner, cs));
        if future_ty.is_error() {
            return Ty::error(gcx);
        }
        cs.solve_intermediate();
        let future_ty = cs.infer_cx.resolve_vars_if_possible(future_ty);

        if self.results.borrow().is_async_call(inner.id) {
            return future_ty;
        }

        if matches!(
            self.resolved_async_call_status(inner.id, Some(cs)),
            Some(true)
        ) {
            return future_ty;
        }

        if self.task_inner_type(future_ty).is_some() {
            gcx.dcx().emit_error(
                "use `await task.result()` to await a `Task[T]`".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        gcx.dcx()
            .emit_error("`await` expects an async call".into(), Some(span));
        Ty::error(gcx)
    }

    fn synth_propagate_expression(
        &self,
        expression: &hir::Expression,
        inner: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        if self.defer_depth.get() > 0 {
            gcx.dcx().emit_error(
                "`!` is not allowed inside a defer block".into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        }

        let operand_ty = self.synth(inner, cs);
        if operand_ty.is_error() {
            return Ty::error(gcx);
        }
        cs.solve_intermediate();

        let operand_ty = cs.infer_cx.resolve_vars_if_possible(operand_ty);
        let Some(return_ty) = self.return_ty.get() else {
            gcx.dcx().emit_error(
                "postfix `!` requires an enclosing Optional or Result return type".into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        };
        let return_ty = cs.infer_cx.resolve_vars_if_possible(return_ty);

        if let Some((_, inner_ty)) = self.optional_inner_type(operand_ty) {
            if self.is_optional_type(return_ty) {
                return inner_ty;
            }

            gcx.dcx().emit_error(
                format!(
                    "Optional propagation requires an enclosing Optional return type, found '{}'",
                    return_ty.format(gcx)
                )
                .into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        }

        if let Some((_, ok_ty, err_ty)) = self.result_inner_types(operand_ty) {
            let Some((_, _, return_err_ty)) = self.result_inner_types(return_ty) else {
                gcx.dcx().emit_error(
                    format!(
                        "Result propagation requires an enclosing Result return type, found '{}'",
                        return_ty.format(gcx)
                    )
                    .into(),
                    Some(expression.span),
                );
                return Ty::error(gcx);
            };

            let resolved_return_err = cs.infer_cx.resolve_vars_if_possible(return_err_ty);
            let resolved_operand_err = cs.infer_cx.resolve_vars_if_possible(err_ty);
            if !resolved_return_err.is_infer()
                && !resolved_operand_err.is_infer()
                && resolved_return_err != resolved_operand_err
            {
                gcx.dcx().emit_error(
                    format!(
                        "Result propagation requires matching error types, found '{}' and '{}'",
                        resolved_operand_err.format(gcx),
                        resolved_return_err.format(gcx)
                    )
                    .into(),
                    Some(expression.span),
                );
                return Ty::error(gcx);
            }

            cs.equal(return_err_ty, err_ty, expression.span);
            return ok_ty;
        }

        gcx.dcx().emit_error(
            format!(
                "postfix `!` requires an Optional or Result value, found '{}'",
                operand_ty.format(gcx)
            )
            .into(),
            Some(inner.span),
        );
        Ty::error(gcx)
    }

    fn synth_expression_literal(
        &self,
        literal: &hir::Literal,
        span: Span,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        match literal {
            hir::Literal::Bool(_) => gcx.types.bool,
            hir::Literal::Rune(_) => gcx.types.rune,
            hir::Literal::String(_) => gcx.types.string,
            hir::Literal::Integer { value, suffix } => {
                if let Some(suffix) = suffix {
                    let ty = match suffix {
                        crate::parse::IntegerTypeSuffix::I8 => gcx.types.int8,
                        crate::parse::IntegerTypeSuffix::I16 => gcx.types.int16,
                        crate::parse::IntegerTypeSuffix::I32 => gcx.types.int32,
                        crate::parse::IntegerTypeSuffix::I64 => gcx.types.int64,
                        crate::parse::IntegerTypeSuffix::U8 => gcx.types.uint8,
                        crate::parse::IntegerTypeSuffix::U16 => gcx.types.uint16,
                        crate::parse::IntegerTypeSuffix::U32 => gcx.types.uint32,
                        crate::parse::IntegerTypeSuffix::U64 => gcx.types.uint64,
                    };

                    if !integer_literal_fits(*value, ty) {
                        gcx.dcx().emit_error(
                            format!(
                                "integer literal '{}' is out of range for type '{}'",
                                value,
                                ty.format(gcx)
                            )
                            .into(),
                            Some(span),
                        );
                        return Ty::error(gcx);
                    }

                    return ty;
                }

                let opt_ty = expectation.and_then(|ty| match ty.kind() {
                    TyKind::Int(_) | TyKind::UInt(_) => Some(ty),
                    _ => None,
                });

                if let Some(ty) = opt_ty {
                    if !integer_literal_fits(*value, ty) {
                        gcx.dcx().emit_error(
                            format!(
                                "integer literal '{}' is out of range for type '{}'",
                                value,
                                ty.format(gcx)
                            )
                            .into(),
                            Some(span),
                        );
                        return Ty::error(gcx);
                    }
                    ty
                } else {
                    cs.infer_cx.next_int_var()
                }
            }
            hir::Literal::Float(_) => {
                let opt_ty = expectation.and_then(|ty| match ty.kind() {
                    TyKind::Float(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| cs.infer_cx.next_float_var())
            }
            hir::Literal::Nil => cs.infer_cx.next_nil_var(),
        }
    }

    fn synth_identifier_expression(
        &self,
        node_id: NodeID,
        span: Span,
        resolution: &hir::Resolution,
        expectation: Option<Ty<'ctx>>,
        instantiation_args: Option<GenericArguments<'ctx>>,
        allow_unsafe_callable_values: bool,
        prefer_async: Option<bool>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match resolution {
            hir::Resolution::LocalVariable(id) => self.get_local(*id).ty,
            hir::Resolution::Definition(id, kind) => {
                if !self.gcx().is_definition_visible(*id, self.current_def) {
                    let name = self.gcx().definition_ident(*id).symbol;
                    self.gcx()
                        .dcx()
                        .emit_error(format!("'{}' is not visible here", name).into(), Some(span));
                    return Ty::error(self.gcx());
                }
                match kind {
                    DefinitionKind::Struct => {
                        let Some(nominal) = self.constructor_nominal_from_resolution(resolution)
                        else {
                            return Ty::error(self.gcx());
                        };
                        self.synth_constructor_value_expression(
                            node_id,
                            nominal,
                            span,
                            expectation,
                            instantiation_args,
                            cs,
                        )
                    }
                    DefinitionKind::ConstParameter => {
                        let Some(owner) = self.gcx().definition_parent(*id) else {
                            return Ty::error(self.gcx());
                        };
                        if let Some(ty) = self.gcx().try_generic_const_param_ty(*id) {
                            return ty;
                        }
                        let generics = self.gcx().generics_of(owner);
                        let Some(param) = generics.parameters.iter().find(|p| p.id == *id) else {
                            return Ty::error(self.gcx());
                        };
                        match &param.kind {
                            GenericParameterDefinitionKind::Const { ty, .. } => self.lower_type(ty),
                            _ => Ty::error(self.gcx()),
                        }
                    }
                    _ => {
                        if !allow_unsafe_callable_values
                            && self.is_unsafe_callable_definition(*id)
                            && matches!(
                                kind,
                                DefinitionKind::Function
                                    | DefinitionKind::AssociatedFunction
                                    | DefinitionKind::AssociatedOperator
                            )
                        {
                            return self.emit_unsafe_callable_value_error(*id, span);
                        }
                        self.gcx().get_type(*id)
                    }
                }
            }
            hir::Resolution::SelfConstructor(..) => {
                let Some(nominal) = self.constructor_nominal_from_resolution(resolution) else {
                    return Ty::error(self.gcx());
                };
                self.synth_constructor_value_expression(
                    node_id,
                    nominal,
                    span,
                    expectation,
                    instantiation_args,
                    cs,
                )
            }
            hir::Resolution::FunctionSet(candidates) => {
                let visible: Vec<_> = candidates
                    .iter()
                    .cloned()
                    .filter(|id| self.gcx().is_definition_visible(*id, self.current_def))
                    .collect();

                if visible.is_empty() {
                    self.gcx()
                        .dcx()
                        .emit_error("function is not visible here".into(), Some(span));
                    return Ty::error(self.gcx());
                }

                if !allow_unsafe_callable_values {
                    if let Some(def_id) = visible
                        .iter()
                        .copied()
                        .find(|id| self.is_unsafe_callable_definition(*id))
                    {
                        return self.emit_unsafe_callable_value_error(def_id, span);
                    }
                }

                let ty = cs.infer_cx.next_ty_var(span);
                let mut branches = vec![];
                for candidate in visible {
                    let candidate_ty = self.gcx().get_type(candidate);
                    let goal = Goal::BindOverload(BindOverloadGoalData {
                        node_id,
                        var_ty: ty,
                        candidate_ty,
                        source: candidate,
                        instantiation_args,
                    });
                    branches.push(DisjunctionBranch {
                        goal,
                        source: Some(candidate),
                        autoref_cost: 0,
                        matches_expectation: false,
                        matches_async_preference: prefer_async.is_some_and(|want_async| {
                            self.gcx().definition_is_async(candidate) == want_async
                        }),
                        deref_steps: 0,
                    });
                }
                cs.add_goal(Goal::Disjunction(branches), span);
                ty
            }
            hir::Resolution::SelfTypeAlias(..) => {
                let Some(nominal) = self.constructor_nominal_from_resolution(resolution) else {
                    self.gcx().dcx().emit_error(
                        "cannot use `Self` as a value in this context".into(),
                        Some(span),
                    );
                    return Ty::error(self.gcx());
                };
                self.synth_constructor_value_expression(
                    node_id,
                    nominal,
                    span,
                    expectation,
                    instantiation_args,
                    cs,
                )
            }
            hir::Resolution::PrimaryType(..) => {
                self.gcx().dcx().emit_error(
                    "primitive types cannot be used as values".into(),
                    Some(span),
                );
                Ty::error(self.gcx())
            }
            hir::Resolution::InterfaceSelfTypeParameter(..) => {
                self.gcx().dcx().emit_error(
                    "`Self` type parameter cannot be used as a value".into(),
                    Some(span),
                );
                Ty::error(self.gcx())
            }
            hir::Resolution::StdItem(std_type) => {
                // Resolve to the actual std library type (e.g., Dictionary, Optional, List)
                let Some(name) = std_type.name_str() else {
                    self.gcx().dcx().emit_error(
                        "this standard library type cannot be used as a value".into(),
                        Some(span),
                    );
                    return Ty::error(self.gcx());
                };
                let Some(def_id) = self.gcx().std_item_def(*std_type) else {
                    self.gcx().dcx().emit_error(
                        format!("unable to resolve standard library type '{}'", name).into(),
                        Some(span),
                    );
                    return Ty::error(self.gcx());
                };
                // Treat Foundation types like struct/enum constructors - bind to constructor overload set
                let kind = self.gcx().definition_kind(def_id);
                match kind {
                    DefinitionKind::Struct | DefinitionKind::Enum => self
                        .synth_constructor_value_expression(
                            node_id,
                            def_id,
                            span,
                            expectation,
                            instantiation_args,
                            cs,
                        ),
                    _ => {
                        // For other types (interfaces, aliases), just return the type
                        self.gcx().get_type(def_id)
                    }
                }
            }
            hir::Resolution::Error => unreachable!(),
        }
    }

    fn synth_constructor_value_expression(
        &self,
        node_id: NodeID,
        nominal: DefinitionID,
        span: Span,
        expectation: Option<Ty<'ctx>>,
        instantiation_args: Option<GenericArguments<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let ty = cs.infer_cx.next_ty_var(span);
        if !self.bind_constructor_overload_set(node_id, nominal, span, ty, instantiation_args, cs) {
            return Ty::error(self.gcx());
        }
        if let Some(expectation) = expectation {
            cs.equal(expectation, ty, span);
        }
        ty
    }

    fn synth_call_expression(
        &self,
        expression: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        expect_ty: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let prefer_async_call = self.direct_await_operand.get() == Some(expression.id);

        // Builtin `make`: returns a pointer to the argument type.
        if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &callee.kind
            && matches!(
                path.resolution,
                hir::Resolution::StdItem(hir::StdItem::Make)
            )
        {
            if arguments.len() != 1 {
                self.gcx().dcx().emit_error(
                    "`make` expects exactly one argument".into(),
                    Some(expression.span),
                );
                return Ty::error(self.gcx());
            }
            let arg_ty = self.synth(&arguments[0].expression, cs);
            let ptr_ty = self
                .gcx()
                .store
                .interners
                .intern_ty(TyKind::Reference(arg_ty, hir::Mutability::Mutable));
            return ptr_ty;
        }

        let callee_ty = match &callee.kind {
            hir::ExpressionKind::InferredMember { name } => {
                let result_ty = cs.infer_cx.next_ty_var(callee.span);
                cs.add_goal(
                    Goal::InferredStaticMember(InferredStaticMemberGoalData {
                        node_id: callee.id,
                        name: *name,
                        expr_ty: result_ty,
                        base_hint: expect_ty,
                        allow_unsafe_callable_values: true,
                        prefer_async: prefer_async_call,
                        span: callee.span,
                    }),
                    callee.span,
                );
                cs.record_expr_ty(callee.id, result_ty);
                result_ty
            }
            hir::ExpressionKind::Path(path) => {
                let result_ty = self.synth_path_expression_with_policy(
                    callee,
                    path,
                    None,
                    true,
                    Some(prefer_async_call),
                    cs,
                );
                cs.record_expr_ty(callee.id, result_ty);
                result_ty
            }
            _ => self.synth(callee, cs),
        };

        let callee_def = self.resolve_callee(callee, cs);
        let arg_expectations = if !callee_ty.is_error() {
            self.argument_expectations_for_call(
                callee, arguments, callee_ty, expect_ty, callee_def, cs,
            )
        } else {
            None
        };

        let apply_arguments: Vec<ApplyArgument<'ctx>> = arguments
            .iter()
            .enumerate()
            .map(|(index, n)| {
                let expected = arg_expectations
                    .as_ref()
                    .and_then(|items| items.get(index))
                    .and_then(|item| *item);
                let ty = if let Some(expected) = expected {
                    let is_closure = matches!(n.expression.kind, hir::ExpressionKind::Closure(_));
                    if expected.expects_async_callable && is_closure {
                        self.with_forced_async_closure_expr(n.expression.id, || {
                            self.synth_with_expectation(&n.expression, Some(expected.ty), cs)
                        })
                    } else {
                        self.synth_with_expectation(&n.expression, Some(expected.ty), cs)
                    }
                } else {
                    self.synth(&n.expression, cs)
                };
                ApplyArgument {
                    id: n.expression.id,
                    label: n.label.map(|n| n.identifier),
                    ty,
                    span: n.expression.span,
                }
            })
            .collect();

        if callee_ty.is_error() || apply_arguments.iter().any(|arg| arg.ty.is_error()) {
            return Ty::error(self.gcx());
        }

        let result_ty = match cs.infer_cx.resolve_vars_if_possible(callee_ty).kind() {
            TyKind::FnPointer { output, .. } | TyKind::Closure { output, .. }
                if matches!(
                    cs.infer_cx.resolve_vars_if_possible(output).kind(),
                    TyKind::Never
                ) =>
            {
                output
            }
            _ => cs.infer_cx.next_ty_var(expression.span),
        };
        cs.record_expr_ty(expression.id, result_ty);

        let is_known_async_call = callee_def
            .is_some_and(|def_id| self.gcx().definition_is_async(def_id))
            || self.type_is_async_callable(callee_ty);
        if is_known_async_call {
            self.results.borrow_mut().record_async_call(expression.id);
        }

        let uses_function_overload_set = match &callee.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                matches!(path.resolution, hir::Resolution::FunctionSet(_))
            }
            hir::ExpressionKind::Path(hir::ResolvedPath::Relative(_, segment)) => {
                matches!(segment.resolution, hir::Resolution::FunctionSet(_))
            }
            _ => matches!(
                self.results.borrow().value_resolution(callee.id),
                Some(hir::Resolution::FunctionSet(_))
            ),
        };
        let may_resolve_async_via_overload = uses_function_overload_set
            || matches!(callee.kind, hir::ExpressionKind::InferredMember { .. });

        let data = ApplyGoalData {
            call_node_id: expression.id,
            call_span: expression.span,
            callee_ty,
            callee_source: callee_def,
            is_unsafe_context: self.unsafe_depth.get() > 0,
            result_ty,
            _expect_ty: expect_ty,
            arguments: apply_arguments,
            skip_labels: false,
        };
        cs.add_goal(Goal::Apply(data), expression.span);

        if !is_known_async_call && may_resolve_async_via_overload {
            self.defer_async_call_surface_check(expression.id, expression.span);
            return result_ty;
        }

        self.finish_async_call_surface_check(expression.id, expression.span, result_ty)
    }

    fn argument_expectations_for_call(
        &self,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        callee_ty: Ty<'ctx>,
        expect_ty: Option<Ty<'ctx>>,
        callee_def: Option<DefinitionID>,
        cs: &mut Cs<'ctx>,
    ) -> Option<Vec<Option<ArgumentExpectation<'ctx>>>> {
        if let hir::ExpressionKind::InferredMember { name } = &callee.kind {
            if let Some(expect_ty) = expect_ty {
                if let Some(args) =
                    self.inferred_member_argument_expectations(name, expect_ty, callee.span, cs)
                {
                    return Some(
                        args.into_iter()
                            .map(|ty| {
                                Some(ArgumentExpectation {
                                    ty,
                                    expects_async_callable: self.ty_is_known_async_callable(ty),
                                })
                            })
                            .collect(),
                    );
                }
            }
        }

        // Get the callee type (may still have type params if not yet instantiated)
        let callee_ty = cs.infer_cx.resolve_vars_if_possible(callee_ty);
        let (instantiated_inputs, instantiated_output) = match callee_ty.kind() {
            TyKind::FnPointer { inputs, output } => (inputs.to_vec(), output),
            _ => return None,
        };

        // If we have a callee definition with type parameters that have Fn bounds,
        // create synthetic FnPointer expectations to help infer closure parameter types
        if let Some(def_id) = callee_def {
            let signature = self.gcx().get_signature(def_id);
            let original_inputs: Vec<Ty<'ctx>> = signature.inputs.iter().map(|p| p.ty).collect();
            let identity_args = GenericsBuilder::identity_for_item(self.gcx(), def_id);
            let has_callable_bound_inputs = original_inputs.iter().copied().any(|input| {
                self.try_resolve_fn_bound(input, def_id, identity_args)
                    .is_some()
            });
            let bound_instantiation_args = if has_callable_bound_inputs {
                cs.instantiation(callee.id)
                    .or_else(|| self.results.borrow().instantiation(callee.id))
                    .unwrap_or_else(|| {
                        self.infer_call_generic_args(
                            def_id,
                            &original_inputs,
                            &instantiated_inputs,
                            signature.output,
                            instantiated_output,
                        )
                    })
            } else {
                self.infer_call_generic_args(
                    def_id,
                    &original_inputs,
                    &instantiated_inputs,
                    signature.output,
                    instantiated_output,
                )
            };

            let mut resolved = Vec::with_capacity(original_inputs.len());
            let mut resolved_async_expectations = Vec::with_capacity(original_inputs.len());
            for (&original_ty, &instantiated_ty) in
                original_inputs.iter().zip(instantiated_inputs.iter())
            {
                // Try to resolve Fn bound if the original param is a type parameter
                if let Some(bound) =
                    self.try_resolve_fn_bound(original_ty, def_id, bound_instantiation_args)
                {
                    resolved.push(bound.fn_signature_ty);
                    resolved_async_expectations.push(bound.expects_async_callable);
                } else {
                    // Fall back to instantiated type from callee
                    resolved.push(instantiated_ty);
                    resolved_async_expectations
                        .push(self.ty_is_known_async_callable(instantiated_ty));
                }
            }
            return self.map_argument_expectations(
                callee_def,
                &resolved,
                &resolved_async_expectations,
                arguments,
            );
        }

        let parameter_async_expectations: Vec<bool> = instantiated_inputs
            .iter()
            .map(|&ty| self.ty_is_known_async_callable(ty))
            .collect();
        self.map_argument_expectations(
            callee_def,
            &instantiated_inputs,
            &parameter_async_expectations,
            arguments,
        )
    }

    fn map_argument_expectations(
        &self,
        callee_def: Option<DefinitionID>,
        parameter_tys: &[Ty<'ctx>],
        parameter_expects_async: &[bool],
        arguments: &[hir::ExpressionArgument],
    ) -> Option<Vec<Option<ArgumentExpectation<'ctx>>>> {
        if arguments.is_empty() {
            return Some(vec![]);
        }

        let signature = if let Some(def_id) = callee_def {
            self.gcx().get_signature(def_id).clone()
        } else {
            crate::sema::models::LabeledFunctionSignature {
                inputs: parameter_tys
                    .iter()
                    .map(|&ty| crate::sema::models::LabeledFunctionParameter {
                        label: None,
                        name: self.gcx().intern_symbol(""),
                        ty,
                        default_provider: None,
                    })
                    .collect(),
                output: self.gcx().types.error,
                is_variadic: false,
                abi: None,
            }
        };

        let apply_args: Vec<ApplyArgument<'ctx>> = arguments
            .iter()
            .map(|arg| ApplyArgument {
                id: arg.expression.id,
                label: arg.label.map(|l| l.identifier),
                ty: self.gcx().types.error,
                span: arg.expression.span,
            })
            .collect();

        if validate_arity(&signature, &apply_args).is_err() {
            return None;
        }

        let positions = match match_arguments_to_parameters(&signature, &apply_args, false) {
            Ok(p) => p,
            Err(_) => return None,
        };

        let mut expectations = vec![None; arguments.len()];
        for (param_idx, arg_indices) in positions.iter().enumerate() {
            let Some(&param_ty) = parameter_tys.get(param_idx) else {
                continue;
            };

            let expected_ty =
                if signature.is_variadic && param_idx == signature.inputs.len().saturating_sub(1) {
                    match param_ty.kind() {
                        TyKind::Adt(_, args) => match args.get(0) {
                            Some(GenericArgument::Type(inner)) => *inner,
                            _ => param_ty,
                        },
                        _ => param_ty,
                    }
                } else {
                    param_ty
                };
            let expects_async = parameter_expects_async
                .get(param_idx)
                .copied()
                .unwrap_or(false);

            for &arg_idx in arg_indices {
                if let Some(slot) = expectations.get_mut(arg_idx) {
                    *slot = Some(ArgumentExpectation {
                        ty: expected_ty,
                        expects_async_callable: expects_async,
                    });
                }
            }
        }

        Some(expectations)
    }

    /// If the type is a type parameter with an Fn/AsyncFn bound,
    /// create a synthetic FnPointer type with the expected inputs/output.
    /// Returns None if the type is not a type parameter or has no Fn bound.
    fn try_resolve_fn_bound(
        &self,
        ty: Ty<'ctx>,
        def_id: DefinitionID,
        instantiation_args: GenericArguments<'ctx>,
    ) -> Option<ResolvedCallableBound<'ctx>> {
        let TyKind::Parameter(param) = ty.kind() else {
            return None;
        };

        let gcx = self.gcx();
        let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(gcx, def_id);

        // Look for callable bounds on this parameter.
        let fn_def = gcx.std_item_def(hir::StdItem::Fn);
        let fn_mut_def = gcx.std_item_def(hir::StdItem::FnMut);
        let async_fn_def = gcx.std_item_def(hir::StdItem::AsyncFn);
        let async_fn_mut_def = gcx.std_item_def(hir::StdItem::AsyncFnMut);
        let fn_once_def = gcx.std_item_def(hir::StdItem::FnOnce);
        let async_fn_once_def = gcx.std_item_def(hir::StdItem::AsyncFnOnce);

        for constraint in constraints {
            if let crate::sema::models::Constraint::Bound {
                ty: bound_ty,
                mut interface,
            } = constraint.value
            {
                // Check if this constraint applies to our parameter
                let TyKind::Parameter(bound_param) = bound_ty.kind() else {
                    continue;
                };

                // Match by index and name since we're in the same definition context
                if bound_param.index != param.index || bound_param.name != param.name {
                    continue;
                }

                let is_fn_trait = fn_def == Some(interface.id)
                    || fn_mut_def == Some(interface.id)
                    || fn_once_def == Some(interface.id)
                    || async_fn_def == Some(interface.id)
                    || async_fn_mut_def == Some(interface.id)
                    || async_fn_once_def == Some(interface.id);

                if !is_fn_trait {
                    continue;
                }
                let expects_async_callable = async_fn_def == Some(interface.id)
                    || async_fn_mut_def == Some(interface.id)
                    || async_fn_once_def == Some(interface.id);

                interface = instantiate_interface_ref_with_args(gcx, interface, instantiation_args);

                // Extract Args and Output from Fn[Args, Output].
                // Raw interface refs still carry `Self` as the first argument.
                if interface.arguments.len() < 3 {
                    continue;
                }

                let Some(args_ty) = interface.arguments[1].ty() else {
                    continue;
                };
                let Some(output_ty) = interface.arguments[2].ty() else {
                    continue;
                };

                // Unpack tuple Args into individual inputs (rust-call ABI)
                let inputs: Vec<Ty<'ctx>> = if let TyKind::Tuple(elem_tys) = args_ty.kind() {
                    elem_tys.to_vec()
                } else {
                    vec![args_ty]
                };
                let inputs = gcx.store.interners.intern_ty_list(inputs);

                // Create a synthetic FnPointer type to pass as expectation
                // This allows the closure synthesizer to extract expected input types
                return Some(ResolvedCallableBound {
                    fn_signature_ty: gcx.store.interners.intern_ty(TyKind::FnPointer {
                        inputs,
                        output: output_ty,
                    }),
                    expects_async_callable,
                });
            }
        }

        None
    }

    /// Infer call-site generic arguments by matching a definition's signature types
    /// against the instantiated callee signature types.
    ///
    /// This lets us instantiate `Fn/AsyncFn` bounds with inference variables
    /// (for example, infer `Out` from closure return type).
    fn infer_call_generic_args(
        &self,
        def_id: DefinitionID,
        original_inputs: &[Ty<'ctx>],
        instantiated_inputs: &[Ty<'ctx>],
        original_output: Ty<'ctx>,
        instantiated_output: Ty<'ctx>,
    ) -> GenericArguments<'ctx> {
        let gcx = self.gcx();
        let identity_args = GenericsBuilder::identity_for_item(gcx, def_id);
        let mut inferred: Vec<Option<GenericArgument<'ctx>>> = vec![None; identity_args.len()];

        for (&original, &instantiated) in original_inputs.iter().zip(instantiated_inputs.iter()) {
            Self::record_generic_bindings_from_ty(original, instantiated, &mut inferred);
        }
        Self::record_generic_bindings_from_ty(original_output, instantiated_output, &mut inferred);

        let resolved: Vec<GenericArgument<'ctx>> = identity_args
            .iter()
            .enumerate()
            .map(|(index, identity)| inferred[index].unwrap_or(*identity))
            .collect();
        gcx.store.interners.intern_generic_args(resolved)
    }

    fn record_generic_bindings_from_ty(
        pattern: Ty<'ctx>,
        actual: Ty<'ctx>,
        inferred: &mut [Option<GenericArgument<'ctx>>],
    ) {
        match pattern.kind() {
            TyKind::Parameter(param) => {
                Self::record_generic_binding(param.index, GenericArgument::Type(actual), inferred);
            }
            TyKind::Reference(pattern_inner, _) | TyKind::Pointer(pattern_inner, _) => {
                if let TyKind::Reference(actual_inner, _) | TyKind::Pointer(actual_inner, _) =
                    actual.kind()
                {
                    Self::record_generic_bindings_from_ty(pattern_inner, actual_inner, inferred);
                }
            }
            TyKind::Tuple(pattern_items) => {
                let TyKind::Tuple(actual_items) = actual.kind() else {
                    return;
                };
                for (&pattern_item, &actual_item) in pattern_items.iter().zip(actual_items.iter()) {
                    Self::record_generic_bindings_from_ty(pattern_item, actual_item, inferred);
                }
            }
            TyKind::FnPointer {
                inputs: pattern_inputs,
                output: pattern_output,
            } => {
                let TyKind::FnPointer {
                    inputs: actual_inputs,
                    output: actual_output,
                } = actual.kind()
                else {
                    return;
                };
                for (&pattern_input, &actual_input) in
                    pattern_inputs.iter().zip(actual_inputs.iter())
                {
                    Self::record_generic_bindings_from_ty(pattern_input, actual_input, inferred);
                }
                Self::record_generic_bindings_from_ty(pattern_output, actual_output, inferred);
            }
            TyKind::Adt(pattern_def, pattern_args) => {
                let TyKind::Adt(actual_def, actual_args) = actual.kind() else {
                    return;
                };
                if pattern_def.id != actual_def.id || pattern_args.len() != actual_args.len() {
                    return;
                }
                for (&pattern_arg, &actual_arg) in pattern_args.iter().zip(actual_args.iter()) {
                    Self::record_generic_bindings_from_arg(pattern_arg, actual_arg, inferred);
                }
            }
            TyKind::Alias {
                kind: pattern_kind,
                def_id: pattern_def_id,
                args: pattern_args,
            } => {
                let TyKind::Alias {
                    kind: actual_kind,
                    def_id: actual_def_id,
                    args: actual_args,
                } = actual.kind()
                else {
                    return;
                };
                if pattern_kind != actual_kind
                    || pattern_def_id != actual_def_id
                    || pattern_args.len() != actual_args.len()
                {
                    return;
                }
                for (&pattern_arg, &actual_arg) in pattern_args.iter().zip(actual_args.iter()) {
                    Self::record_generic_bindings_from_arg(pattern_arg, actual_arg, inferred);
                }
            }
            TyKind::Closure {
                kind: pattern_kind,
                inputs: pattern_inputs,
                output: pattern_output,
                ..
            } => {
                let TyKind::Closure {
                    kind: actual_kind,
                    inputs: actual_inputs,
                    output: actual_output,
                    ..
                } = actual.kind()
                else {
                    return;
                };
                if pattern_kind != actual_kind {
                    return;
                }
                for (&pattern_input, &actual_input) in
                    pattern_inputs.iter().zip(actual_inputs.iter())
                {
                    Self::record_generic_bindings_from_ty(pattern_input, actual_input, inferred);
                }
                Self::record_generic_bindings_from_ty(pattern_output, actual_output, inferred);
            }
            _ => {}
        }
    }

    fn record_generic_bindings_from_arg(
        pattern: GenericArgument<'ctx>,
        actual: GenericArgument<'ctx>,
        inferred: &mut [Option<GenericArgument<'ctx>>],
    ) {
        match (pattern, actual) {
            (GenericArgument::Type(pattern_ty), GenericArgument::Type(actual_ty)) => {
                Self::record_generic_bindings_from_ty(pattern_ty, actual_ty, inferred);
            }
            (GenericArgument::Const(pattern_const), GenericArgument::Const(actual_const)) => {
                Self::record_generic_bindings_from_const(pattern_const, actual_const, inferred);
            }
            _ => {}
        }
    }

    fn record_generic_bindings_from_const(
        pattern: Const<'ctx>,
        actual: Const<'ctx>,
        inferred: &mut [Option<GenericArgument<'ctx>>],
    ) {
        if let ConstKind::Param(param) = pattern.kind {
            Self::record_generic_binding(param.index, GenericArgument::Const(actual), inferred);
        }
        Self::record_generic_bindings_from_ty(pattern.ty, actual.ty, inferred);
    }

    fn record_generic_binding(
        index: usize,
        argument: GenericArgument<'ctx>,
        inferred: &mut [Option<GenericArgument<'ctx>>],
    ) {
        let Some(slot) = inferred.get_mut(index) else {
            return;
        };
        if slot.is_none() {
            *slot = Some(argument);
        }
    }

    fn inferred_member_argument_expectations(
        &self,
        name: &crate::span::Identifier,
        expect_ty: Ty<'ctx>,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Option<Vec<Ty<'ctx>>> {
        let expect_ty = cs.infer_cx.resolve_vars_if_possible(expect_ty);
        if expect_ty.is_infer() || expect_ty.is_error() {
            return None;
        }

        let base_ty = match expect_ty.kind() {
            TyKind::FnPointer { output, .. } => {
                let output = cs.infer_cx.resolve_vars_if_possible(output);
                if output.is_infer() {
                    return None;
                }
                output
            }
            _ => expect_ty,
        };
        let base_ty = cs.infer_cx.resolve_vars_if_possible(base_ty);

        let head = type_head_from_value_ty(base_ty)?;
        let base_args = match base_ty.kind() {
            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
            _ => None,
        };

        let resolution = self.resolve_static_member_resolution(head, base_ty, name, span, false);
        let def_id = resolution.definition_id()?;
        let signature = self.gcx().get_signature(def_id);

        let generics = self.gcx().generics_of(def_id);
        let signature = if generics.is_empty() {
            signature.clone()
        } else if let Some(base_args) = base_args {
            let args = GenericsBuilder::for_item(self.gcx(), def_id, |param, _| {
                base_args
                    .get(param.index)
                    .cloned()
                    .unwrap_or_else(|| cs.infer_cx.var_for_generic_param(param, span))
            });
            instantiate_signature_with_args(self.gcx(), signature, args)
        } else {
            return None;
        };

        Some(signature.inputs.into_iter().map(|param| param.ty).collect())
    }

    fn synth_method_call_expression(
        &self,
        expression: &hir::Expression,
        receiver: &hir::Expression,
        name: &crate::span::Identifier,
        arguments: &[hir::ExpressionArgument],
        expect_ty: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let prefer_async_call = self.direct_await_operand.get() == Some(expression.id);

        // Static member invocation on a type (e.g., `List[Int].new()`).
        if let hir::ExpressionKind::Path(path) = &receiver.kind {
            let (resolution, base_args) =
                self.resolve_value_path_resolution_with_args(path, receiver.span, true, cs);
            if let Some(def_id) = self.value_path_def_id(&resolution) {
                match self.gcx().definition_kind(def_id) {
                    DefinitionKind::Struct | DefinitionKind::Enum => {
                        // Treat as a static member call.
                        let type_node = hir::Type {
                            id: receiver.id,
                            kind: hir::TypeKind::Nominal(path.clone()),
                            span: receiver.span,
                        };
                        let base_ty = self.lower_type(&type_node);
                        self.add_type_constraints(base_ty, receiver.span, cs);
                        let Some(head) = type_head_from_value_ty(base_ty) else {
                            self.gcx().dcx().emit_error(
                                "cannot resolve members on this type receiver".into(),
                                Some(receiver.span),
                            );
                            return Ty::error(self.gcx());
                        };

                        let base_args = match base_ty.kind() {
                            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
                            _ => base_args,
                        };

                        let resolution = self
                            .resolve_static_member_resolution(head, base_ty, name, name.span, true);
                        self.record_value_path_resolution(receiver.id, &resolution);

                        let segment = hir::PathSegment {
                            id: receiver.id,
                            identifier: *name,
                            arguments: None,
                            span: name.span,
                            resolution: resolution.clone(),
                        };
                        let instantiation_args = self.lower_value_path_instantiation_args(
                            &resolution,
                            &segment,
                            base_args,
                        );
                        let callee_ty = self.instantiate_value_path(
                            receiver.id,
                            receiver.span,
                            &resolution,
                            instantiation_args,
                            expect_ty,
                            true,
                            Some(prefer_async_call),
                            cs,
                        );

                        let apply_arguments: Vec<ApplyArgument<'ctx>> = arguments
                            .iter()
                            .map(|n| ApplyArgument {
                                id: n.expression.id,
                                label: n.label.map(|n| n.identifier),
                                ty: self.synth(&n.expression, cs),
                                span: n.expression.span,
                            })
                            .collect();

                        if callee_ty.is_error()
                            || apply_arguments.iter().any(|arg| arg.ty.is_error())
                        {
                            return Ty::error(self.gcx());
                        }

                        let result_ty = cs.infer_cx.next_ty_var(expression.span);
                        cs.record_expr_ty(expression.id, result_ty);

                        let data = ApplyGoalData {
                            call_node_id: expression.id,
                            call_span: expression.span,
                            callee_ty,
                            callee_source: resolution.definition_id(),
                            is_unsafe_context: self.unsafe_depth.get() > 0,
                            result_ty,
                            _expect_ty: expect_ty,
                            arguments: apply_arguments,
                            skip_labels: false,
                        };
                        cs.add_goal(Goal::Apply(data), expression.span);

                        if resolution
                            .definition_id()
                            .is_some_and(|id| self.gcx().definition_is_async(id))
                            || self.type_is_async_callable(callee_ty)
                        {
                            self.results.borrow_mut().record_async_call(expression.id);
                        } else if matches!(&resolution, hir::Resolution::FunctionSet(..)) {
                            self.defer_async_call_surface_check(expression.id, expression.span);
                            return result_ty;
                        }

                        return self.finish_async_call_surface_check(
                            expression.id,
                            expression.span,
                            result_ty,
                        );
                    }
                    _ => {}
                }
            }
        }

        let recv_ty = self.synth(receiver, cs);
        let receiver_can_mut_borrow = self.can_mutably_borrow_receiver(receiver, cs);
        let arg_expectations = if recv_ty.is_error() {
            None
        } else {
            self.method_argument_expectations(recv_ty, name, arguments.len(), expression.span, cs)
        };

        let args: Vec<ApplyArgument<'ctx>> = arguments
            .iter()
            .enumerate()
            .map(|(index, n)| {
                let expected = arg_expectations
                    .as_ref()
                    .and_then(|items| items.get(index))
                    .cloned();
                let ty = if let Some(expected) = expected {
                    let is_closure = matches!(n.expression.kind, hir::ExpressionKind::Closure(_));
                    if expected.expects_async_callable && is_closure {
                        self.with_forced_async_closure_expr(n.expression.id, || {
                            self.synth_with_expectation(&n.expression, Some(expected.ty), cs)
                        })
                    } else {
                        self.synth_with_expectation(&n.expression, Some(expected.ty), cs)
                    }
                } else {
                    self.synth(&n.expression, cs)
                };
                ApplyArgument {
                    id: n.expression.id,
                    label: n.label.map(|n| n.identifier),
                    ty,
                    span: n.expression.span,
                }
            })
            .collect();

        if recv_ty.is_error() || args.iter().any(|arg| arg.ty.is_error()) {
            return Ty::error(self.gcx());
        }

        let method_ty = cs.infer_cx.next_ty_var(name.span);
        let result_ty = cs.infer_cx.next_ty_var(expression.span);
        cs.record_expr_ty(expression.id, result_ty);

        cs.add_goal(
            Goal::MethodCall(MethodCallData {
                node_id: expression.id,
                receiver: recv_ty,
                receiver_can_mut_borrow,
                reciever_node: receiver.id,
                reciever_span: receiver.span,
                is_unsafe_context: self.unsafe_depth.get() > 0,
                method_ty: method_ty,
                prefer_async: prefer_async_call,
                expect_ty,
                name: *name,
                arguments: args,
                result: result_ty,
                span: expression.span,
            }),
            expression.span,
        );

        self.defer_async_call_surface_check(expression.id, expression.span);
        result_ty
    }
}

impl<'ctx> Checker<'ctx> {
    fn method_argument_expectations(
        &self,
        receiver_ty: Ty<'ctx>,
        name: &crate::span::Identifier,
        argument_count: usize,
        _span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Option<Vec<ArgumentExpectation<'ctx>>> {
        let gcx = self.gcx();

        let mut base_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
        if base_ty.is_error() || base_ty.is_infer() {
            return None;
        }

        loop {
            match base_ty.kind() {
                TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                    base_ty = cs.infer_cx.resolve_vars_if_possible(inner);
                    if base_ty.is_error() || base_ty.is_infer() {
                        return None;
                    }
                }
                _ => break,
            }
        }

        let Some(head) = type_head_from_value_ty(base_ty) else {
            return None;
        };

        let base_args = match base_ty.kind() {
            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
            _ => None,
        };

        let candidates = self.collect_inherent_instance_candidates(head, name.symbol);
        if candidates.is_empty() {
            return None;
        }

        let mut candidate_inputs: Vec<Vec<ArgumentExpectation<'ctx>>> = vec![];

        for def_id in candidates {
            if !gcx.is_definition_visible(def_id, self.current_def) {
                continue;
            }

            let signature = gcx.get_signature(def_id);
            let original_inputs: Vec<Ty<'ctx>> =
                signature.inputs.iter().map(|input| input.ty).collect();
            let generics = self.gcx().generics_of(def_id);
            let instantiation_args = if generics.is_empty() {
                None
            } else {
                let identity_args = GenericsBuilder::identity_for_item(self.gcx(), def_id);
                Some(GenericsBuilder::for_item(self.gcx(), def_id, |param, _| {
                    base_args
                        .and_then(|args| args.get(param.index).cloned())
                        .unwrap_or_else(|| identity_args[param.index])
                }))
            };
            let signature = if let Some(args) = instantiation_args {
                instantiate_signature_with_args(gcx, signature, args)
            } else {
                signature.clone()
            };

            let instantiated_inputs: Vec<Ty<'ctx>> =
                signature.inputs.iter().map(|input| input.ty).collect();
            if instantiated_inputs.is_empty() {
                continue;
            }

            let mut input_expectations =
                Vec::with_capacity(instantiated_inputs.len().saturating_sub(1));
            for (&original_ty, &instantiated_ty) in original_inputs
                .iter()
                .skip(1)
                .zip(instantiated_inputs.iter().skip(1))
            {
                if let Some(bound_args) = instantiation_args
                    && let Some(bound) = self.try_resolve_fn_bound(original_ty, def_id, bound_args)
                {
                    let expectation_ty =
                        self.freshen_method_expectation_ty(def_id, bound.fn_signature_ty, name.span, cs);
                    input_expectations.push(ArgumentExpectation {
                        ty: expectation_ty,
                        expects_async_callable: bound.expects_async_callable,
                    });
                } else {
                    let expectation_ty =
                        self.freshen_method_expectation_ty(def_id, instantiated_ty, name.span, cs);
                    input_expectations.push(ArgumentExpectation {
                        ty: expectation_ty,
                        expects_async_callable: self.ty_is_known_async_callable(expectation_ty),
                    });
                }
            }

            if input_expectations.len() != argument_count {
                continue;
            }

            candidate_inputs.push(input_expectations);
        }

        if candidate_inputs.is_empty() {
            return None;
        }

        let first = candidate_inputs[0].clone();
        if candidate_inputs.iter().all(|inputs| {
            inputs.len() == first.len()
                && inputs.iter().zip(first.iter()).all(|(lhs, rhs)| {
                    lhs.ty == rhs.ty && lhs.expects_async_callable == rhs.expects_async_callable
                })
        }) {
            Some(first)
        } else {
            None
        }
    }

    fn method_call_can_yield_mutable_reference(
        &self,
        receiver_ty: Ty<'ctx>,
        name: &crate::span::Identifier,
        argument_count: usize,
        cs: &Cs<'ctx>,
    ) -> bool {
        let gcx = self.gcx();

        let mut base_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
        if base_ty.is_error() || base_ty.is_infer() || base_ty.contains_inference() {
            return false;
        }

        loop {
            match base_ty.kind() {
                TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                    base_ty = cs.infer_cx.resolve_vars_if_possible(inner);
                    if base_ty.is_error() || base_ty.is_infer() || base_ty.contains_inference() {
                        return false;
                    }
                }
                _ => break,
            }
        }

        let Some(head) = type_head_from_value_ty(base_ty) else {
            return false;
        };

        let base_args = match base_ty.kind() {
            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
            _ => None,
        };

        self.collect_inherent_instance_candidates(head, name.symbol)
            .into_iter()
            .filter(|def_id| gcx.is_definition_visible(*def_id, self.current_def))
            .any(|def_id| {
                let signature = gcx.get_signature(def_id);
                let signature = if let Some(base_args) = base_args {
                    instantiate_signature_with_args(gcx, signature, base_args)
                } else {
                    signature.clone()
                };

                if signature.inputs.len() != argument_count + 1 {
                    return false;
                }

                matches!(
                    signature.output.kind(),
                    TyKind::Reference(_, hir::Mutability::Mutable)
                )
            })
    }

    fn freshen_method_expectation_ty(
        &self,
        def_id: DefinitionID,
        ty: Ty<'ctx>,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        use rustc_hash::FxHashSet;

        fn collect_generic_param_indices<'ctx>(ty: Ty<'ctx>, indices: &mut FxHashSet<usize>) {
            use crate::sema::models::TyKind;

            match ty.kind() {
                TyKind::Array { element, .. } => {
                    collect_generic_param_indices(element, indices);
                }
                TyKind::Parameter(param) => {
                    indices.insert(param.index);
                }
                TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                    collect_generic_param_indices(inner, indices);
                }
                TyKind::Tuple(items) => {
                    for &item in items.iter() {
                        collect_generic_param_indices(item, indices);
                    }
                }
                TyKind::FnPointer { inputs, output } => {
                    for &input in inputs.iter() {
                        collect_generic_param_indices(input, indices);
                    }
                    collect_generic_param_indices(output, indices);
                }
                TyKind::Closure {
                    captured_generics,
                    inputs,
                    output,
                    ..
                } => {
                    for &arg in captured_generics.iter() {
                        if let GenericArgument::Type(inner) = arg {
                            collect_generic_param_indices(inner, indices);
                        }
                    }
                    for &input in inputs.iter() {
                        collect_generic_param_indices(input, indices);
                    }
                    collect_generic_param_indices(output, indices);
                }
                TyKind::Adt(_, args) | TyKind::Alias { args, .. } => {
                    for &arg in args.iter() {
                        if let GenericArgument::Type(inner) = arg {
                            collect_generic_param_indices(inner, indices);
                        }
                    }
                }
                _ => {}
            }
        }

        let mut indices = FxHashSet::default();
        collect_generic_param_indices(ty, &mut indices);
        if indices.is_empty() {
            return ty;
        }

        let mut args: Vec<GenericArgument<'ctx>> = GenericsBuilder::identity_for_item(self.gcx(), def_id)
            .iter()
            .copied()
            .collect();
        for param in self.gcx().generics_of(def_id).parameters.iter() {
            if indices.contains(&param.index) {
                args[param.index] = cs.infer_cx.var_for_generic_param(param, span);
            }
        }
        let args = self.gcx().store.interners.intern_generic_args(args);

        instantiate_ty_with_args(self.gcx(), ty, args)
    }

    fn collect_inherent_instance_candidates(
        &self,
        head: TypeHead,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let databases = gcx.store.type_databases.borrow();
        let mut members = Vec::new();
        let mut seen = FxHashSet::default();

        for db in databases.values() {
            if let Some(index) = db.type_head_to_members.get(&head) {
                if let Some(set) = index.inherent_instance.get(&name) {
                    for &id in &set.members {
                        if seen.insert(id) {
                            members.push(id);
                        }
                    }
                }
            }
        }

        members
    }

    fn constructor_nominal_from_resolution(
        &self,
        resolution: &hir::Resolution,
    ) -> Option<DefinitionID> {
        let gcx = self.gcx();
        match resolution {
            hir::Resolution::Definition(id, DefinitionKind::Struct) => Some(*id),
            hir::Resolution::SelfConstructor(id) | hir::Resolution::SelfTypeAlias(id) => {
                match gcx.definition_kind(*id) {
                    DefinitionKind::Struct => Some(*id),
                    DefinitionKind::Impl => match gcx.get_impl_type_head(*id)? {
                        TypeHead::Nominal(nominal) => Some(nominal),
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn bind_constructor_overload_set(
        &self,
        node_id: NodeID,
        nominal: DefinitionID,
        span: Span,
        var_ty: Ty<'ctx>,
        instantiation_args: Option<GenericArguments<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> bool {
        let gcx = self.gcx();
        let head = TypeHead::Nominal(nominal);
        let name = gcx.intern_symbol("new");
        let constructors = self.collect_static_member_candidates(head, name);

        if constructors.is_empty() {
            let name = gcx.definition_ident(nominal).symbol;
            gcx.dcx().emit_error(
                format!("type '{name}' defines no methods named 'new'").into(),
                Some(span),
            );
            return false;
        }

        let mut branches = Vec::with_capacity(constructors.len());
        for ctor in constructors {
            let candidate_ty = gcx.get_type(ctor);
            branches.push(DisjunctionBranch {
                goal: Goal::BindOverload(BindOverloadGoalData {
                    node_id,
                    var_ty,
                    candidate_ty,
                    source: ctor,
                    instantiation_args,
                }),
                source: Some(ctor),
                autoref_cost: 0,
                matches_expectation: false,
                matches_async_preference: false,
                deref_steps: 0,
            });
        }

        cs.add_goal(Goal::Disjunction(branches), span);
        true
    }
}

impl<'ctx> Checker<'ctx> {
    fn synth_if_expression(
        &self,
        expression: &hir::Expression,
        node: &hir::IfExpression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Condition must be bool.
        let cond_ty = self.synth(&node.condition, cs);
        if !cond_ty.is_error() {
            cs.equal(self.gcx().types.bool, cond_ty, node.condition.span);
        }

        // then/else branches are expressions; typecheck with shared expectation.
        let then_ty = self.synth_with_expectation(&node.then_block, expectation, cs);
        let else_ty = if let Some(else_expr) = &node.else_block {
            let else_expectation = expectation.or(Some(then_ty));
            Some(self.synth_with_expectation(else_expr, else_expectation, cs))
        } else {
            None
        };

        if cond_ty.is_error()
            || then_ty.is_error()
            || else_ty.map(|ty| ty.is_error()).unwrap_or(false)
        {
            return Ty::error(self.gcx());
        }

        match else_ty {
            Some(else_ty) => {
                let result_ty =
                    expectation.unwrap_or_else(|| cs.infer_cx.next_ty_var(expression.span));

                let resolved_then = cs.infer_cx.resolve_vars_if_possible(then_ty);
                if matches!(resolved_then.kind(), TyKind::Never) {
                    cs.add_goal(
                        Goal::Coerce {
                            node_id: node.then_block.id,
                            from: then_ty,
                            to: result_ty,
                        },
                        node.then_block.span,
                    );
                } else {
                    cs.equal(result_ty, then_ty, node.then_block.span);
                }

                let else_expr = node
                    .else_block
                    .as_ref()
                    .expect("else_ty exists iff else block exists");
                let resolved_else = cs.infer_cx.resolve_vars_if_possible(else_ty);
                if matches!(resolved_else.kind(), TyKind::Never) {
                    cs.add_goal(
                        Goal::Coerce {
                            node_id: else_expr.id,
                            from: else_ty,
                            to: result_ty,
                        },
                        else_expr.span,
                    );
                } else {
                    cs.equal(result_ty, else_ty, else_expr.span);
                }

                result_ty
            }
            None => {
                // `if cond { ... }` without an else always has unit type.
                // The then branch value must be coercible to unit (or diverge).
                let unit_ty = self.gcx().types.void;
                cs.add_goal(
                    Goal::Coerce {
                        node_id: node.then_block.id,
                        from: then_ty,
                        to: unit_ty,
                    },
                    node.then_block.span,
                );
                unit_ty
            }
        }
    }

    fn synth_pattern_binding_expression(
        &self,
        _expression: &hir::Expression,
        condition: &hir::PatternBindingCondition,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let source_name = condition.source.diagnostic_name();

        // Typecheck the expression being matched
        let expr_ty = self.synth(&condition.expression, cs);
        if expr_ty.is_error() {
            GatherLocalsVisitor::from_match_arm(cs, self, &condition.pattern);
            self.mark_pattern_bindings_error(&condition.pattern);
            return Ty::error(self.gcx());
        }

        // Specialized diagnostic for optional binding shorthand (`if let`).
        // Catching this early avoids a cascade of resolution/type errors.
        if condition.source.kind == hir::MatchKind::OptionalBinding
            && !self.is_optional_type(expr_ty)
        {
            self.gcx().dcx().emit_error(
                format!(
                    "{} requires an Optional value, found '{}'",
                    source_name,
                    expr_ty.format(self.gcx())
                )
                .into(),
                Some(condition.expression.span),
            );
            self.mark_pattern_bindings_error(&condition.pattern);
            return Ty::error(self.gcx());
        }

        // Gather local bindings from the pattern before checking
        GatherLocalsVisitor::from_match_arm(cs, self, &condition.pattern);

        // Check the pattern against the expression's type
        let scrutinee_id = condition.expression.id;
        self.check_pattern(&condition.pattern, expr_ty, scrutinee_id, cs);
        cs.solve_intermediate();

        // Pattern binding conditions always evaluate to bool
        self.gcx().types.bool
    }

    fn synth_match_expression(
        &self,
        expression: &hir::Expression,
        node: &hir::MatchExpression,
        expectation: Option<Ty<'ctx>>,
        _cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let source_name = node.source.diagnostic_name();
        if node.arms.is_empty() {
            self.gcx().dcx().emit_error(
                format!("{source_name} must have at least one arm").into(),
                Some(node.kw_span),
            );
            return Ty::error(self.gcx());
        }

        // ══════════════════════════════════════════════════════════════════════
        // PHASE 1: Resolve scrutinee in its own constraint system
        // ══════════════════════════════════════════════════════════════════════
        // Flush pending constraints in the parent system (e.g., local variable initializations)
        // so that the scrutinee solver has access to the most up-to-date type information.
        _cs.solve_intermediate();

        // This ensures the scrutinee type is fully concrete before we check arms,
        // enabling inferred pattern resolution (e.g., `.some(value)`).
        let scrutinee_ty = {
            let mut scrutinee_cs = self.new_cs();
            self.with_infer_ctx(scrutinee_cs.infer_cx.clone(), || {
                let ty = self.synth(&node.value, &mut scrutinee_cs);
                scrutinee_cs.solve_intermediate();
                self.commit_constraint_results(&scrutinee_cs);
                _cs.merge(scrutinee_cs);
                ty
            })
        };
        // Re-resolve in parent context to get latest state
        let scrutinee_ty = _cs.infer_cx.resolve_vars_if_possible(scrutinee_ty);
        if scrutinee_ty.is_error() {
            return Ty::error(self.gcx());
        }

        // ══════════════════════════════════════════════════════════════════════
        // PHASE 1.5: Validate OptionalDefault scrutinee
        // ══════════════════════════════════════════════════════════════════════
        // For `??` operator (OptionalDefault), the LHS must be an Optional type.
        // Emit a single clear error instead of cascading pattern match errors.
        if matches!(node.source.kind, hir::MatchKind::OptionalDefault) {
            let is_optional = self.is_optional_type(scrutinee_ty);
            if !is_optional && !scrutinee_ty.is_error() {
                self.gcx().dcx().emit_error(
                    format!(
                        "{} requires an Optional type on the left-hand side, found '{}'",
                        source_name,
                        scrutinee_ty.format(self.gcx())
                    )
                    .into(),
                    Some(node.value.span),
                );
                return Ty::error(self.gcx());
            }
        }

        if matches!(node.source.kind, hir::MatchKind::OptionalUnwrap) {
            let is_optional = self.is_optional_type(scrutinee_ty);
            if !is_optional && !scrutinee_ty.is_error() {
                self.gcx().dcx().emit_error(
                    format!(
                        "{} requires an Optional value, found '{}'",
                        source_name,
                        scrutinee_ty.format(self.gcx())
                    )
                    .into(),
                    Some(node.value.span),
                );
                return Ty::error(self.gcx());
            }
        }

        if matches!(node.source.kind, hir::MatchKind::OptionalUnwrap) {
            return self.synth_optional_unwrap_match(
                expression,
                node,
                scrutinee_ty,
                expectation,
                _cs,
            );
        }

        // Create a shared inference context for all arms to share the result type variable
        let shared_infer_cx = self
            .infer_ctx()
            .unwrap_or_else(|| Rc::new(InferCtx::new(self.context)));
        let had_expectation = expectation.is_some();
        let result_ty = expectation.unwrap_or_else(|| shared_infer_cx.next_ty_var(expression.span));

        self.with_infer_ctx(shared_infer_cx.clone(), || {
            let mut all_arms_never = true;
            for arm in &node.arms {
                // Each arm gets its own constraint system
                let mut arm_cs = self.new_cs();
                arm_cs.infer_cx = shared_infer_cx.clone();

                GatherLocalsVisitor::from_match_arm(&arm_cs, self, &arm.pattern);
                self.check_pattern(&arm.pattern, scrutinee_ty, node.value.id, &mut arm_cs);
                arm_cs.solve_intermediate();

                if let Some(guard) = &arm.guard {
                    let guard_ty = self.synth_with_expectation(
                        guard,
                        Some(self.gcx().types.bool),
                        &mut arm_cs,
                    );
                    arm_cs.equal(self.gcx().types.bool, guard_ty, guard.span);
                }

                let arm_ty = self.synth_with_expectation(&arm.body, Some(result_ty), &mut arm_cs);

                // Solve intermediate to resolve any inference variables in arm_ty
                arm_cs.solve_intermediate();

                // Check if the resolved arm type is Never
                let resolved_arm_ty = arm_cs.infer_cx.resolve_vars_if_possible(arm_ty);

                // Use coercion for Never type (!) arms to allow diverging branches,
                // but use equality for other arms to preserve type inference behavior
                if matches!(resolved_arm_ty.kind(), TyKind::Never) {
                    arm_cs.add_goal(
                        Goal::Coerce {
                            node_id: arm.body.id,
                            from: arm_ty,
                            to: result_ty,
                        },
                        arm.body.span,
                    );
                } else {
                    all_arms_never = false;
                    arm_cs.equal(result_ty, arm_ty, arm.body.span);
                }

                // Solve and commit each arm independently
                arm_cs.solve_intermediate();
                self.commit_constraint_results(&arm_cs);
                _cs.merge(arm_cs);
            }

            if all_arms_never {
                let never_ty = Ty::new(TyKind::Never, self.gcx());
                if !had_expectation && result_ty.is_infer() {
                    _cs.equal(result_ty, never_ty, expression.span);
                    _cs.solve_intermediate();
                }
                return never_ty;
            }

            let resolved = shared_infer_cx.resolve_vars_if_possible(result_ty);
            if resolved.is_infer() {
                Ty::error(self.gcx())
            } else {
                resolved
            }
        })
    }

    fn synth_optional_unwrap_match(
        &self,
        expression: &hir::Expression,
        node: &hir::MatchExpression,
        scrutinee_ty: Ty<'ctx>,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let shared_infer_cx = self
            .infer_ctx()
            .unwrap_or_else(|| Rc::new(InferCtx::new(self.context)));

        self.with_infer_ctx(shared_infer_cx.clone(), || {
            let Some((some_arm, rest)) = node.arms.split_first() else {
                return Ty::error(self.gcx());
            };
            let none_arm = match rest {
                [arm] => arm,
                _ => {
                    self.gcx().dcx().emit_error(
                        "optional unwrap must have exactly two arms".into(),
                        Some(node.kw_span),
                    );
                    return Ty::error(self.gcx());
                }
            };

            let (result_ty, _wrap_some, _optional_args) = {
                let mut arm_cs = self.new_cs();
                arm_cs.infer_cx = shared_infer_cx.clone();

                GatherLocalsVisitor::from_match_arm(&arm_cs, self, &some_arm.pattern);
                self.check_pattern(&some_arm.pattern, scrutinee_ty, node.value.id, &mut arm_cs);
                arm_cs.solve_intermediate();

                if let Some(guard) = &some_arm.guard {
                    let guard_ty = self.synth_with_expectation(
                        guard,
                        Some(self.gcx().types.bool),
                        &mut arm_cs,
                    );
                    arm_cs.equal(self.gcx().types.bool, guard_ty, guard.span);
                }

                let body_ty = self.synth(&some_arm.body, &mut arm_cs);
                arm_cs.solve_intermediate();

                let resolved_body_ty = arm_cs.infer_cx.resolve_vars_if_possible(body_ty);
                let (result_ty, wrap_some, optional_args) = if resolved_body_ty.is_error() {
                    (resolved_body_ty, false, None)
                } else if let Some((args, _)) = self.optional_inner_type(resolved_body_ty) {
                    (resolved_body_ty, false, Some(args))
                } else {
                    let (opt_ty, args) = self.mk_optional_type(resolved_body_ty);
                    (opt_ty, true, Some(args))
                };

                if wrap_some {
                    if let Some(args) = optional_args {
                        arm_cs.record_adjustments(
                            some_arm.body.id,
                            vec![Adjustment::OptionalWrap {
                                is_some: true,
                                generic_args: args,
                            }],
                        );
                    }
                }

                self.commit_constraint_results(&arm_cs);
                cs.merge(arm_cs);
                (result_ty, wrap_some, optional_args)
            };

            if let Some(expectation) = expectation {
                cs.equal(result_ty, expectation, expression.span);
            }

            let mut none_cs = self.new_cs();
            none_cs.infer_cx = shared_infer_cx.clone();

            GatherLocalsVisitor::from_match_arm(&none_cs, self, &none_arm.pattern);
            self.check_pattern(&none_arm.pattern, scrutinee_ty, node.value.id, &mut none_cs);
            none_cs.solve_intermediate();

            if let Some(guard) = &none_arm.guard {
                let guard_ty =
                    self.synth_with_expectation(guard, Some(self.gcx().types.bool), &mut none_cs);
                none_cs.equal(self.gcx().types.bool, guard_ty, guard.span);
            }

            let none_ty =
                self.synth_with_expectation(&none_arm.body, Some(result_ty), &mut none_cs);
            none_cs.equal(result_ty, none_ty, none_arm.body.span);

            none_cs.solve_intermediate();
            self.commit_constraint_results(&none_cs);
            cs.merge(none_cs);

            let resolved = shared_infer_cx.resolve_vars_if_possible(result_ty);
            if resolved.is_infer() {
                Ty::error(self.gcx())
            } else {
                resolved
            }
        })
    }

    fn synth_unary_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::UnaryOperator,
        operand: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let operand_ty = self.synth(operand, cs);
        if operand_ty.is_error() {
            return Ty::error(self.gcx());
        }
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = UnOpGoalData {
            lhs: operand_ty,
            rho: result_ty,
            expectation,
            operator,
            span: expression.span,
            node_id: expression.id,
            rhs_id: operand.id,
        };

        cs.add_goal(Goal::UnaryOp(data), expression.span);
        result_ty
    }

    fn synth_binary_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::BinaryOperator,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // For arithmetic/bitwise ops where result type = operand type, forward expectation
        // to help infer literal types (e.g., 2 * 3 with expectation isize)
        let operand_expectation = match operator {
            hir::BinaryOperator::Add
            | hir::BinaryOperator::Sub
            | hir::BinaryOperator::Mul
            | hir::BinaryOperator::Div
            | hir::BinaryOperator::Rem
            | hir::BinaryOperator::BitAnd
            | hir::BinaryOperator::BitOr
            | hir::BinaryOperator::BitXor
            | hir::BinaryOperator::BitShl
            | hir::BinaryOperator::BitShr => expectation,
            // Comparison/boolean ops return bool, not operand type
            _ => None,
        };
        let lhs_ty = self.synth_with_expectation(lhs, operand_expectation, cs);
        let rhs_ty = self.synth_with_expectation(rhs, operand_expectation, cs);
        if lhs_ty.is_error() || rhs_ty.is_error() {
            return Ty::error(self.gcx());
        }
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = BinOpGoalData {
            lhs: lhs_ty,
            rhs: rhs_ty,
            rho: result_ty,
            expectation,
            operator,
            span: expression.span,
            node_id: expression.id,
            lhs_id: lhs.id,
            rhs_id: rhs.id,
        };

        cs.add_goal(Goal::BinaryOp(data), expression.span);
        result_ty
    }

    fn synth_assign_op_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::BinaryOperator,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Type-check the LHS and require it be a mutable place
        let (lhs_ty, ok) = self.synth_with_needs(lhs, None, Needs::MutPlace, cs);
        if !ok {
            return Ty::error(self.gcx());
        }

        let rhs_ty = self.synth(rhs, cs);
        if lhs_ty.is_error() || rhs_ty.is_error() {
            return Ty::error(self.gcx());
        }

        if let hir::ExpressionKind::Member { target, name } = &lhs.kind
            && let Some(receiver_ty) = cs.expr_ty(target.id)
        {
            let receiver_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
            let base_ty = match receiver_ty.kind() {
                TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => inner,
                _ => receiver_ty,
            };

            if self
                .lookup_member_property_on_base_ty(base_ty, name.symbol)
                .is_some()
            {
                self.gcx().dcx().emit_error(
                    "compound assignment on computed properties is not supported".into(),
                    Some(expression.span),
                );
                return Ty::error(self.gcx());
            }
        }

        let data = AssignOpGoalData {
            lhs: lhs_ty,
            rhs: rhs_ty,
            operator,
            span: expression.span,
            node_id: expression.id,
            lhs_id: lhs.id,
            rhs_id: rhs.id,
        };

        cs.add_goal(Goal::AssignOp(data), expression.span);

        // Assign ops return void/unit
        self.gcx().types.void
    }
}

impl<'ctx> Checker<'ctx> {
    fn is_unsafe_callable_definition(&self, id: DefinitionID) -> bool {
        self.gcx().definition_is_unsafe(id)
    }

    fn emit_unsafe_callable_value_error(&self, def_id: DefinitionID, span: Span) -> Ty<'ctx> {
        self.gcx().dcx().emit_error(
            crate::sema::error::TypeError::UnsafeCallableValueNotAllowed {
                name: self.gcx().definition_symbol_or_fallback(def_id),
            }
            .format(self.gcx())
            .into(),
            Some(span),
        );
        Ty::error(self.gcx())
    }

    fn resolve_callee(&self, node: &hir::Expression, cs: &Cs<'ctx>) -> Option<DefinitionID> {
        match &node.kind {
            hir::ExpressionKind::Path(path) => {
                if let Some(resolution) = self.results.borrow().value_resolution(node.id) {
                    return self.resolve_resolution_callee(&resolution);
                }
                let resolution = self.resolve_value_path_resolution(path, node.span, false, cs);
                self.resolve_resolution_callee(&resolution)
            }
            _ => None,
        }
    }

    fn resolve_resolution_callee(&self, res: &hir::Resolution) -> Option<DefinitionID> {
        match res {
            hir::Resolution::Definition(id, DefinitionKind::Function)
            | hir::Resolution::Definition(id, DefinitionKind::AssociatedFunction)
            | hir::Resolution::Definition(id, DefinitionKind::VariantConstructor(..)) => Some(*id),
            _ => None,
        }
    }

    fn resolve_value_path_resolution(
        &self,
        path: &hir::ResolvedPath,
        span: Span,
        emit_errors: bool,
        cs: &Cs<'ctx>,
    ) -> hir::Resolution {
        self.resolve_value_path_resolution_with_args(path, span, emit_errors, cs)
            .0
    }

    fn resolve_value_path_resolution_with_args(
        &self,
        path: &hir::ResolvedPath,
        span: Span,
        emit_errors: bool,
        cs: &Cs<'ctx>,
    ) -> (
        hir::Resolution,
        Option<crate::sema::models::GenericArguments<'ctx>>,
    ) {
        match path {
            hir::ResolvedPath::Resolved(path) => (path.resolution.clone(), None),
            hir::ResolvedPath::Relative(base_ty, segment) => {
                // Attempt to reuse generic arguments from the base type for inherent
                // static members (e.g., `List[Int].new`). Avoid lowering interface
                // types without a provided `Self`, which would panic.
                let base_is_interface = matches!(
                    &base_ty.kind,
                    hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path))
                        if matches!(
                            path.resolution,
                            hir::Resolution::Definition(_, DefinitionKind::Interface)
                        )
                );

                let mut lowered_base_ty = None;
                let mut base_args = None;
                if !base_is_interface {
                    let ty = self.lower_type(base_ty);
                    let ty = cs.infer_cx.resolve_vars_if_possible(ty);
                    if let TyKind::Adt(_, args) = ty.kind() {
                        if !args.is_empty() {
                            base_args = Some(args);
                        }
                    }
                    lowered_base_ty = Some(ty);
                }

                if !matches!(segment.resolution, hir::Resolution::Error) {
                    return (segment.resolution.clone(), base_args);
                }

                let base_ty = match lowered_base_ty {
                    Some(ty) => ty,
                    None => {
                        if emit_errors {
                            self.gcx().dcx().emit_error(
                                "cannot resolve members on this type receiver".into(),
                                Some(span),
                            );
                        }
                        return (hir::Resolution::Error, None);
                    }
                };

                let Some(head) = type_head_from_value_ty(base_ty) else {
                    let resolution = self.resolve_bounded_static_member_resolution(
                        base_ty,
                        &segment.identifier,
                        segment.identifier.span,
                        emit_errors,
                    );
                    return (resolution, base_args);
                };

                let resolution = self.resolve_static_member_resolution(
                    head,
                    base_ty,
                    &segment.identifier,
                    segment.identifier.span,
                    emit_errors,
                );
                (resolution, base_args)
            }
        }
    }

    fn record_value_path_resolution(&self, node_id: NodeID, resolution: &hir::Resolution) {
        match resolution {
            hir::Resolution::Definition(..)
            | hir::Resolution::LocalVariable(..)
            | hir::Resolution::StdItem(..) => {
                self.results
                    .borrow_mut()
                    .record_value_resolution(node_id, resolution.clone());
            }
            _ => {}
        }
    }

    fn resolve_static_member_resolution(
        &self,
        head: TypeHead,
        base_ty: Ty<'ctx>,
        name: &crate::span::Identifier,
        span: Span,
        emit_errors: bool,
    ) -> hir::Resolution {
        let gcx = self.gcx();
        if let TypeHead::Nominal(def_id) = head {
            if gcx.definition_kind(def_id) == DefinitionKind::Enum {
                let enum_def = gcx.get_enum_definition(def_id);

                if let Some(variant) = enum_def.variants.iter().find(|v| v.name == name.symbol) {
                    if !gcx.is_definition_visible(variant.ctor_def_id, self.current_def) {
                        if emit_errors {
                            gcx.dcx()
                                .emit_error("enum variant is not visible here".into(), Some(span));
                        }
                        return hir::Resolution::Error;
                    }

                    let kind = gcx.definition_kind(variant.ctor_def_id);
                    return hir::Resolution::Definition(variant.ctor_def_id, kind);
                }
            }
        }

        let candidates = self.collect_static_member_candidates(head, name.symbol);

        if candidates.is_empty() {
            if emit_errors {
                let msg = format!(
                    "unknown associated symbol named '{}' on type '{}'",
                    gcx.symbol_text(name.symbol),
                    base_ty.format(gcx)
                );
                gcx.dcx().emit_error(msg.into(), Some(span));
            }
            return hir::Resolution::Error;
        }

        let visible: Vec<_> = candidates
            .iter()
            .cloned()
            .filter(|id| gcx.is_definition_visible(*id, self.current_def))
            .collect();

        if visible.is_empty() {
            if emit_errors {
                gcx.dcx().emit_error(
                    format!(
                        "static member '{}' is not visible here",
                        gcx.symbol_text(name.symbol)
                    )
                    .into(),
                    Some(span),
                );
            }
            return hir::Resolution::Error;
        }

        if visible.len() == 1 {
            let id = visible[0];
            let kind = gcx.definition_kind(id);
            return hir::Resolution::Definition(id, kind);
        }

        hir::Resolution::FunctionSet(visible)
    }

    fn collect_static_member_candidates(&self, head: TypeHead, name: Symbol) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let databases = gcx.store.type_databases.borrow();
        let mut members = Vec::new();

        for db in databases.values() {
            if let Some(index) = db.type_head_to_members.get(&head) {
                if let Some(set) = index.inherent_static.get(&name) {
                    members.extend(set.members.iter().cloned());
                }
            }
        }

        members
    }

    fn resolve_bounded_static_member_resolution(
        &self,
        base_ty: Ty<'ctx>,
        name: &crate::span::Identifier,
        span: Span,
        emit_errors: bool,
    ) -> hir::Resolution {
        let gcx = self.gcx();
        let candidates = self.collect_bounded_static_member_candidates(base_ty, name.symbol);

        if candidates.is_empty() {
            if emit_errors {
                let msg = format!(
                    "unknown associated symbol named '{}' on type '{}'",
                    gcx.symbol_text(name.symbol),
                    base_ty.format(gcx)
                );
                gcx.dcx().emit_error(msg.into(), Some(span));
            }
            return hir::Resolution::Error;
        }

        let visible: Vec<_> = candidates
            .into_iter()
            .filter(|id| gcx.is_definition_visible(*id, self.current_def))
            .collect();
        if visible.is_empty() {
            if emit_errors {
                gcx.dcx().emit_error(
                    format!(
                        "static member '{}' is not visible here",
                        gcx.symbol_text(name.symbol)
                    )
                    .into(),
                    Some(span),
                );
            }
            return hir::Resolution::Error;
        }

        if visible.len() == 1 {
            let id = visible[0];
            let kind = gcx.definition_kind(id);
            return hir::Resolution::Definition(id, kind);
        }

        hir::Resolution::FunctionSet(visible)
    }

    fn collect_bounded_static_member_candidates(
        &self,
        base_ty: Ty<'ctx>,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let mut roots: Vec<InterfaceReference<'ctx>> = Vec::new();

        match base_ty.kind() {
            TyKind::Parameter(_) => {
                let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(
                    gcx,
                    self.current_def,
                );
                for constraint in constraints {
                    if let crate::sema::models::Constraint::Bound { ty, interface } =
                        constraint.value
                    {
                        if ty == base_ty {
                            roots.push(interface);
                        }
                    }
                }
            }
            TyKind::BoxedExistential { interfaces } => roots.extend_from_slice(interfaces),
            _ => return Vec::new(),
        }

        let mut out = Vec::new();
        let mut seen_defs: FxHashSet<DefinitionID> = FxHashSet::default();
        let mut seen_ifaces: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();
        let mut queue = std::collections::VecDeque::new();

        for root in roots {
            if seen_ifaces.insert(root) {
                queue.push_back(root);
            }
        }

        while let Some(interface_ref) = queue.pop_front() {
            if let Some(requirements) = gcx.get_interface_requirements(interface_ref.id) {
                for method in &requirements.methods {
                    if method.name == name && !method.has_self && seen_defs.insert(method.id) {
                        out.push(method.id);
                    }
                }
            }

            let Some(interface_def) = gcx.get_interface_definition(interface_ref.id) else {
                continue;
            };

            for superface in &interface_def.superfaces {
                let instantiated = instantiate_interface_ref_with_args(
                    gcx,
                    superface.value,
                    interface_ref.arguments,
                );
                if seen_ifaces.insert(instantiated) {
                    queue.push_back(instantiated);
                }
            }
        }

        out
    }

    fn value_path_def_id(&self, resolution: &hir::Resolution) -> Option<DefinitionID> {
        match resolution {
            hir::Resolution::StdItem(std_type) => self.gcx().std_item_def(*std_type),
            _ => resolution.definition_id(),
        }
    }

    fn lower_value_path_instantiation_args(
        &self,
        resolution: &hir::Resolution,
        segment: &hir::PathSegment,
        base_args: Option<GenericArguments<'ctx>>,
    ) -> Option<GenericArguments<'ctx>> {
        let gcx = self.gcx();
        let explicit_args = segment
            .arguments
            .as_ref()
            .map(|args| args.arguments.as_slice())
            .unwrap_or(&[]);
        let has_explicit = segment.arguments.is_some();
        let args_span = segment
            .arguments
            .as_ref()
            .map(|args| args.span)
            .unwrap_or(segment.span);

        if let hir::Resolution::StdItem(std_type) = resolution {
            if std_type.name_str().is_none() {
                if has_explicit {
                    gcx.dcx().emit_error(
                        "generic arguments are not permitted on this builtin".into(),
                        Some(args_span),
                    );
                }
                return None;
            }
        }

        match resolution {
            hir::Resolution::FunctionSet(_) => {
                if has_explicit {
                    gcx.dcx().emit_error(
                        "generic arguments are not permitted on overloaded function sets".into(),
                        Some(args_span),
                    );
                }
                return base_args;
            }
            hir::Resolution::LocalVariable(_)
            | hir::Resolution::PrimaryType(_)
            | hir::Resolution::InterfaceSelfTypeParameter(_)
            | hir::Resolution::SelfTypeAlias(_)
            | hir::Resolution::Error => {
                if has_explicit {
                    gcx.dcx().emit_error(
                        format!(
                            "generic arguments are not permitted on {}",
                            resolution.description()
                        )
                        .into(),
                        Some(args_span),
                    );
                }
                return None;
            }
            _ => {}
        }

        let Some(def_id) = self.value_path_def_id(resolution) else {
            return None;
        };

        let generics = gcx.generics_of(def_id);
        if generics.is_empty() && base_args.is_none() {
            if has_explicit {
                let name = gcx.definition_ident(def_id).symbol;
                gcx.dcx().emit_error(
                    format!(
                        "'{}' does not accept generic arguments",
                        gcx.symbol_text(name)
                    )
                    .into(),
                    Some(args_span),
                );
            }
            return None;
        }

        let explicit_count = explicit_args.len();
        let own_total = generics.total_count();
        let own_defaults = generics.default_count();
        let own_has_self = generics.has_self && generics.parent_count == 0;
        let def_kind = gcx.definition_kind(def_id);
        let allow_partial = matches!(
            def_kind,
            DefinitionKind::Function
                | DefinitionKind::AssociatedFunction
                | DefinitionKind::AssociatedOperator
                | DefinitionKind::VariantConstructor(VariantCtorKind::Function)
        );

        if explicit_count > own_total {
            gcx.dcx().emit_error(
                format!(
                    "excess generic arguments: {} takes at most {}, provided {}",
                    def_kind.description(),
                    own_total,
                    explicit_count
                )
                .into(),
                Some(args_span),
            );
        } else if has_explicit && !allow_partial {
            let min = own_total
                .saturating_sub(own_defaults)
                .saturating_sub(own_has_self as usize);
            if explicit_count < min {
                gcx.dcx().emit_error(
                    "Missing Generic Arguments".into(),
                    Some(segment.identifier.span),
                );
            }
        }

        let base_args = base_args.unwrap_or(GenericArguments::empty());
        let parent_count = if base_args.is_empty() {
            generics.parent_count
        } else {
            base_args.len()
        };
        let span = segment
            .arguments
            .as_ref()
            .map(|args| args.span)
            .unwrap_or(segment.span);
        let mut explicit_iter = explicit_args.iter();

        let args = GenericsBuilder::for_item(gcx, def_id, |param, current_args| {
            let current_args = gcx.store.interners.intern_generic_args_slice(current_args);
            if param.index < parent_count {
                if let Some(arg) = base_args.get(param.index) {
                    return *arg;
                }
                return self.lower_value_path_missing_arg(param, span, current_args);
            }

            if let Some(arg) = explicit_iter.next() {
                return self.lower_value_path_explicit_arg(param, arg);
            }

            self.lower_value_path_missing_arg(param, span, current_args)
        });

        Some(args)
    }

    fn lower_value_path_explicit_arg(
        &self,
        param: &GenericParameterDefinition,
        arg: &hir::TypeArgument,
    ) -> GenericArgument<'ctx> {
        let gcx = self.gcx();
        match (&param.kind, arg) {
            (GenericParameterDefinitionKind::Type { .. }, hir::TypeArgument::Type(ty)) => {
                GenericArgument::Type(self.lower_type(ty))
            }
            (GenericParameterDefinitionKind::Const { ty, .. }, hir::TypeArgument::Const(c)) => {
                let expected_ty = gcx
                    .try_generic_const_param_ty(param.id)
                    .unwrap_or_else(|| self.lower_type(ty));
                GenericArgument::Const(self.lowerer().lower_const_argument(expected_ty, c))
            }
            (
                GenericParameterDefinitionKind::Type { .. },
                hir::TypeArgument::AssociatedType(_, ty),
            )
            | (
                GenericParameterDefinitionKind::Const { .. },
                hir::TypeArgument::AssociatedType(_, ty),
            ) => {
                // Associated types in generic arguments (e.g. List<Item=int>) are handled earlier
                // by stripping them from the positional arguments list.
                // If we reach here, it's structurally invalid or handled elsewhere.
                // For now, check the type to be safe.
                // The original code had `self.lower_type(ty)` here, but the instruction
                // implies `self.lowerer.lower_type(ty)` and `self.check_type(ty)`.
                // Given the context of `lower_value_path_explicit_arg` and the existing
                // `lower_type` calls, I'll stick to `self.lower_type(ty)` for consistency
                // and avoid introducing `self.lowerer` directly without further context.
                // Also, `check_type` is not part of the original `lower_value_path_explicit_arg`
                // function, so I'm omitting it to make the minimal change.
                GenericArgument::Type(self.lower_type(ty))
            }
            (GenericParameterDefinitionKind::Type { .. }, hir::TypeArgument::Const(c)) => {
                gcx.dcx()
                    .emit_error("expected type argument".into(), Some(c.value.span));
                GenericArgument::Type(gcx.types.error)
            }
            (GenericParameterDefinitionKind::Const { ty, .. }, hir::TypeArgument::Type(ty_arg)) => {
                let expected_ty = gcx
                    .try_generic_const_param_ty(param.id)
                    .unwrap_or_else(|| self.lower_type(ty));
                if let Some(param) = self.const_param_from_type_arg(ty_arg) {
                    if param.ty != expected_ty
                        && param.ty != gcx.types.error
                        && expected_ty != gcx.types.error
                    {
                        let message = format!(
                            "const argument does not match parameter type '{}'",
                            expected_ty.format(gcx)
                        );
                        gcx.dcx().emit_error(message, Some(ty_arg.span));
                        return GenericArgument::Const(self.lowerer().error_const());
                    }
                    return GenericArgument::Const(Const {
                        ty: expected_ty,
                        kind: param.kind,
                    });
                }

                gcx.dcx()
                    .emit_error("expected const argument".into(), Some(ty_arg.span));
                GenericArgument::Const(self.lowerer().error_const())
            }
        }
    }

    fn const_param_from_type_arg(&self, ty: &hir::Type) -> Option<Const<'ctx>> {
        let hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path)) = &ty.kind else {
            return None;
        };

        let hir::Resolution::Definition(param_id, DefinitionKind::ConstParameter) = path.resolution
        else {
            return None;
        };

        let gcx = self.gcx();
        let owner = gcx.definition_parent(param_id)?;
        let generics = gcx.generics_of(owner);
        let def = generics.parameters.iter().find(|p| p.id == param_id)?;

        let param = GenericParameter {
            index: def.index,
            name: def.name,
        };

        Some(Const {
            ty: gcx
                .try_generic_const_param_ty(param_id)
                .or_else(|| match &def.kind {
                    GenericParameterDefinitionKind::Const { ty, .. } => Some(self.lower_type(ty)),
                    _ => None,
                })?,
            kind: ConstKind::Param(param),
        })
    }

    fn lower_value_path_missing_arg(
        &self,
        param: &GenericParameterDefinition,
        span: Span,
        current_args: GenericArguments<'ctx>,
    ) -> GenericArgument<'ctx> {
        let gcx = self.gcx();
        match &param.kind {
            GenericParameterDefinitionKind::Type { default } => {
                if let Some(default) = default {
                    if self.can_infer() {
                        let infer_ty = self.ty_infer(Some(param), span);
                        let mut default_ty = gcx
                            .try_generic_type_default(param.id)
                            .unwrap_or_else(|| self.lower_type(default));
                        default_ty = instantiate_ty_with_args(gcx, default_ty, current_args);
                        self.register_default_fallback(
                            crate::sema::tycheck::solve::DefaultFallbackGoalData {
                                infer_var: GenericArgument::Type(infer_ty),
                                default: GenericArgument::Type(default_ty),
                                span,
                            },
                        );
                        GenericArgument::Type(infer_ty)
                    } else {
                        GenericArgument::Type(
                            gcx.try_generic_type_default(param.id)
                                .unwrap_or_else(|| self.lower_type(default)),
                        )
                    }
                } else {
                    GenericArgument::Type(self.ty_infer(Some(param), span))
                }
            }
            GenericParameterDefinitionKind::Const { ty, default } => {
                let expected_ty = gcx
                    .try_generic_const_param_ty(param.id)
                    .unwrap_or_else(|| self.lower_type(ty));
                if let Some(default) = default {
                    if self.can_infer() {
                        let infer_const = self.const_infer(expected_ty, Some(param), span);
                        let mut default_const =
                            gcx.try_generic_const_default(param.id).unwrap_or_else(|| {
                                self.lowerer().lower_const_argument(expected_ty, default)
                            });
                        default_const =
                            instantiate_const_with_args(gcx, default_const, current_args);
                        self.register_default_fallback(
                            crate::sema::tycheck::solve::DefaultFallbackGoalData {
                                infer_var: GenericArgument::Const(infer_const),
                                default: GenericArgument::Const(default_const),
                                span,
                            },
                        );
                        GenericArgument::Const(infer_const)
                    } else {
                        GenericArgument::Const(
                            gcx.try_generic_const_default(param.id).unwrap_or_else(|| {
                                self.lowerer().lower_const_argument(expected_ty, default)
                            }),
                        )
                    }
                } else {
                    if self.can_infer() {
                        GenericArgument::Const(self.const_infer(expected_ty, Some(param), span))
                    } else {
                        gcx.dcx()
                            .emit_error("missing const argument".into(), Some(span));
                        GenericArgument::Const(self.lowerer().error_const())
                    }
                }
            }
        }
    }

    fn instantiate_value_path(
        &self,
        node_id: NodeID,
        span: Span,
        resolution: &hir::Resolution,
        instantiation_args: Option<GenericArguments<'ctx>>,
        expectation: Option<Ty<'ctx>>,
        allow_unsafe_callable_values: bool,
        prefer_async: Option<bool>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        if matches!(resolution, hir::Resolution::Error) {
            return Ty::error(self.gcx());
        }

        let ty = self.synth_identifier_expression(
            node_id,
            span,
            resolution,
            expectation,
            instantiation_args,
            allow_unsafe_callable_values,
            prefer_async,
            cs,
        );

        if let Some(def_id) = self.value_path_def_id(resolution) {
            let generics = self.gcx().generics_of(def_id);
            if !generics.is_empty() {
                if let Some(args) = instantiation_args {
                    cs.record_instantiation(node_id, args);
                    cs.add_constraints_for_def(def_id, Some(args), span);
                    if ty.needs_instantiation() {
                        return instantiate_ty_with_args(self.gcx(), ty, args);
                    }
                    return ty;
                }

                if ty.needs_instantiation() {
                    let args = cs.infer_cx.fresh_args_for_def(def_id, span);
                    let instantiated = instantiate_ty_with_args(self.gcx(), ty, args);
                    cs.record_instantiation(node_id, args);
                    cs.add_constraints_for_def(def_id, Some(args), span);
                    return instantiated;
                }
            }
        }

        ty
    }
}

impl<'ctx> Checker<'ctx> {
    fn synth_path_expression_with_policy(
        &self,
        expression: &hir::Expression,
        path: &hir::ResolvedPath,
        expectation: Option<Ty<'ctx>>,
        allow_unsafe_callable_values: bool,
        prefer_async: Option<bool>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let (resolution, base_args) =
            self.resolve_value_path_resolution_with_args(path, expression.span, true, cs);
        self.record_value_path_resolution(expression.id, &resolution);
        let segment = match path {
            hir::ResolvedPath::Resolved(path) => {
                path.segments.last().expect("path must have segments")
            }
            hir::ResolvedPath::Relative(_, segment) => segment,
        };
        let instantiation_args =
            self.lower_value_path_instantiation_args(&resolution, segment, base_args);
        // Note: For relative paths like `Optional.some`, we don't need to add type constraints
        // for the base type `Optional` since it's only used for name resolution, not as a value.
        // Adding constraints here creates spurious type variables that cause inference failures.
        self.instantiate_value_path(
            expression.id,
            expression.span,
            &resolution,
            instantiation_args,
            expectation,
            allow_unsafe_callable_values,
            prefer_async,
            cs,
        )
    }

    fn synth_path_expression(
        &self,
        expression: &hir::Expression,
        path: &hir::ResolvedPath,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        self.synth_path_expression_with_policy(expression, path, expectation, false, None, cs)
    }

    fn synth_member_expression(
        &self,
        expression: &hir::Expression,
        target: &hir::Expression,
        name: &crate::span::Identifier,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Instance receiver (`value.member`) uses synthesized receiver type.
        let receiver_ty = self.synth_with_expectation(target, None, cs);
        if receiver_ty.is_error() {
            return Ty::error(self.gcx());
        }
        let receiver_can_mut_borrow = self.can_mutably_borrow_receiver(target, cs);
        let result_ty = cs.infer_cx.next_ty_var(expression.span);
        cs.add_goal(
            Goal::Member(MemberGoalData {
                node_id: expression.id,
                receiver_node: target.id,
                receiver: receiver_ty,
                receiver_can_mut_borrow,
                name: *name,
                result: result_ty,
                span: expression.span,
            }),
            expression.span,
        );

        self.defer_async_property_surface_check(expression.id, expression.span);

        if let Some(expectation) = expectation {
            cs.equal(expectation, result_ty, expression.span);
        }
        result_ty
    }

    fn synth_inferred_member_expression(
        &self,
        expression: &hir::Expression,
        name: &crate::span::Identifier,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let result_ty = cs.infer_cx.next_ty_var(expression.span);
        cs.add_goal(
            Goal::InferredStaticMember(InferredStaticMemberGoalData {
                node_id: expression.id,
                name: *name,
                expr_ty: result_ty,
                base_hint: expectation,
                allow_unsafe_callable_values: false,
                prefer_async: false,
                span: expression.span,
            }),
            expression.span,
        );

        if let Some(expectation) = expectation {
            cs.equal(expectation, result_ty, expression.span);
        }

        result_ty
    }

    fn synth_struct_literal(
        &self,
        expression: &hir::Expression,
        lit: &hir::StructLiteral,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let span = expression.span;

        // Lower path to type to hook up WF goals
        let type_span = match &lit.path {
            hir::ResolvedPath::Resolved(p) => p.span,
            hir::ResolvedPath::Relative(_, s) => s.span,
        };

        // Lower the struct type in inference mode so that:
        // - Omitted generic args get fresh inference variables (inferred from fields)
        // - Default fallbacks are registered for params with defaults
        let type_node = hir::Type {
            id: expression.id,
            kind: hir::TypeKind::Nominal(lit.path.clone()),
            span: type_span,
        };
        let struct_ty = self.lower_type(&type_node);
        let gcx = self.gcx();
        let is_struct = match struct_ty.kind() {
            TyKind::Adt(def, _) => gcx.definition_kind(def.id) == DefinitionKind::Struct,
            TyKind::Error => return struct_ty,
            _ => false,
        };
        if !is_struct {
            gcx.dcx().emit_error(
                format!("expected struct type, found {}", struct_ty.format(gcx)).into(),
                Some(type_span),
            );
            return Ty::error(gcx);
        }
        self.add_type_constraints(struct_ty, type_span, cs);

        // Synthesize fields
        let mut fields = Vec::with_capacity(lit.fields.len());
        let mut had_error = false;
        for field in &lit.fields {
            let ty = self.synth(&field.expression, cs);
            if ty.is_error() {
                had_error = true;
            }

            let (name, label_span) = if let Some(label) = &field.label {
                (label.identifier.symbol, label.span)
            } else {
                // Shorthand: extract name from expression
                match &field.expression.kind {
                    hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                        let seg = path.segments.last().expect("path must have segments");
                        (seg.identifier.symbol, seg.identifier.span)
                    }
                    _ => unreachable!(),
                }
            };

            fields.push(StructLiteralField {
                name,
                node_id: field.expression.id,
                ty,
                value_span: field.expression.span,
                label_span,
            });
        }

        if had_error {
            return Ty::error(gcx);
        }

        cs.add_goal(
            Goal::StructLiteral(StructLiteralGoalData {
                ty_span: type_span,
                span,
                struct_ty,
                fields,
            }),
            span,
        );

        struct_ty
    }
    fn synth_tuple_expression(
        &self,
        _: &hir::Expression,
        elements: &[Box<hir::Expression>],
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let expected_elements = if let Some(expectation) = expectation {
            if let TyKind::Tuple(tys) = expectation.kind() {
                Some(tys)
            } else {
                None
            }
        } else {
            None
        };

        let mut element_types = Vec::with_capacity(elements.len());
        let mut had_error = false;
        for (i, element) in elements.iter().enumerate() {
            let elem_expectation = expected_elements.and_then(|tys| tys.get(i).cloned());
            let ty = self.synth_with_expectation(element, elem_expectation, cs);
            if ty.is_error() {
                had_error = true;
            }
            element_types.push(ty);
        }

        if had_error {
            return Ty::error(self.gcx());
        }

        Ty::new(
            TyKind::Tuple(self.gcx().store.interners.intern_ty_list(element_types)),
            self.gcx(),
        )
    }

    fn synth_array_expression(
        &self,
        expression: &hir::Expression,
        elements: &[Box<hir::Expression>],
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let list_def_id = gcx.std_item_def(hir::StdItem::List);
        let (expected_elem, expected_array, expected_list) = if let Some(expectation) = expectation
        {
            match expectation.kind() {
                TyKind::Array { element, .. } => (Some(element), Some(expectation), None),
                TyKind::Adt(def, args) if Some(def.id) == list_def_id => {
                    let elem = match args.get(0) {
                        Some(GenericArgument::Type(ty)) => Some(*ty),
                        _ => None,
                    };
                    (elem, None, Some(expectation))
                }
                _ => (None, None, None),
            }
        } else {
            (None, None, None)
        };

        if expected_elem.map(|ty| ty.is_error()).unwrap_or(false) {
            return Ty::error(gcx);
        }

        let element_ty = expected_elem.unwrap_or_else(|| cs.infer_cx.next_ty_var(expression.span));
        let mut had_error = false;

        for elem in elements {
            let ty = self.synth_with_expectation(elem, Some(element_ty), cs);
            if ty.is_error() {
                had_error = true;
                continue;
            }
            cs.equal(element_ty, ty, elem.span);
        }

        if had_error {
            return Ty::error(gcx);
        }

        if let Some(expect) = expected_list {
            return expect;
        }

        let len_const = Const {
            ty: gcx.types.uint,
            kind: ConstKind::Value(ConstValue::Integer(elements.len() as i128)),
        };

        if let Some(expect) = expected_array {
            let arr_ty = Ty::new(
                TyKind::Array {
                    element: element_ty,
                    len: len_const,
                },
                gcx,
            );
            cs.equal(expect, arr_ty, expression.span);
            expect
        } else {
            Ty::new(
                TyKind::Array {
                    element: element_ty,
                    len: len_const,
                },
                gcx,
            )
        }
    }

    fn synth_repeat_expression(
        &self,
        expression: &hir::Expression,
        value: &hir::Expression,
        count: &hir::AnonConst,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        // Extract expected element type from array expectation to guide inference
        let expected_elem = expectation.and_then(|ty| match ty.kind() {
            TyKind::Array { element, .. } => Some(element),
            _ => None,
        });

        let elem_ty = self.synth_with_expectation(value, expected_elem, cs);
        if elem_ty.is_error() {
            return Ty::error(gcx);
        }

        let len_const = self.lowerer().lower_array_length(count);
        if !matches!(
            len_const.kind,
            ConstKind::Value(ConstValue::Integer(_)) | ConstKind::Param(_) | ConstKind::Infer(_)
        ) {
            if len_const.ty != gcx.types.error {
                gcx.dcx().emit_error(
                    "repeat expression count must be a known integer constant".into(),
                    Some(count.value.span),
                );
            }
            return Ty::error(gcx);
        }

        let array_ty = Ty::new(
            TyKind::Array {
                element: elem_ty,
                len: len_const,
            },
            gcx,
        );

        if let Some(expectation) = expectation {
            if let TyKind::Array { .. } = expectation.kind() {
                cs.equal(expectation, array_ty, expression.span);
                expectation
            } else {
                gcx.dcx().emit_error(
                    "repeat expressions are only valid for fixed-size array types".into(),
                    Some(expression.span),
                );
                array_ty
            }
        } else {
            array_ty
        }
    }

    fn synth_tuple_access_expression(
        &self,
        expression: &hir::Expression,
        receiver: &hir::Expression,
        index: &hir::AnonConst,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let idx_val = if let hir::ExpressionKind::Literal(hir::Literal::Integer { value, .. }) =
            &index.value.kind
        {
            *value as usize
        } else {
            unreachable!()
        };

        let receiver_ty = self.synth(receiver, cs);
        if receiver_ty.is_error() {
            return Ty::error(self.gcx());
        }
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        cs.add_goal(
            Goal::TupleAccess(TupleAccessGoalData {
                node_id: expression.id,
                receiver: receiver_ty,
                index: idx_val,
                result: result_ty,
                span: expression.span,
            }),
            expression.span,
        );

        if let Some(expectation) = expectation {
            cs.equal(expectation, result_ty, expression.span);
        }

        result_ty
    }
}

/// Context for tracking binding modes during pattern matching.
/// This enables "match ergonomics" - automatic dereferencing and binding mode adjustment.
struct PatternContext<'ctx> {
    /// Current default binding mode (starts as ByValue, becomes ByRef when auto-derefing)
    default_mode: hir::BindingMode,
    /// The adjusted scrutinee type after auto-derefs
    adjusted_ty: Ty<'ctx>,
}

impl<'ctx> PatternContext<'ctx> {
    fn new(scrutinee: Ty<'ctx>) -> Self {
        Self {
            default_mode: hir::BindingMode::ByValue,
            adjusted_ty: scrutinee,
        }
    }

    /// Update binding mode when matching a reference with a non-reference pattern.
    /// This implements the match ergonomics rules.
    fn adjust_for_reference(&mut self, mutability: hir::Mutability, inner_ty: Ty<'ctx>) {
        self.default_mode = match (self.default_mode, mutability) {
            // If already ByRef, stay ByRef (don't upgrade to ByRef(Mutable))
            (hir::BindingMode::ByRef(_), hir::Mutability::Mutable) => self.default_mode,
            // Otherwise, match the reference's mutability
            (_, mutability) => hir::BindingMode::ByRef(mutability),
        };
        self.adjusted_ty = inner_ty;
    }

    /// Reset to ByValue mode (when encountering an explicit reference pattern)
    fn reset_to_move(&mut self) {
        self.default_mode = hir::BindingMode::ByValue;
    }
}

impl<'ctx> Checker<'ctx> {
    /// Entry point for pattern checking. Creates a PatternContext and delegates to check_pattern_with_context.
    fn check_pattern(
        &self,
        pattern: &hir::Pattern,
        scrutinee: Ty<'ctx>,
        scrutinee_node_id: NodeID,
        cs: &mut Cs<'ctx>,
    ) {
        let mut ctx = PatternContext::new(scrutinee);
        self.check_pattern_with_context(pattern, &mut ctx, scrutinee_node_id, cs);
    }

    /// Handles automatic dereferencing (match ergonomics).
    /// If the scrutinee is a reference and the pattern is not a reference pattern,
    /// automatically dereference and adjust the binding mode.
    /// Records Dereference adjustments for each auto-deref.
    fn check_pattern_with_context(
        &self,
        pattern: &hir::Pattern,
        ctx: &mut PatternContext<'ctx>,
        scrutinee_node_id: NodeID,
        cs: &mut Cs<'ctx>,
    ) {
        use crate::sema::tycheck::solve::Adjustment;

        let pattern_uses_rest = match &pattern.kind {
            hir::PatternKind::Tuple(patterns, _) => patterns
                .iter()
                .any(|pattern| matches!(pattern.kind, hir::PatternKind::Rest)),
            hir::PatternKind::PathTuple { fields, .. } => fields
                .iter()
                .any(|pattern| matches!(pattern.kind, hir::PatternKind::Rest)),
            _ => false,
        };
        if pattern_uses_rest {
            if let Some(scrutinee_ty) = cs.expr_ty(scrutinee_node_id) {
                let resolved = cs.infer_cx.resolve_vars_if_possible(scrutinee_ty);
                if !resolved.is_infer() {
                    ctx.adjusted_ty = resolved;
                }
            }
        }

        // Auto-deref loop: if scrutinee is &T and pattern is NOT &pat, auto-deref
        let mut adjustments = Vec::new();
        while let TyKind::Reference(inner_ty, mutability) =
            cs.infer_cx.resolve_vars_if_possible(ctx.adjusted_ty).kind()
        {
            // Don't auto-deref if this is an explicit reference pattern, or if it's a binding/wildcard
            // which should consume the reference as-is (fixing a double-reference issue in MIR)
            if matches!(
                pattern.kind,
                hir::PatternKind::Reference { .. }
                    | hir::PatternKind::Binding { .. }
                    | hir::PatternKind::Wildcard
                    | hir::PatternKind::Rest
            ) {
                break;
            }

            // Record the dereference adjustment
            adjustments.push(Adjustment::Dereference);

            // Auto-deref: adjust the type and binding mode
            ctx.adjust_for_reference(mutability, inner_ty);
        }

        // Record all adjustments on the scrutinee expression
        if !adjustments.is_empty() {
            self.results
                .borrow_mut()
                .record_node_adjustments(scrutinee_node_id, adjustments);
        }

        // Now check the pattern against the adjusted type
        self.check_pattern_inner(pattern, ctx, cs);
    }

    /// The actual pattern checking logic (renamed from check_pattern_structure).
    /// Now takes a PatternContext to track binding modes.
    fn check_pattern_inner(
        &self,
        pattern: &hir::Pattern,
        ctx: &mut PatternContext<'ctx>,
        cs: &mut Cs<'ctx>,
    ) {
        cs.record_expr_ty(pattern.id, ctx.adjusted_ty);
        match &pattern.kind {
            hir::PatternKind::Wildcard => {}
            hir::PatternKind::Rest => {}
            hir::PatternKind::Binding { mode, .. } => {
                let binding = self.get_local(pattern.id);

                // Determine the actual binding mode:
                // If the pattern has an explicit mode (not ByValue), use it.
                // Otherwise, use the default mode from the context (for match ergonomics).
                let actual_mode = if *mode == hir::BindingMode::ByValue {
                    ctx.default_mode
                } else {
                    *mode
                };

                // Compute the binding's type based on the binding mode
                let binding_ty = match actual_mode {
                    hir::BindingMode::ByValue => ctx.adjusted_ty,
                    hir::BindingMode::ByRef(mutability) => {
                        let gcx = self.gcx();
                        Ty::new(TyKind::Reference(ctx.adjusted_ty, mutability), gcx)
                    }
                };

                // Record the inferred binding mode for later phases (THIR, MIR)
                self.results
                    .borrow_mut()
                    .record_binding_mode(pattern.id, actual_mode);

                cs.equal(binding_ty, binding.ty, pattern.span);
            }
            hir::PatternKind::Tuple(pats, _) => {
                let has_rest = pats
                    .iter()
                    .any(|pat| matches!(pat.kind, hir::PatternKind::Rest));
                if has_rest {
                    let resolved_scrutinee = cs.infer_cx.resolve_vars_if_possible(ctx.adjusted_ty);
                    let elem_tys = match resolved_scrutinee.kind() {
                        TyKind::Tuple(items) => items.to_vec(),
                        TyKind::Error => return,
                        _ => {
                            self.gcx().dcx().emit_error(
                                format!(
                                    "rest pattern requires a tuple scrutinee with known arity, found `{}`",
                                    resolved_scrutinee.format(self.gcx())
                                )
                                .into(),
                                Some(pattern.span),
                            );
                            return;
                        }
                    };

                    let Some(field_mapping) = self.compute_pattern_field_mapping(
                        pats,
                        elem_tys.len(),
                        "tuple pattern",
                        pattern.span,
                    ) else {
                        return;
                    };

                    let tuple_ty = Ty::new(
                        TyKind::Tuple(self.gcx().store.interners.intern_ty_list(elem_tys.clone())),
                        self.gcx(),
                    );
                    cs.record_expr_ty(pattern.id, tuple_ty);
                    cs.equal(ctx.adjusted_ty, tuple_ty, pattern.span);

                    for (pat_index, field_index) in field_mapping {
                        let mut sub_ctx = PatternContext::new(elem_tys[field_index]);
                        sub_ctx.default_mode = ctx.default_mode;
                        self.check_pattern_with_context(
                            &pats[pat_index],
                            &mut sub_ctx,
                            pats[pat_index].id,
                            cs,
                        );
                    }
                    return;
                }

                let mut elem_tys = Vec::with_capacity(pats.len());
                for _ in pats {
                    elem_tys.push(cs.infer_cx.next_ty_var(pattern.span));
                }

                let tuple_ty = Ty::new(
                    TyKind::Tuple(self.gcx().store.interners.intern_ty_list(elem_tys.clone())),
                    self.gcx(),
                );
                cs.record_expr_ty(pattern.id, tuple_ty);
                cs.equal(ctx.adjusted_ty, tuple_ty, pattern.span);

                for (i, pat) in pats.iter().enumerate() {
                    let mut sub_ctx = PatternContext::new(elem_tys[i]);
                    sub_ctx.default_mode = ctx.default_mode;
                    self.check_pattern_with_context(pat, &mut sub_ctx, pat.id, cs);
                }
            }
            hir::PatternKind::Member(path) => {
                let Some((variant, enum_ty)) = self.resolve_enum_variant_pattern(
                    ctx.adjusted_ty,
                    pattern.id,
                    path,
                    pattern.span,
                    cs,
                ) else {
                    return;
                };

                if !matches!(variant.kind, crate::sema::models::EnumVariantKind::Unit) {
                    self.gcx().dcx().emit_error(
                        format!(
                            "enum variant '{}' requires tuple fields",
                            self.gcx().symbol_text(variant.name)
                        )
                        .into(),
                        Some(pattern.span),
                    );
                    return;
                }

                cs.equal(ctx.adjusted_ty, enum_ty, pattern.span);
            }
            hir::PatternKind::PathTuple { path, fields, .. } => {
                let Some((variant, enum_ty, variant_fields)) = self
                    .resolve_enum_tuple_variant_pattern(
                        ctx.adjusted_ty,
                        pattern.id,
                        path,
                        pattern.span,
                        cs,
                    )
                else {
                    return;
                };

                let variant_name = self.gcx().symbol_text(variant.name);
                let context = format!("enum variant '{}'", variant_name);
                let Some(field_mapping) = self.compute_pattern_field_mapping(
                    fields,
                    variant_fields.len(),
                    &context,
                    pattern.span,
                ) else {
                    return;
                };

                cs.equal(ctx.adjusted_ty, enum_ty, pattern.span);

                for (pat_index, field_index) in field_mapping {
                    let mut sub_ctx = PatternContext::new(variant_fields[field_index].ty);
                    sub_ctx.default_mode = ctx.default_mode;
                    self.check_pattern_with_context(
                        &fields[pat_index],
                        &mut sub_ctx,
                        fields[pat_index].id,
                        cs,
                    );
                }
            }
            hir::PatternKind::Or(patterns, _) => {
                for pat in patterns {
                    let mut sub_ctx = PatternContext::new(ctx.adjusted_ty);
                    sub_ctx.default_mode = ctx.default_mode;
                    self.check_pattern_with_context(pat, &mut sub_ctx, pat.id, cs);
                }
            }
            hir::PatternKind::Literal(literal) => {
                let lit_ty = self.synth_expression_literal(literal, pattern.span, None, cs);
                cs.equal(ctx.adjusted_ty, lit_ty, pattern.span);
            }
            hir::PatternKind::Reference { pattern, mutable } => {
                let gcx = self.gcx();
                // The scrutinee must be a reference type
                let inner_ty = match cs.infer_cx.resolve_vars_if_possible(ctx.adjusted_ty).kind() {
                    TyKind::Reference(inner, scrutinee_mut) => {
                        // Check mutability compatibility:
                        // Cannot match &mut pattern against immutable reference
                        if *mutable == hir::Mutability::Mutable
                            && scrutinee_mut != hir::Mutability::Mutable
                        {
                            gcx.dcx().emit_error(
                                "cannot match `&mut` pattern against immutable reference".into(),
                                Some(pattern.span),
                            );
                            return;
                        }
                        inner
                    }
                    TyKind::Error => return,
                    _ => {
                        gcx.dcx().emit_error(
                            format!(
                                "reference pattern requires reference type, found `{}`",
                                ctx.adjusted_ty.format(gcx)
                            )
                            .into(),
                            Some(pattern.span),
                        );
                        return;
                    }
                };
                // Recursively check the inner pattern against the dereferenced type
                // Reset binding mode to ByValue for explicit reference patterns
                ctx.reset_to_move();
                ctx.adjusted_ty = inner_ty;
                self.check_pattern_inner(pattern, ctx, cs);
            }
        }
    }

    fn compute_pattern_field_mapping(
        &self,
        patterns: &[hir::Pattern],
        field_count: usize,
        context: &str,
        span: Span,
    ) -> Option<Vec<(usize, usize)>> {
        let rest_positions: Vec<usize> = patterns
            .iter()
            .enumerate()
            .filter_map(|(index, pattern)| {
                if matches!(pattern.kind, hir::PatternKind::Rest) {
                    Some(index)
                } else {
                    None
                }
            })
            .collect();

        if rest_positions.len() > 1 {
            self.gcx().dcx().emit_error(
                format!("rest pattern (`..`) can appear at most once in {}", context).into(),
                Some(span),
            );
            return None;
        }

        let Some(rest_index) = rest_positions.first().copied() else {
            if patterns.len() != field_count {
                self.gcx().dcx().emit_error(
                    format!(
                        "expected {} field(s) in {}, got {}",
                        field_count,
                        context,
                        patterns.len()
                    )
                    .into(),
                    Some(span),
                );
                return None;
            }

            return Some((0..field_count).map(|index| (index, index)).collect());
        };

        let explicit_field_count = patterns.len() - 1;
        if explicit_field_count > field_count {
            self.gcx().dcx().emit_error(
                format!(
                    "expected at most {} explicit field(s) in {}, got {}",
                    field_count, context, explicit_field_count
                )
                .into(),
                Some(span),
            );
            return None;
        }

        let trailing_pattern_count = patterns.len() - rest_index - 1;
        let trailing_field_start = field_count - trailing_pattern_count;

        let mut mapping = Vec::with_capacity(explicit_field_count);
        for index in 0..rest_index {
            mapping.push((index, index));
        }
        for offset in 0..trailing_pattern_count {
            let pattern_index = rest_index + 1 + offset;
            mapping.push((pattern_index, trailing_field_start + offset));
        }

        Some(mapping)
    }

    fn resolve_enum_variant_pattern(
        &self,
        scrutinee: Ty<'ctx>,
        id: NodeID,
        path: &hir::PatternPath,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Option<(crate::sema::models::EnumVariant<'ctx>, Ty<'ctx>)> {
        match path {
            hir::PatternPath::Qualified { path } => {
                // Note: Similar to value paths, we don't need to add type constraints
                // for the base type in relative patterns like `Optional.none`.
                // The base type is only used for name resolution.
                let (resolution, base_args) =
                    self.resolve_value_path_resolution_with_args(path, span, true, cs);
                self.record_value_path_resolution(id, &resolution);
                self.resolve_enum_variant_from_resolution(
                    scrutinee, resolution, span, cs, base_args,
                )
            }
            hir::PatternPath::Inferred {
                name,
                span: inferred_span,
            } => {
                self.resolve_inferred_enum_variant_pattern(scrutinee, id, name, *inferred_span, cs)
            }
        }
    }

    fn resolve_enum_tuple_variant_pattern(
        &self,
        scrutinee: Ty<'ctx>,
        id: NodeID,
        path: &hir::PatternPath,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Option<(
        crate::sema::models::EnumVariant<'ctx>,
        Ty<'ctx>,
        &'ctx [crate::sema::models::EnumVariantField<'ctx>],
    )> {
        let (variant, enum_ty) =
            self.resolve_enum_variant_pattern(scrutinee, id, path, span, cs)?;
        let crate::sema::models::EnumVariantKind::Tuple(fields) = variant.kind else {
            self.gcx().dcx().emit_error(
                format!(
                    "enum variant '{}' does not take tuple fields",
                    self.gcx().symbol_text(variant.name)
                )
                .into(),
                Some(span),
            );
            return None;
        };

        Some((variant, enum_ty, fields))
    }

    fn resolve_enum_variant_from_resolution(
        &self,
        scrutinee: Ty<'ctx>,
        resolution: hir::Resolution,
        span: Span,
        cs: &mut Cs<'ctx>,
        base_args: Option<crate::sema::models::GenericArguments<'ctx>>,
    ) -> Option<(crate::sema::models::EnumVariant<'ctx>, Ty<'ctx>)> {
        let gcx = self.gcx();
        let (ctor_id, kind) = match resolution {
            hir::Resolution::Definition(ctor_id, kind) => (ctor_id, kind),
            hir::Resolution::StdItem(item) => {
                let Some(ctor_id) = gcx.std_item_def(item) else {
                    gcx.dcx()
                        .emit_error("expected enum variant pattern".into(), Some(span));
                    return None;
                };
                (ctor_id, gcx.definition_kind(ctor_id))
            }
            hir::Resolution::Error => return None,
            _ => {
                gcx.dcx()
                    .emit_error("expected enum variant pattern".into(), Some(span));
                return None;
            }
        };

        if !matches!(kind, DefinitionKind::VariantConstructor(..)) {
            gcx.dcx()
                .emit_error("expected enum variant pattern".into(), Some(span));
            return None;
        }

        let Some(parent_id) = gcx.definition_parent(ctor_id) else {
            gcx.dcx()
                .emit_error("enum variant is missing a parent".into(), Some(span));
            return None;
        };

        let enum_id = match gcx.definition_kind(parent_id) {
            DefinitionKind::Enum => parent_id,
            DefinitionKind::Variant => {
                let Some(enum_id) = gcx.definition_parent(parent_id) else {
                    gcx.dcx()
                        .emit_error("enum variant is missing a parent".into(), Some(span));
                    return None;
                };
                enum_id
            }
            _ => {
                gcx.dcx()
                    .emit_error("enum variant is missing a parent".into(), Some(span));
                return None;
            }
        };

        let def = gcx.with_type_database(enum_id.package(), |db| {
            db.def_to_enum_def.get(&enum_id).cloned()
        });
        let Some(def) = def else {
            gcx.dcx()
                .emit_error("missing enum definition for variant".into(), Some(span));
            return None;
        };

        let args = if let Some(base_args) = base_args {
            base_args
        } else {
            match cs.infer_cx.resolve_vars_if_possible(scrutinee).kind() {
                TyKind::Adt(adt_def, args) if adt_def.id == enum_id => {
                    if !args.is_empty() || gcx.generics_of(enum_id).is_empty() {
                        args
                    } else {
                        cs.infer_cx.fresh_args_for_def(enum_id, span)
                    }
                }
                _ => cs.infer_cx.fresh_args_for_def(enum_id, span),
            }
        };

        let enum_ty = Ty::new(TyKind::Adt(def.adt_def, args), gcx);
        cs.add_constraints_for_def(enum_id, Some(args), span);
        let def = crate::sema::tycheck::utils::instantiate::instantiate_enum_definition_with_args(
            gcx, &def, args,
        );

        let variant = def
            .variants
            .iter()
            .find(|v| v.ctor_def_id == ctor_id)
            .cloned();

        let Some(variant) = variant else {
            gcx.dcx().emit_error(
                "enum variant constructor does not belong to this enum".into(),
                Some(span),
            );
            return None;
        };

        if !gcx.is_definition_visible(variant.ctor_def_id, self.current_def) {
            gcx.dcx()
                .emit_error("enum variant is not visible here".into(), Some(span));
            return None;
        }

        cs.equal(scrutinee, enum_ty, span);
        Some((variant, enum_ty))
    }

    /// Resolves an inferred pattern like `.some(value)` by looking up the variant by name
    /// from the scrutinee's concrete type. Requires the scrutinee to be a fully resolved enum type.
    fn resolve_inferred_enum_variant_pattern(
        &self,
        scrutinee: Ty<'ctx>,
        id: NodeID,
        name: &crate::span::Identifier,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Option<(crate::sema::models::EnumVariant<'ctx>, Ty<'ctx>)> {
        let gcx = self.gcx();
        let scrutinee = cs.infer_cx.resolve_vars_if_possible(scrutinee);
        // Scrutinee must be a concrete ADT type
        let TyKind::Adt(adt_def, args) = scrutinee.kind() else {
            gcx.dcx().emit_error(
                format!(
                    "inferred pattern '.{}' requires an enum type, found '{}'",
                    gcx.symbol_text(name.symbol),
                    scrutinee.format(gcx)
                )
                .into(),
                Some(span),
            );
            return None;
        };

        let enum_id = adt_def.id;

        // Must be an enum, not a struct
        if gcx.definition_kind(enum_id) != DefinitionKind::Enum {
            gcx.dcx().emit_error(
                format!(
                    "inferred pattern '.{}' can only be used with enum types, found struct '{}'",
                    gcx.symbol_text(name.symbol),
                    scrutinee.format(gcx)
                )
                .into(),
                Some(span),
            );
            return None;
        }

        // Get the enum definition
        let def = gcx.get_enum_definition(enum_id);

        // Find variant by name
        let variant = def.variants.iter().find(|v| v.name == name.symbol).cloned();

        let Some(variant) = variant else {
            gcx.dcx().emit_error(
                format!(
                    "enum '{}' has no variant named '{}'",
                    gcx.symbol_text(gcx.definition_ident(enum_id).symbol),
                    gcx.symbol_text(name.symbol)
                )
                .into(),
                Some(span),
            );
            return None;
        };

        // Check visibility
        if !gcx.is_definition_visible(variant.ctor_def_id, self.current_def) {
            gcx.dcx()
                .emit_error("enum variant is not visible here".into(), Some(span));
            return None;
        }

        // Record the resolution
        let kind = gcx.definition_kind(variant.ctor_def_id);
        self.record_value_path_resolution(
            id,
            &hir::Resolution::Definition(variant.ctor_def_id, kind),
        );

        // Instantiate the variant with the scrutinee's type arguments
        let enum_ty = Ty::new(TyKind::Adt(adt_def, args), gcx);
        cs.add_constraints_for_def(enum_id, Some(args), span);
        let instantiated_def =
            crate::sema::tycheck::utils::instantiate::instantiate_enum_definition_with_args(
                gcx, def, args,
            );

        // Find the instantiated variant
        let instantiated_variant = instantiated_def
            .variants
            .iter()
            .find(|v| v.ctor_def_id == variant.ctor_def_id)
            .cloned();

        let Some(instantiated_variant) = instantiated_variant else {
            gcx.dcx().emit_error(
                "internal error: variant not found after instantiation".into(),
                Some(span),
            );
            return None;
        };

        cs.equal(scrutinee, enum_ty, span);
        Some((instantiated_variant, enum_ty))
    }

    /// Check if a type is Optional[T]
    fn is_optional_type(&self, ty: Ty<'ctx>) -> bool {
        let TyKind::Adt(def, _) = ty.kind() else {
            return false;
        };
        let Some(opt_id) = self.gcx().std_item_def(hir::StdItem::Optional) else {
            return false;
        };
        def.id == opt_id
    }

    fn is_result_type(&self, ty: Ty<'ctx>) -> bool {
        let TyKind::Adt(def, _) = ty.kind() else {
            return false;
        };
        let Some(result_id) = self.gcx().std_item_def(hir::StdItem::Result) else {
            return false;
        };
        def.id == result_id
    }

    fn task_inner_type(&self, ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        let Some(task_id) = self.gcx().std_item_def(hir::StdItem::Task) else {
            return None;
        };
        if def.id != task_id {
            return None;
        }
        (*args.first()?).ty()
    }

    fn with_return_ty<R>(&self, return_ty: Option<Ty<'ctx>>, f: impl FnOnce() -> R) -> R {
        let prev = self.return_ty.replace(return_ty);
        let result = f();
        self.return_ty.set(prev);
        result
    }

    fn finish_async_call_surface_check(
        &self,
        node_id: NodeID,
        span: Span,
        result_ty: Ty<'ctx>,
    ) -> Ty<'ctx> {
        if self.results.borrow().is_async_call(node_id)
            && self.direct_await_operand.get() != Some(node_id)
        {
            self.gcx()
                .dcx()
                .emit_error("async calls must be immediately awaited".into(), Some(span));
            return Ty::error(self.gcx());
        }

        result_ty
    }

    fn resolved_async_call_status(&self, node_id: NodeID, cs: Option<&Cs<'ctx>>) -> Option<bool> {
        if self.results.borrow().is_async_call(node_id) {
            return Some(true);
        }

        {
            let results = self.results.borrow();
            if let Some(def_id) = results.overload_source(node_id) {
                return Some(self.gcx().definition_is_async(def_id));
            }

            if let Some(call_info) = results.interface_call(node_id) {
                return Some(self.gcx().definition_is_async(call_info.method_id));
            }
        }

        let Some(cs) = cs else {
            return None;
        };

        if let Some(def_id) = cs.resolved_overload_sources().get(&node_id).copied() {
            return Some(self.gcx().definition_is_async(def_id));
        }

        if let Some(call_info) = cs.resolved_interface_calls().get(&node_id).copied() {
            return Some(self.gcx().definition_is_async(call_info.method_id));
        }

        None
    }

    fn resolved_async_property_status(
        &self,
        node_id: NodeID,
        cs: Option<&Cs<'ctx>>,
    ) -> Option<bool> {
        if let Some(property) = self.results.borrow().property_read(node_id) {
            return Some(property.getter_is_async);
        }

        let Some(cs) = cs else {
            return None;
        };

        cs.resolved_property_reads()
            .get(&node_id)
            .map(|property| property.getter_is_async)
    }

    fn finalize_deferred_async_call_surface_checks(&self, cs: &Cs<'ctx>) {
        let pending: Vec<_> = self
            .pending_async_surface_checks
            .borrow_mut()
            .drain(..)
            .collect();
        let mut unresolved = Vec::new();

        for pending in pending {
            match self.resolved_async_call_status(pending.node_id, Some(cs)) {
                Some(true) => {
                    self.results.borrow_mut().record_async_call(pending.node_id);
                    if !pending.directly_awaited {
                        self.gcx().dcx().emit_error(
                            "async calls must be immediately awaited".into(),
                            Some(pending.span),
                        );
                    }
                }
                Some(false) => {}
                None => unresolved.push(pending),
            }
        }

        if !unresolved.is_empty() {
            self.pending_async_surface_checks
                .borrow_mut()
                .extend(unresolved);
        }
    }

    fn finalize_deferred_async_property_surface_checks(&self, cs: &Cs<'ctx>) {
        let pending: Vec<_> = self
            .pending_async_property_surface_checks
            .borrow_mut()
            .drain(..)
            .collect();

        for pending in pending {
            match self.resolved_async_property_status(pending.node_id, Some(cs)) {
                Some(true) => {
                    self.results.borrow_mut().record_async_call(pending.node_id);
                    if !pending.directly_awaited {
                        self.gcx().dcx().emit_error(
                            "async calls must be immediately awaited".into(),
                            Some(pending.span),
                        );
                    }
                }
                Some(false) => {}
                None => {}
            }
        }
    }

    fn type_is_async_callable(&self, ty: Ty<'ctx>) -> bool {
        self.async_callable_input_count(ty).is_some()
    }

    fn ty_is_known_async_callable(&self, ty: Ty<'ctx>) -> bool {
        matches!(
            ty.kind(),
            TyKind::Closure {
                kind: crate::sema::models::ClosureKind::AsyncFn
                    | crate::sema::models::ClosureKind::AsyncFnMut
                    | crate::sema::models::ClosureKind::AsyncFnOnce,
                ..
            }
        )
    }

    fn async_callable_input_count(&self, ty: Ty<'ctx>) -> Option<usize> {
        match ty.kind() {
            TyKind::Closure { kind, inputs, .. } => matches!(
                kind,
                crate::sema::models::ClosureKind::AsyncFn
                    | crate::sema::models::ClosureKind::AsyncFnMut
                    | crate::sema::models::ClosureKind::AsyncFnOnce
            )
            .then_some(inputs.len()),
            TyKind::Parameter(param) => {
                let gcx = self.gcx();
                let Some(async_fn_def) = gcx.std_item_def(hir::StdItem::AsyncFn) else {
                    return None;
                };
                let async_fn_mut_def = gcx.std_item_def(hir::StdItem::AsyncFnMut);
                let async_fn_once_def = gcx.std_item_def(hir::StdItem::AsyncFnOnce);
                crate::sema::tycheck::constraints::canonical_constraints_of(gcx, self.current_def)
                    .into_iter()
                    .find_map(|constraint| {
                        let crate::sema::models::Constraint::Bound {
                            ty: bound_ty,
                            interface,
                        } = constraint.value
                        else {
                            return None;
                        };
                        let TyKind::Parameter(bound_param) = bound_ty.kind() else {
                            return None;
                        };
                        if bound_param.index != param.index
                            || bound_param.name != param.name
                            || (interface.id != async_fn_def
                                && Some(interface.id) != async_fn_mut_def
                                && Some(interface.id) != async_fn_once_def)
                        {
                            return None;
                        }

                        let args_ty = interface.arguments.get(1).and_then(|arg| arg.ty())?;
                        Some(match args_ty.kind() {
                            TyKind::Tuple(elem_tys) => elem_tys.len(),
                            _ => 1,
                        })
                    })
            }
            _ => None,
        }
    }

    fn optional_inner_type(&self, ty: Ty<'ctx>) -> Option<(GenericArguments<'ctx>, Ty<'ctx>)> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        let Some(opt_id) = self.gcx().std_item_def(hir::StdItem::Optional) else {
            return None;
        };
        if def.id != opt_id {
            return None;
        }
        let inner = (*args.first()?).ty()?;
        Some((args, inner))
    }

    fn result_inner_types(
        &self,
        ty: Ty<'ctx>,
    ) -> Option<(GenericArguments<'ctx>, Ty<'ctx>, Ty<'ctx>)> {
        if !self.is_result_type(ty) {
            return None;
        }
        let TyKind::Adt(_, args) = ty.kind() else {
            return None;
        };
        let ok_ty = args.get(0)?.ty()?;
        let err_ty = args.get(1)?.ty()?;
        Some((args, ok_ty, err_ty))
    }

    fn mk_optional_type(&self, inner: Ty<'ctx>) -> (Ty<'ctx>, GenericArguments<'ctx>) {
        let gcx = self.gcx();
        let opt_id = gcx
            .std_item_def(hir::StdItem::Optional)
            .expect("Optional type must exist");
        let enum_def = gcx.get_enum_definition(opt_id);
        let args = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(inner)]);
        let opt_ty = gcx
            .store
            .interners
            .intern_ty(TyKind::Adt(enum_def.adt_def, args));
        (opt_ty, args)
    }

    fn mark_pattern_bindings_error(&self, pattern: &hir::Pattern) {
        match &pattern.kind {
            hir::PatternKind::Binding { .. } => {
                self.finalize_local(pattern.id, self.gcx().types.error);
            }
            hir::PatternKind::Reference { pattern, .. } => {
                self.mark_pattern_bindings_error(pattern);
            }
            hir::PatternKind::Tuple(patterns, _)
            | hir::PatternKind::Or(patterns, _)
            | hir::PatternKind::PathTuple {
                fields: patterns, ..
            } => {
                for pat in patterns {
                    self.mark_pattern_bindings_error(pat);
                }
            }
            _ => {}
        }
    }

    /// Extract expected input types for closure parameter inference.
    /// Returns None if no expectation is available or it can't be extracted.
    fn extract_closure_expected_inputs(
        &self,
        expectation: Ty<'ctx>,
        cs: &mut Cs<'ctx>,
    ) -> Option<Vec<Ty<'ctx>>> {
        let expectation = cs.infer_cx.resolve_vars_if_possible(expectation);

        match expectation.kind() {
            // Direct closure type - use its inputs (this includes synthetic closures from Fn bounds)
            TyKind::Closure { inputs, .. } => Some(inputs.to_vec()),

            // Function pointer - use its inputs
            TyKind::FnPointer { inputs, .. } => Some(inputs.to_vec()),

            _ => None,
        }
    }

    /// Extract expected output type for closure return type inference.
    /// Returns None if no expectation is available or it can't be extracted.
    fn extract_closure_expected_output(
        &self,
        expectation: Ty<'ctx>,
        cs: &mut Cs<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let expectation = cs.infer_cx.resolve_vars_if_possible(expectation);

        match expectation.kind() {
            TyKind::Closure { output, .. } => Some(output),
            TyKind::FnPointer { output, .. } => Some(output),
            _ => None,
        }
    }

    /// Updates the global function signature for a closure with fully resolved types.
    ///
    /// This is critical because the initial signature created during closure synthesis may contain
    /// inference variables (e.g., `{var(N)}`). Codegen uses the global signature cache, so if we don't
    /// update it after type inference resolves these variables, `normalize_post_monomorphization` will panic.
    fn update_closure_signature(&self, closure_def_id: DefinitionID, closure_ty: Ty<'ctx>) {
        use crate::sema::models::{LabeledFunctionParameter, LabeledFunctionSignature};

        let TyKind::Closure {
            kind,
            inputs,
            output,
            ..
        } = closure_ty.kind()
        else {
            return;
        };

        let gcx = self.gcx();
        let old_sig = gcx.get_signature(closure_def_id);

        let self_ty = closure_self_ty(gcx, closure_ty, kind);

        let mut new_inputs = Vec::with_capacity(old_sig.inputs.len());

        // Handle self (first arg)
        if !old_sig.inputs.is_empty() {
            let old_self = &old_sig.inputs[0];
            new_inputs.push(LabeledFunctionParameter {
                ty: self_ty,
                ..*old_self
            });
        }

        // Handle explicit args
        // inputs (from closure_ty) corresponds to old_sig.inputs[1..]
        for (i, param_ty) in inputs.iter().enumerate() {
            // +1 for self
            if i + 1 < old_sig.inputs.len() {
                let old_param = &old_sig.inputs[i + 1];
                new_inputs.push(LabeledFunctionParameter {
                    ty: *param_ty,
                    ..*old_param
                });
            }
        }

        let new_sig = LabeledFunctionSignature {
            inputs: new_inputs,
            output: output, // resolved output from closure_ty
            ..old_sig.clone()
        };

        gcx.cache_signature(closure_def_id, new_sig);
    }
}

fn integer_literal_fits<'ctx>(value: u64, ty: Ty<'ctx>) -> bool {
    let value = value as u128;
    match ty.kind() {
        TyKind::UInt(kind) => value <= unsigned_max_u128(kind),
        TyKind::Int(kind) => value <= signed_nonnegative_max_u128(kind),
        _ => true,
    }
}

fn signed_nonnegative_max_u128(kind: IntTy) -> u128 {
    let bits = match kind {
        IntTy::ISize => isize::BITS,
        IntTy::I8 => 8,
        IntTy::I16 => 16,
        IntTy::I32 => 32,
        IntTy::I64 => 64,
    };
    (1u128 << (bits - 1)) - 1
}

fn unsigned_max_u128(kind: UIntTy) -> u128 {
    let bits = match kind {
        UIntTy::USize => usize::BITS,
        UIntTy::U8 => 8,
        UIntTy::U16 => 16,
        UIntTy::U32 => 32,
        UIntTy::U64 => 64,
    };

    if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

struct DefaultParamRefChecker<'a> {
    param_ids: &'a [NodeID],
    param_symbols: &'a [Symbol],
    found: bool,
}

impl<'a> hir::HirVisitor for DefaultParamRefChecker<'a> {
    fn visit_resolved_path(&mut self, node: &hir::ResolvedPath) -> Self::Result {
        if let hir::ResolvedPath::Resolved(path) = node {
            match path.resolution {
                hir::Resolution::LocalVariable(id) => {
                    if self.param_ids.contains(&id) {
                        self.found = true;
                    }
                }
                hir::Resolution::Error => {
                    if path
                        .segments
                        .iter()
                        .any(|segment| self.param_symbols.contains(&segment.identifier.symbol))
                    {
                        self.found = true;
                    }
                }
                _ => {}
            }
        }
        hir::walk_resolved_path(self, node)
    }
}

#[derive(Default, Clone, Copy)]
struct CaptureUsage {
    moved: bool,
    by_ref: Option<hir::Mutability>,
}

struct CaptureInfo {
    name: Symbol,
    usage: CaptureUsage,
}

enum UseContext {
    Value,
    Place,
    Borrow { mutable: bool },
}

fn closure_body_has_explicit_return(expr: &hir::Expression) -> bool {
    struct ReturnFinder {
        found: bool,
    }

    impl hir::HirVisitor for ReturnFinder {
        fn visit_expression(&mut self, node: &hir::Expression) {
            match &node.kind {
                hir::ExpressionKind::Return { .. } => {
                    self.found = true;
                }
                hir::ExpressionKind::Closure(_) => {}
                _ => hir::walk_expression(self, node),
            }
        }
    }

    let mut finder = ReturnFinder { found: false };
    finder.visit_expression(expr);
    finder.found
}

/// Collects free variable references from a closure body.
/// A "capture" is a local variable referenced in the closure body
/// that is not a closure parameter or locally declared.
struct CaptureCollector<'a, 'ctx> {
    /// IDs of closure parameters (these are NOT captures)
    param_ids: &'a rustc_hash::FxHashSet<NodeID>,
    /// IDs of variables declared inside the closure body (NOT captures)
    local_decls: rustc_hash::FxHashSet<NodeID>,
    /// Capture order (first-seen)
    order: Vec<NodeID>,
    /// Capture info keyed by NodeID
    info: rustc_hash::FxHashMap<NodeID, CaptureInfo>,
    /// Reference to the checker for accessing local bindings
    checker: &'a Checker<'ctx>,
    /// Adjustments recorded during type checking
    adjustments: &'a rustc_hash::FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
}

impl<'a, 'ctx> CaptureCollector<'a, 'ctx> {
    fn record_capture(&mut self, id: NodeID, name: Symbol, usage: CaptureUsage) {
        let entry = self.info.entry(id).or_insert_with(|| {
            self.order.push(id);
            CaptureInfo {
                name,
                usage: CaptureUsage::default(),
            }
        });
        if usage.moved {
            entry.usage.moved = true;
        }
        match (entry.usage.by_ref, usage.by_ref) {
            (_, Some(hir::Mutability::Mutable)) => {
                entry.usage.by_ref = Some(hir::Mutability::Mutable);
            }
            (None, Some(hir::Mutability::Immutable)) => {
                entry.usage.by_ref = Some(hir::Mutability::Immutable);
            }
            _ => {}
        }
    }

    fn capture_usage(
        &self,
        expr: &hir::Expression,
        ctx: UseContext,
        local_ty: Ty<'ctx>,
    ) -> CaptureUsage {
        match ctx {
            UseContext::Borrow { mutable } => CaptureUsage {
                moved: false,
                by_ref: Some(if mutable {
                    hir::Mutability::Mutable
                } else {
                    hir::Mutability::Immutable
                }),
            },
            UseContext::Place => CaptureUsage {
                moved: false,
                by_ref: Some(hir::Mutability::Mutable),
            },
            UseContext::Value => {
                if let Some(adjustments) = self.adjustments.get(&expr.id) {
                    if adjustments
                        .iter()
                        .any(|adj| matches!(adj, Adjustment::BorrowMutable))
                    {
                        return CaptureUsage {
                            moved: false,
                            by_ref: Some(hir::Mutability::Mutable),
                        };
                    }
                    if adjustments
                        .iter()
                        .any(|adj| matches!(adj, Adjustment::BorrowImmutable))
                    {
                        return CaptureUsage {
                            moved: false,
                            by_ref: Some(hir::Mutability::Immutable),
                        };
                    }
                }

                CaptureUsage {
                    moved: !self
                        .checker
                        .gcx()
                        .is_type_copyable_in_def(local_ty, self.checker.current_def),
                    by_ref: None,
                }
            }
        }
    }

    fn maybe_capture(&mut self, expr: &hir::Expression, path: &hir::ResolvedPath, ctx: UseContext) {
        let hir::ResolvedPath::Resolved(path) = path else {
            return;
        };
        let hir::Resolution::LocalVariable(id) = path.resolution else {
            return;
        };
        // Skip closure parameters
        if self.param_ids.contains(&id) {
            return;
        }
        // Skip variables declared inside this closure body
        if self.local_decls.contains(&id) {
            return;
        }
        let Some(binding) = self.checker.try_get_local(id) else {
            return;
        };

        let name = path
            .segments
            .last()
            .map(|s| s.identifier.symbol)
            .unwrap_or_else(|| self.checker.gcx().intern_symbol("_"));
        let usage = self.capture_usage(expr, ctx, binding.ty);
        self.record_capture(id, name, usage);
    }

    fn collect_block(&mut self, block: &hir::Block) {
        for stmt in &block.statements {
            self.collect_statement(stmt);
        }
        if let Some(tail) = block.tail.as_deref() {
            self.collect_expr(tail, UseContext::Value);
        }
    }

    fn collect_statement(&mut self, stmt: &hir::Statement) {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => {}
            hir::StatementKind::Expression(expr) => {
                self.collect_expr(expr, UseContext::Value);
            }
            hir::StatementKind::Variable(local) => {
                // First collect captures from the initializer (before registering the local)
                if let Some(init) = local.initializer.as_deref() {
                    self.collect_expr(init, UseContext::Value);
                }
                // Mark every binding introduced by this local pattern as scoped to the closure body.
                self.collect_pattern_bindings(&local.pattern);
            }
            hir::StatementKind::Loop { block, .. } => {
                self.collect_block(block);
            }
            hir::StatementKind::Defer(block) => {
                self.collect_block(block);
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                self.collect_expr(condition, UseContext::Value);
                self.collect_block(else_block);
            }
        }
    }

    fn collect_expr(&mut self, expr: &hir::Expression, ctx: UseContext) {
        match &expr.kind {
            hir::ExpressionKind::Literal(_) | hir::ExpressionKind::Malformed => {}
            hir::ExpressionKind::Closure(closure) => {
                // For nested closures, propagate their captures to our capture list.
                // The nested closure has already been type-checked (during body synthesis),
                // so its captures are cached.
                if let Some(nested_captures) =
                    self.checker.gcx().get_closure_captures(closure.def_id)
                {
                    for cap in &nested_captures.captures {
                        // Skip if this is one of our parameters
                        if self.param_ids.contains(&cap.source_id) {
                            continue;
                        }
                        // Skip if this is a local declared in our closure body
                        // (the nested closure can access it directly)
                        if self.local_decls.contains(&cap.source_id) {
                            continue;
                        }
                        // Skip if we can't find the binding (shouldn't happen)
                        if self.checker.try_get_local(cap.source_id).is_none() {
                            continue;
                        }
                        // Propagate the capture - the nested closure needs this variable,
                        // so we must capture it too to make it available
                        let usage = match cap.capture_kind {
                            crate::sema::models::CaptureKind::ByCopy => CaptureUsage::default(),
                            crate::sema::models::CaptureKind::ByRef { mutable } => CaptureUsage {
                                moved: false,
                                by_ref: Some(if mutable {
                                    hir::Mutability::Mutable
                                } else {
                                    hir::Mutability::Immutable
                                }),
                            },
                            crate::sema::models::CaptureKind::ByMove => CaptureUsage {
                                moved: true,
                                by_ref: None,
                            },
                        };
                        self.record_capture(cap.source_id, cap.name, usage);
                    }
                }
            }
            hir::ExpressionKind::Path(path) => {
                self.maybe_capture(expr, path, ctx);
            }
            hir::ExpressionKind::Member { target, .. } => {
                self.collect_expr(target, ctx);
            }
            hir::ExpressionKind::InferredMember { .. } => {}
            hir::ExpressionKind::Array(items) | hir::ExpressionKind::Tuple(items) => {
                for item in items {
                    self.collect_expr(item, UseContext::Value);
                }
            }
            hir::ExpressionKind::Repeat { value, .. } => {
                self.collect_expr(value, UseContext::Value);
            }
            hir::ExpressionKind::If(expr) => {
                self.collect_expr(&expr.condition, UseContext::Value);
                self.collect_expr(&expr.then_block, UseContext::Value);
                if let Some(else_block) = expr.else_block.as_deref() {
                    self.collect_expr(else_block, UseContext::Value);
                }
            }
            hir::ExpressionKind::Match(expr) => {
                self.collect_expr(&expr.value, UseContext::Value);
                for arm in &expr.arms {
                    let mut arm_bindings = Vec::new();
                    self.collect_pattern_binding_ids(&arm.pattern, &mut arm_bindings);
                    for binding_id in &arm_bindings {
                        self.local_decls.insert(*binding_id);
                    }
                    if let Some(guard) = arm.guard.as_deref() {
                        self.collect_expr(guard, UseContext::Value);
                    }
                    self.collect_expr(&arm.body, UseContext::Value);
                    for binding_id in arm_bindings {
                        self.local_decls.remove(&binding_id);
                    }
                }
            }
            hir::ExpressionKind::Return { value } => {
                if let Some(value) = value.as_deref() {
                    self.collect_expr(value, UseContext::Value);
                }
            }
            hir::ExpressionKind::Break { .. } | hir::ExpressionKind::Continue { .. } => {}
            hir::ExpressionKind::Call { callee, arguments } => {
                self.collect_expr(callee, UseContext::Value);
                for arg in arguments {
                    self.collect_expr(&arg.expression, UseContext::Value);
                }
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                arguments,
                ..
            } => {
                self.collect_expr(receiver, UseContext::Value);
                for arg in arguments {
                    self.collect_expr(&arg.expression, UseContext::Value);
                }
            }
            hir::ExpressionKind::Reference(value, mutability) => {
                let mutable = matches!(mutability, hir::Mutability::Mutable);
                self.collect_expr(value, UseContext::Borrow { mutable });
            }
            hir::ExpressionKind::Dereference(value) => {
                self.collect_expr(value, ctx);
            }
            hir::ExpressionKind::Binary(_, lhs, rhs) => {
                self.collect_expr(lhs, UseContext::Value);
                self.collect_expr(rhs, UseContext::Value);
            }
            hir::ExpressionKind::AssignOp(_, lhs, rhs) => {
                self.collect_expr(lhs, UseContext::Place);
                self.collect_expr(rhs, UseContext::Value);
            }
            hir::ExpressionKind::Unary(_, value)
            | hir::ExpressionKind::Propagate(value)
            | hir::ExpressionKind::CastAs(value, _)
            | hir::ExpressionKind::CastAsTry(value, _)
            | hir::ExpressionKind::TypeIs(value, _) => {
                self.collect_expr(value, UseContext::Value);
            }
            hir::ExpressionKind::TupleAccess(value, _) => {
                self.collect_expr(value, ctx);
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                self.collect_expr(lhs, UseContext::Place);
                self.collect_expr(rhs, UseContext::Value);
            }
            hir::ExpressionKind::PatternBinding(binding) => {
                self.collect_expr(&binding.expression, UseContext::Value);
            }
            hir::ExpressionKind::Block(block) | hir::ExpressionKind::UnsafeBlock(block) => {
                self.collect_block(block);
            }
            hir::ExpressionKind::StructLiteral(literal) => {
                for field in &literal.fields {
                    self.collect_expr(&field.expression, UseContext::Value);
                }
            }
            hir::ExpressionKind::Await(value) => {
                self.collect_expr(value, UseContext::Value);
            }
        }
    }

    fn collect_pattern_bindings(&mut self, pattern: &hir::Pattern) {
        let mut binding_ids = Vec::new();
        self.collect_pattern_binding_ids(pattern, &mut binding_ids);
        for binding_id in binding_ids {
            self.local_decls.insert(binding_id);
        }
    }

    fn collect_pattern_binding_ids(&self, pattern: &hir::Pattern, binding_ids: &mut Vec<NodeID>) {
        match &pattern.kind {
            hir::PatternKind::Binding { .. } => binding_ids.push(pattern.id),
            hir::PatternKind::Tuple(patterns, _) | hir::PatternKind::Or(patterns, _) => {
                for pattern in patterns {
                    self.collect_pattern_binding_ids(pattern, binding_ids);
                }
            }
            hir::PatternKind::Reference { pattern, .. } => {
                self.collect_pattern_binding_ids(pattern, binding_ids);
            }
            hir::PatternKind::PathTuple { fields, .. } => {
                for pattern in fields {
                    self.collect_pattern_binding_ids(pattern, binding_ids);
                }
            }
            hir::PatternKind::Wildcard
            | hir::PatternKind::Rest
            | hir::PatternKind::Member(_)
            | hir::PatternKind::Literal(_) => {}
        }
    }
}

fn classify_capture_kind<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    ty: Ty<'ctx>,
    usage: CaptureUsage,
) -> crate::sema::models::CaptureKind {
    if usage.moved {
        return crate::sema::models::CaptureKind::ByMove;
    }
    if let Some(mutability) = usage.by_ref {
        return crate::sema::models::CaptureKind::ByRef {
            mutable: matches!(mutability, hir::Mutability::Mutable),
        };
    }
    if gcx.is_type_copyable_in_def(ty, owner) {
        crate::sema::models::CaptureKind::ByCopy
    } else {
        crate::sema::models::CaptureKind::ByMove
    }
}

fn infer_closure_kind(
    is_async: bool,
    captures: &[crate::sema::models::CapturedVar<'_>],
) -> crate::sema::models::ClosureKind {
    // Async closures currently lower to futures that outlive the call site.
    // Any captured environment therefore has to be owned by the returned
    // future, which means the closure must be consumed when invoked.
    if is_async {
        return if captures.is_empty() {
            crate::sema::models::ClosureKind::AsyncFn
        } else {
            crate::sema::models::ClosureKind::AsyncFnOnce
        };
    }

    let mut kind = crate::sema::models::ClosureKind::Fn;

    for capture in captures {
        match capture.capture_kind {
            crate::sema::models::CaptureKind::ByMove => {
                return if is_async {
                    crate::sema::models::ClosureKind::AsyncFnOnce
                } else {
                    crate::sema::models::ClosureKind::FnOnce
                };
            }
            crate::sema::models::CaptureKind::ByRef { mutable: true } => {
                kind = if is_async {
                    crate::sema::models::ClosureKind::AsyncFnMut
                } else {
                    crate::sema::models::ClosureKind::FnMut
                };
            }
            crate::sema::models::CaptureKind::ByCopy
            | crate::sema::models::CaptureKind::ByRef { mutable: false } => {}
        }
    }

    kind
}

fn closure_self_ty<'ctx>(
    gcx: Gcx<'ctx>,
    closure_ty: Ty<'ctx>,
    kind: crate::sema::models::ClosureKind,
) -> Ty<'ctx> {
    match kind {
        crate::sema::models::ClosureKind::Fn | crate::sema::models::ClosureKind::AsyncFn => {
            Ty::new(TyKind::Pointer(closure_ty, hir::Mutability::Immutable), gcx)
        }
        crate::sema::models::ClosureKind::FnMut | crate::sema::models::ClosureKind::AsyncFnMut => {
            Ty::new(TyKind::Pointer(closure_ty, hir::Mutability::Mutable), gcx)
        }
        crate::sema::models::ClosureKind::FnOnce
        | crate::sema::models::ClosureKind::AsyncFnOnce => closure_ty,
    }
}
