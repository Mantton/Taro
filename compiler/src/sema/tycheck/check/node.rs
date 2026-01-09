use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID},
    sema::{
        models::{
            Const, ConstKind, ConstValue, GenericArgument, GenericArguments, GenericParameter,
            GenericParameterDefinition, GenericParameterDefinitionKind, Ty, TyKind,
        },
        resolve::models::{DefinitionKind, TypeHead, VariantCtorKind},
        tycheck::{
            check::{checker::Checker, gather::GatherLocalsVisitor},
            infer::InferCtx,
            lower::lowerer::TypeLowerer,
            results::TypeCheckResults,
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, AssignOpGoalData, BinOpGoalData,
                BindOverloadGoalData, ConstraintSystem, DerefGoalData, DisjunctionBranch, Goal,
                InferredStaticMemberGoalData, MemberGoalData, MethodCallData, StructLiteralField,
                StructLiteralGoalData, TupleAccessGoalData, UnOpGoalData,
            },
            utils::{
                const_eval::eval_const_expression,
                generics::GenericsBuilder,
                instantiate::{instantiate_signature_with_args, instantiate_ty_with_args},
                type_head_from_value_ty,
            },
        },
    },
    span::{Span, Symbol},
};
use std::cell::RefCell;
use std::rc::Rc;

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

        self.return_ty = Some(return_ty);

        // Add Parameters To Locals Map
        for (parameter, parameter_ty) in node
            .signature
            .prototype
            .inputs
            .iter()
            .zip(param_tys.iter().copied())
        {
            self.locals.borrow_mut().insert(
                parameter.id,
                crate::sema::tycheck::check::checker::LocalBinding {
                    ty: parameter_ty,
                    mutable: false,
                },
            );
        }

        let Some(body) = &node.block else {
            // Extern function declaration.
            return;
        };

        if let Some(body) = hir::is_expression_bodied(body) {
            // --- single-expression body ---
            self.check_return(Some(body), body.span, None);
        } else {
            // --- regular block body ---
            self.check_block(body, None);
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
            hir::StatementKind::Break => self.check_break(node.span),
            hir::StatementKind::Continue => self.check_continue(node.span),
            hir::StatementKind::Return(expression) => {
                self.check_return(expression.as_deref(), node.span, cs.as_deref_mut());
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

        return;
    }

    fn check_local_declaration(&self, decl: &hir::Declaration) {
        match &decl.kind {
            hir::DeclarationKind::Function(node) => {
                let mut checker = Checker::new(
                    self.context,
                    decl.id,
                    RefCell::new(TypeCheckResults::default()),
                );
                checker.check_function(decl.id, node, hir::FunctionContext::Free);
                self.results
                    .borrow_mut()
                    .extend_from(checker.results.into_inner());
            }
            hir::DeclarationKind::Constant(node) => {
                let mut checker = Checker::new(
                    self.context,
                    decl.id,
                    RefCell::new(TypeCheckResults::default()),
                );
                checker.check_constant(decl.id, node);
                self.results
                    .borrow_mut()
                    .extend_from(checker.results.into_inner());
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

        let Some(expectation) = self.return_ty else {
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
    fn check_local(&self, node: &hir::Local) {
        let mut cs = self.new_cs();
        self.with_infer_ctx(cs.infer_cx.clone(), || {
            GatherLocalsVisitor::from_local(&cs, &self, node);
            let local_ty = self.get_local(node.id).ty;
            if let Some(annotation) = node.ty.as_deref() {
                self.add_type_constraints(local_ty, annotation.span, &mut cs);
            }

            if let Some(expression) = node.initializer.as_ref() {
                let init_ty = self.synth_with_expectation(expression, Some(local_ty), &mut cs);
                cs.add_goal(
                    Goal::Coerce {
                        node_id: expression.id,
                        from: init_ty,
                        to: local_ty,
                    },
                    expression.span,
                );
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
            self.add_type_constraints(local_ty, annotation.span, cs);
        }

        if let Some(expression) = node.initializer.as_ref() {
            let init_ty = self.synth_with_expectation(expression, Some(local_ty), cs);
            cs.add_goal(
                Goal::Coerce {
                    node_id: expression.id,
                    from: init_ty,
                    to: local_ty,
                },
                expression.span,
            );
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
        self.with_infer_ctx(cs.infer_cx.clone(), || {
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
        })
    }

    fn new_cs(&self) -> Cs<'ctx> {
        if let Some(infer_cx) = self.infer_ctx() {
            Cs::with_infer_ctx(self.context, self.current_def, infer_cx)
        } else {
            Cs::new(self.context, self.current_def)
        }
    }

    /// Commits all resolved results from a constraint system to the checker's results.
    /// Used when solving sub-expressions in separate constraint systems (e.g., match scrutinee).
    fn commit_constraint_results(&self, cs: &Cs<'ctx>) {
        for (id, ty) in cs.resolved_expr_types() {
            let ty = cs.infer_cx.resolve_vars_if_possible(ty);
            self.results.borrow_mut().record_node_type(id, ty);
        }
        for (id, adjustments) in cs.resolved_adjustments() {
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
        for (id, args) in cs.resolved_instantiations() {
            let resolved_args = cs.infer_cx.resolve_args_if_possible(args);
            self.results
                .borrow_mut()
                .record_instantiation(id, resolved_args);
        }
        for (id, ty) in cs.resolved_local_types() {
            let ty = cs.infer_cx.resolve_vars_if_possible(ty);
            self.finalize_local(id, ty);
            self.results.borrow_mut().record_node_type(id, ty);
        }
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
                self.synth_expression_literal(node, expectation, cs)
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
            hir::ExpressionKind::Reference(inner, mutability) => {
                let inner_ty = self.synth_with_expectation(inner, None, cs);
                if *mutability == hir::Mutability::Mutable {
                    if !self.require_mut_borrow(inner, cs) {
                        return Ty::error(self.gcx());
                    }
                }
                Ty::new(TyKind::Reference(inner_ty, *mutability), self.gcx())
            }
            hir::ExpressionKind::Dereference(inner) => {
                let ptr_ty = self.synth_with_expectation(inner, None, cs);
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
            hir::ExpressionKind::PatternBinding(condition) => {
                self.synth_pattern_binding_expression(expression, condition, cs)
            }
            hir::ExpressionKind::Block(block) => {
                self.synth_block_expression(block, expectation, cs)
            }
            hir::ExpressionKind::UnsafeBlock(block) => {
                self.synth_unsafe_block_expression(block, expectation, cs)
            }
            hir::ExpressionKind::StructLiteral(lit) => {
                self.synth_struct_literal(expression, lit, cs)
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
            cs.equal(expectation, target_ty, expression.span);
        }

        target_ty
    }

    fn require_mut_place(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                match &path.resolution {
                    hir::Resolution::LocalVariable(id) => {
                        let binding = self.get_local(*id);
                        if !binding.mutable {
                            self.gcx().dcx().emit_error(
                                "cannot assign to an immutable binding".into(),
                                Some(expr.span),
                            );
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
                        if matches!(&path.resolution, hir::Resolution::LocalVariable(_)) =>
                    {
                        let hir::Resolution::LocalVariable(id) = &path.resolution else {
                            unreachable!()
                        };
                        let binding = self.get_local(*id);
                        if !binding.mutable && !via_ptr_mut {
                            self.gcx().dcx().emit_error(
                                "cannot assign through an immutable binding".into(),
                                Some(target.span),
                            );
                            false
                        } else {
                            true
                        }
                    }
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

                // Field mutability (struct only for now).
                let TyKind::Adt(def, args) = base_ty.kind() else {
                    self.gcx().dcx().emit_error(
                        "cannot assign to a member of a non-struct value".into(),
                        Some(expr.span),
                    );
                    return false;
                };
                if self.gcx().definition_kind(def.id) != DefinitionKind::Struct {
                    self.gcx().dcx().emit_error(
                        "cannot assign to a member of a non-struct value".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                let struct_def = self.gcx().get_struct_definition(def.id);
                let struct_def = crate::sema::tycheck::utils::instantiate::
                    instantiate_struct_definition_with_args(self.gcx(), struct_def, args);
                let mut field = None;
                for f in struct_def.fields {
                    if f.name == name.symbol {
                        field = Some(*f);
                        break;
                    }
                }

                let Some(field) = field else {
                    self.gcx().dcx().emit_error(
                        format!("unknown field '{}'", name.symbol.as_str()),
                        Some(expr.span),
                    );
                    return false;
                };

                if field.mutability != hir::Mutability::Mutable {
                    self.gcx().dcx().emit_error(
                        "cannot assign to an immutable field".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                true
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

    fn require_mut_borrow(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                if let hir::Resolution::LocalVariable(id) = &path.resolution {
                    let binding = self.get_local(*id);
                    if binding.ty.is_error() {
                        return true;
                    }
                    if !binding.mutable {
                        self.gcx().dcx().emit_error(
                            "cannot take a mutable reference to an immutable binding".into(),
                            Some(expr.span),
                        );
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

                let (base_ty, via_ptr_mut, via_ptr) = match receiver_ty.kind() {
                    TyKind::Error => return true,
                    TyKind::Pointer(inner, mutbl) | TyKind::Reference(inner, mutbl) => {
                        (inner, mutbl == hir::Mutability::Mutable, true)
                    }
                    _ => (receiver_ty, true, false),
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
                        if let hir::Resolution::LocalVariable(id) = &path.resolution {
                            let binding = self.get_local(*id);
                            if !binding.mutable {
                                self.gcx().dcx().emit_error(
                                    "cannot take a mutable reference to an immutable binding"
                                        .into(),
                                    Some(target.span),
                                );
                                return false;
                            }
                        }
                    }
                }

                let TyKind::Adt(def, args) = base_ty.kind() else {
                    self.gcx().dcx().emit_error(
                        "cannot borrow a member of a non-struct value".into(),
                        Some(expr.span),
                    );
                    return false;
                };
                if self.gcx().definition_kind(def.id) != DefinitionKind::Struct {
                    self.gcx().dcx().emit_error(
                        "cannot borrow a member of a non-struct value".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                let struct_def = self.gcx().get_struct_definition(def.id);
                let struct_def = crate::sema::tycheck::utils::instantiate::
                    instantiate_struct_definition_with_args(self.gcx(), struct_def, args);
                let mut field = None;
                for f in struct_def.fields {
                    if f.name == name.symbol {
                        field = Some(*f);
                        break;
                    }
                }

                let Some(field) = field else {
                    self.gcx().dcx().emit_error(
                        format!("unknown field '{}'", name.symbol.as_str()),
                        Some(expr.span),
                    );
                    return false;
                };

                if field.mutability != hir::Mutability::Mutable {
                    self.gcx().dcx().emit_error(
                        "cannot take a mutable reference to an immutable field".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                true
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
                            if let hir::Resolution::LocalVariable(id) = &path.resolution {
                                let binding = self.get_local(*id);
                                if !binding.mutable {
                                    self.gcx().dcx().emit_error(
                                        "cannot take a mutable reference to an immutable binding"
                                            .into(),
                                        Some(target.span),
                                    );
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

    fn synth_expression_literal(
        &self,
        literal: &hir::Literal,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        match literal {
            hir::Literal::Bool(_) => gcx.types.bool,
            hir::Literal::Rune(_) => gcx.types.rune,
            hir::Literal::String(_) => gcx.types.string,
            hir::Literal::Integer(_) => {
                let opt_ty = expectation.and_then(|ty| match ty.kind() {
                    TyKind::Int(_) | TyKind::UInt(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| cs.infer_cx.next_int_var())
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
                        let generics = self.gcx().generics_of(owner);
                        let Some(param) = generics.parameters.iter().find(|p| p.id == *id) else {
                            return Ty::error(self.gcx());
                        };
                        match &param.kind {
                            GenericParameterDefinitionKind::Const { ty, .. } => self.lower_type(ty),
                            _ => Ty::error(self.gcx()),
                        }
                    }
                    _ => self.gcx().get_type(*id),
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
                    .copied()
                    .filter(|id| self.gcx().is_definition_visible(*id, self.current_def))
                    .collect();

                if visible.is_empty() {
                    self.gcx()
                        .dcx()
                        .emit_error("function is not visible here".into(), Some(span));
                    return Ty::error(self.gcx());
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
            hir::Resolution::Foundation(std_type) => {
                // Resolve to the actual std library type (e.g., Dictionary, Optional, List)
                let Some(name) = std_type.name_str() else {
                    self.gcx().dcx().emit_error(
                        "this standard library type cannot be used as a value".into(),
                        Some(span),
                    );
                    return Ty::error(self.gcx());
                };
                let Some(def_id) = self.gcx().find_std_type(name) else {
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
        // Builtin `make`: returns a pointer to the argument type.
        if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &callee.kind
            && matches!(
                path.resolution,
                hir::Resolution::Foundation(hir::StdType::Make)
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
                        span: callee.span,
                    }),
                    callee.span,
                );
                cs.record_expr_ty(callee.id, result_ty);
                result_ty
            }
            _ => self.synth(callee, cs),
        };

        let positional_args = arguments.iter().all(|arg| arg.label.is_none());
        let arg_expectations = if positional_args {
            self.argument_expectations_for_call(callee, callee_ty, expect_ty, cs)
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
                    .copied();
                let ty = if let Some(expected) = expected {
                    self.synth_with_expectation(&n.expression, Some(expected), cs)
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

        let result_ty = cs.infer_cx.next_ty_var(expression.span);
        cs.record_expr_ty(expression.id, result_ty);

        let data = ApplyGoalData {
            call_node_id: expression.id,
            call_span: expression.span,
            callee_ty,
            callee_source: self.resolve_callee(callee, cs),
            result_ty,
            _expect_ty: expect_ty,
            arguments: apply_arguments,
            skip_labels: false,
        };
        cs.add_goal(Goal::Apply(data), expression.span);

        result_ty
    }

    fn argument_expectations_for_call(
        &self,
        callee: &hir::Expression,
        callee_ty: Ty<'ctx>,
        expect_ty: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Option<Vec<Ty<'ctx>>> {
        if let hir::ExpressionKind::InferredMember { name } = &callee.kind {
            if let Some(expect_ty) = expect_ty {
                if let Some(args) =
                    self.inferred_member_argument_expectations(name, expect_ty, callee.span, cs)
                {
                    return Some(args);
                }
            }
        }

        let callee_ty = cs.infer_cx.resolve_vars_if_possible(callee_ty);
        match callee_ty.kind() {
            TyKind::FnPointer { inputs, .. } => Some(inputs.to_vec()),
            _ => None,
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
                    .copied()
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

                        let result_ty = cs.infer_cx.next_ty_var(expression.span);
                        cs.record_expr_ty(expression.id, result_ty);

                        let data = ApplyGoalData {
                            call_node_id: expression.id,
                            call_span: expression.span,
                            callee_ty,
                            callee_source: resolution.definition_id(),
                            result_ty,
                            _expect_ty: expect_ty,
                            arguments: apply_arguments,
                            skip_labels: false,
                        };
                        cs.add_goal(Goal::Apply(data), expression.span);
                        return result_ty;
                    }
                    _ => {}
                }
            }
        }

        let recv_ty = self.synth(receiver, cs);
        let args: Vec<ApplyArgument<'ctx>> = arguments
            .iter()
            .map(|n| ApplyArgument {
                id: n.expression.id,
                label: n.label.map(|n| n.identifier),
                ty: self.synth(&n.expression, cs),
                span: n.expression.span,
            })
            .collect();

        let method_ty = cs.infer_cx.next_ty_var(name.span);
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        cs.add_goal(
            Goal::MethodCall(MethodCallData {
                node_id: expression.id,
                receiver: recv_ty,
                reciever_node: receiver.id,
                reciever_span: receiver.span,
                method_ty: method_ty,
                expect_ty,
                name: *name,
                arguments: args,
                result: result_ty,
                span: expression.span,
            }),
            expression.span,
        );

        result_ty
    }
}

impl<'ctx> Checker<'ctx> {
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
        let name = Symbol::new("new");
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
        cs.equal(self.gcx().types.bool, cond_ty, node.condition.span);

        // then/else branches are expressions; typecheck with shared expectation.
        let then_ty = self.synth_with_expectation(&node.then_block, expectation, cs);
        let else_ty = if let Some(else_expr) = &node.else_block {
            let else_expectation = expectation.or(Some(then_ty));
            Some(self.synth_with_expectation(else_expr, else_expectation, cs))
        } else {
            None
        };

        match else_ty {
            Some(else_ty) => {
                // Branches must agree.
                cs.equal(
                    then_ty,
                    else_ty,
                    node.else_block
                        .as_ref()
                        .map(|e| e.span)
                        .unwrap_or(node.then_block.span),
                );
                then_ty
            }
            None => {
                // No else: coerce the then branch into the expected type if provided,
                // otherwise use void/unit.
                if let Some(exp) = expectation {
                    cs.add_goal(
                        Goal::Coerce {
                            node_id: node.then_block.id,
                            from: then_ty,
                            to: exp,
                        },
                        expression.span,
                    );
                    exp
                } else {
                    self.gcx().types.void
                }
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

        // Specialized diagnostic for optional binding shorthand (`if let`).
        // Catching this early avoids a cascade of resolution/type errors.
        if condition.source.kind == hir::MatchKind::OptionalBinding
            && !expr_ty.is_error()
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
        let result_ty = expectation.unwrap_or_else(|| shared_infer_cx.next_ty_var(expression.span));

        self.with_infer_ctx(shared_infer_cx.clone(), || {
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
                arm_cs.equal(result_ty, arm_ty, arm.body.span);

                // Solve and commit each arm independently
                arm_cs.solve_intermediate();
                self.commit_constraint_results(&arm_cs);
                _cs.merge(arm_cs);
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
                let guard_ty = self.synth_with_expectation(
                    guard,
                    Some(self.gcx().types.bool),
                    &mut none_cs,
                );
                none_cs.equal(self.gcx().types.bool, guard_ty, guard.span);
            }

            let none_ty = self.synth_with_expectation(&none_arm.body, Some(result_ty), &mut none_cs);
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
                    if emit_errors {
                        self.gcx().dcx().emit_error(
                            "cannot resolve members on this type receiver".into(),
                            Some(span),
                        );
                    }
                    return (hir::Resolution::Error, None);
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
            | hir::Resolution::Foundation(..) => {
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
                    name.symbol.as_str(),
                    base_ty.format(gcx)
                );
                gcx.dcx().emit_error(msg.into(), Some(span));
            }
            return hir::Resolution::Error;
        }

        let visible: Vec<_> = candidates
            .iter()
            .copied()
            .filter(|id| gcx.is_definition_visible(*id, self.current_def))
            .collect();

        if visible.is_empty() {
            if emit_errors {
                gcx.dcx().emit_error(
                    format!(
                        "static member '{}' is not visible here",
                        name.symbol.as_str()
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
                    members.extend(set.members.iter().copied());
                }
            }
        }

        members
    }

    fn value_path_def_id(&self, resolution: &hir::Resolution) -> Option<DefinitionID> {
        match resolution {
            hir::Resolution::Foundation(std_type) => {
                let name = std_type.name_str()?;
                self.gcx().find_std_type(name)
            }
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

        if let hir::Resolution::Foundation(std_type) = resolution {
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
                    format!("'{}' does not accept generic arguments", name.as_str()).into(),
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

        let base_args = base_args.unwrap_or(&[]);
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

        let args = GenericsBuilder::for_item(gcx, def_id, |param, _| {
            if param.index < parent_count {
                if let Some(arg) = base_args.get(param.index) {
                    return *arg;
                }
                return self.lower_value_path_missing_arg(param, span);
            }

            if let Some(arg) = explicit_iter.next() {
                return self.lower_value_path_explicit_arg(param, arg);
            }

            self.lower_value_path_missing_arg(param, span)
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
                let expected_ty = self.lower_type(ty);
                GenericArgument::Const(self.lowerer().lower_const_argument(expected_ty, c))
            }
            (GenericParameterDefinitionKind::Type { .. }, hir::TypeArgument::Const(c)) => {
                gcx.dcx()
                    .emit_error("expected type argument".into(), Some(c.value.span));
                GenericArgument::Type(gcx.types.error)
            }
            (GenericParameterDefinitionKind::Const { ty, .. }, hir::TypeArgument::Type(ty_arg)) => {
                let expected_ty = self.lower_type(ty);
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

        let GenericParameterDefinitionKind::Const { ty, .. } = &def.kind else {
            return None;
        };

        let param = GenericParameter {
            index: def.index,
            name: def.name,
        };

        Some(Const {
            ty: self.lower_type(ty),
            kind: ConstKind::Param(param),
        })
    }

    fn lower_value_path_missing_arg(
        &self,
        param: &GenericParameterDefinition,
        span: Span,
    ) -> GenericArgument<'ctx> {
        let gcx = self.gcx();
        match &param.kind {
            GenericParameterDefinitionKind::Type { default } => {
                if let Some(default) = default {
                    GenericArgument::Type(self.lower_type(default))
                } else {
                    GenericArgument::Type(self.ty_infer(Some(param), span))
                }
            }
            GenericParameterDefinitionKind::Const { ty, default } => {
                let expected_ty = self.lower_type(ty);
                if let Some(default) = default {
                    GenericArgument::Const(
                        self.lowerer().lower_const_argument(expected_ty, default),
                    )
                } else {
                    if let Some(infer_cx) = self.infer_ctx() {
                        infer_cx.var_for_generic_param(param, span)
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
    fn synth_path_expression(
        &self,
        expression: &hir::Expression,
        path: &hir::ResolvedPath,
        expectation: Option<Ty<'ctx>>,
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
            cs,
        )
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
        let result_ty = cs.infer_cx.next_ty_var(expression.span);
        cs.add_goal(
            Goal::Member(MemberGoalData {
                node_id: expression.id,
                receiver_node: target.id,
                receiver: receiver_ty,
                name: *name,
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

        // We construct a temporary Type node to reuse the lower_type logic.
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
        for field in &lit.fields {
            let ty = self.synth(&field.expression, cs);

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
        for (i, element) in elements.iter().enumerate() {
            let elem_expectation = expected_elements.and_then(|tys| tys.get(i).copied());
            let ty = self.synth_with_expectation(element, elem_expectation, cs);
            element_types.push(ty);
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
        let (expected_elem, expected_array) = if let Some(expectation) = expectation {
            match expectation.kind() {
                TyKind::Array { element, .. } => (Some(element), Some(expectation)),
                _ => (None, None),
            }
        } else {
            (None, None)
        };

        let element_ty = expected_elem.unwrap_or_else(|| cs.infer_cx.next_ty_var(expression.span));

        for elem in elements {
            let ty = self.synth_with_expectation(elem, Some(element_ty), cs);
            cs.equal(element_ty, ty, elem.span);
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
        let idx_val =
            if let hir::ExpressionKind::Literal(hir::Literal::Integer(val)) = &index.value.kind {
                *val as usize
            } else {
                unreachable!()
            };

        let receiver_ty = self.synth(receiver, cs);
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
                            variant.name.as_str()
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

                if fields.len() != variant_fields.len() {
                    self.gcx().dcx().emit_error(
                        format!(
                            "expected {} field(s) for enum variant '{}', got {}",
                            variant_fields.len(),
                            variant.name.as_str(),
                            fields.len()
                        )
                        .into(),
                        Some(pattern.span),
                    );
                    return;
                }

                cs.equal(ctx.adjusted_ty, enum_ty, pattern.span);

                for (pat, field) in fields.iter().zip(variant_fields.iter()) {
                    let mut sub_ctx = PatternContext::new(field.ty);
                    sub_ctx.default_mode = ctx.default_mode;
                    self.check_pattern_with_context(pat, &mut sub_ctx, pat.id, cs);
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
                let lit_ty = self.synth_expression_literal(literal, None, cs);
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
                    variant.name.as_str()
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
        let hir::Resolution::Definition(ctor_id, kind) = resolution else {
            if !matches!(resolution, hir::Resolution::Error) {
                gcx.dcx()
                    .emit_error("expected enum variant pattern".into(), Some(span));
            }
            return None;
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
            db.def_to_enum_def.get(&enum_id).copied()
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
            .copied();

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
                    name.symbol.as_str(),
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
                    name.symbol.as_str(),
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
        let variant = def.variants.iter().find(|v| v.name == name.symbol).copied();

        let Some(variant) = variant else {
            gcx.dcx().emit_error(
                format!(
                    "enum '{}' has no variant named '{}'",
                    gcx.definition_ident(enum_id).symbol.as_str(),
                    name.symbol.as_str()
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
            .copied();

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
        let Some(opt_id) = self.gcx().find_std_type("Optional") else {
            return false;
        };
        def.id == opt_id
    }

    fn optional_inner_type(
        &self,
        ty: Ty<'ctx>,
    ) -> Option<(GenericArguments<'ctx>, Ty<'ctx>)> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        let Some(opt_id) = self.gcx().find_std_type("Optional") else {
            return None;
        };
        if def.id != opt_id {
            return None;
        }
        let inner = args.first()?.ty()?;
        Some((args, inner))
    }

    fn mk_optional_type(&self, inner: Ty<'ctx>) -> (Ty<'ctx>, GenericArguments<'ctx>) {
        let gcx = self.gcx();
        let opt_id = gcx
            .find_std_type("Optional")
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
}
