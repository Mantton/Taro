use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID},
    sema::{
        models::{Ty, TyKind},
        resolve::models::{DefinitionKind, TypeHead},
        tycheck::{
            check::{checker::Checker, gather::GatherLocalsVisitor},
            solve::{
                ApplyArgument, ApplyGoalData, BinOpGoalData, BindOverloadGoalData,
                ConstraintSystem, DisjunctionBranch, Goal, MemberGoalData, MethodCallData,
                StructLiteralField, StructLiteralGoalData, TupleAccessGoalData, UnOpGoalData,
            },
        },
    },
    span::{Span, Symbol},
};

impl<'ctx> Checker<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.context
    }

    pub fn check_function(
        mut self,
        id: DefinitionID,
        node: &hir::Function,
        _: hir::FunctionContext,
    ) {
        let gcx = self.gcx();
        let signature = gcx.get_signature(id);
        let signature = Ty::from_labeled_signature(gcx, signature);

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
            // TODO: Mark As return
            self.check_return(body);
        } else {
            // --- regular block body ---
            self.check_block(body);
        }
    }
}

impl<'ctx> Checker<'ctx> {
    fn check_statement(&self, node: &hir::Statement) {
        match &node.kind {
            hir::StatementKind::Declaration(..) => return,
            hir::StatementKind::Expression(node) => {
                self.top_level_check(node, None);
            }
            hir::StatementKind::Variable(node) => {
                self.check_local(node);
            }
            hir::StatementKind::Break => self.check_break(node.span),
            hir::StatementKind::Continue => self.check_continue(node.span),
            hir::StatementKind::Return(expression) => {
                if let Some(expression) = expression {
                    self.check_return(expression);
                }
            }
            hir::StatementKind::Loop { block, .. } => {
                self.check_loop(block);
            }
            hir::StatementKind::Defer(..) => todo!(),
            hir::StatementKind::Guard { .. } => todo!(),
        }

        return;
    }

    fn check_return(&self, node: &hir::Expression) {
        let Some(expectation) = self.return_ty else {
            unreachable!("ICE: return check called outside function body")
        };
        self.top_level_check(node, Some(expectation));
    }

    fn check_block(&self, node: &hir::Block) {
        for statement in &node.statements {
            self.check_statement(statement);
        }
        if let Some(tail) = node.tail.as_deref() {
            self.top_level_check(tail, None);
        }
    }
    fn check_local(&self, node: &hir::Local) {
        let mut cs = Cs::new(self.context);
        GatherLocalsVisitor::from_local(&cs, &self, node);
        let local_ty = self.get_local(node.id).ty;

        if let Some(expression) = node.initializer.as_ref() {
            let init_ty = self.synth_with_expectation(expression, Some(local_ty), &mut cs);
            cs.equal(local_ty, init_ty, expression.span);
        }

        self.check_pattern_structure(&node.pattern, local_ty, &mut cs);
        cs.solve_all();

        for (id, ty) in cs.resolved_expr_types() {
            self.gcx().cache_node_type(id, ty);
        }
        for (id, adjustments) in cs.resolved_adjustments() {
            self.gcx().cache_node_adjustments(id, adjustments);
        }
        for (id, def_id) in cs.resolved_overload_sources() {
            self.gcx().cache_overload_source(id, def_id);
        }

        for (id, index) in cs.resolved_field_indices() {
            self.gcx().cache_field_index(id, index);
        }

        for (id, ty) in cs.resolved_local_types() {
            self.finalize_local(id, ty);
            self.gcx().cache_node_type(id, ty);
        }
    }

    fn check_loop(&self, block: &hir::Block) {
        let depth = self.loop_depth.get();
        self.loop_depth.set(depth + 1);
        self.check_block(block);
        self.loop_depth.set(depth);
    }

    fn check_break(&self, span: Span) {
        if self.loop_depth.get() == 0 {
            self.gcx()
                .dcx()
                .emit_error("`break` used outside of a loop".into(), Some(span));
        }
    }

    fn check_continue(&self, span: Span) {
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
        let mut cs = Cs::new(self.context);
        let provided = self.synth_with_expectation(expression, expectation, &mut cs);
        if let Some(expectation) = expectation {
            cs.equal(expectation, provided, expression.span);
        }
        cs.solve_all();

        for (id, ty) in cs.resolved_expr_types() {
            self.gcx().cache_node_type(id, ty);
        }
        for (id, adjustments) in cs.resolved_adjustments() {
            self.gcx().cache_node_adjustments(id, adjustments);
        }
        for (id, def_id) in cs.resolved_overload_sources() {
            self.gcx().cache_overload_source(id, def_id);
        }

        for (id, index) in cs.resolved_field_indices() {
            self.gcx().cache_field_index(id, index);
        }

        for (id, ty) in cs.resolved_local_types() {
            self.finalize_local(id, ty);
            self.gcx().cache_node_type(id, ty);
        }

        let provided = cs.infer_cx.resolve_vars_if_possible(provided);
        if provided.is_infer() {
            return Ty::error(self.gcx());
        }
        provided
    }
}

type Cs<'c> = ConstraintSystem<'c>;
impl<'ctx> Checker<'ctx> {
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
            hir::ExpressionKind::Specialize { .. } => todo!(),
            hir::ExpressionKind::Array(..) => todo!(),
            hir::ExpressionKind::Tuple(elements) => {
                self.synth_tuple_expression(expression, elements, expectation, cs)
            }
            hir::ExpressionKind::If(expr) => {
                self.synth_if_expression(expression, expr, expectation, cs)
            }
            hir::ExpressionKind::Match(..) => todo!(),
            hir::ExpressionKind::Reference(inner, mutability) => {
                let inner_ty = self.synth_with_expectation(inner, None, cs);
                Ty::new(TyKind::Reference(inner_ty, *mutability), self.gcx())
            }
            hir::ExpressionKind::Dereference(inner) => {
                let ptr_ty = self.synth_with_expectation(inner, None, cs);
                match ptr_ty.kind() {
                    TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => inner,
                    _ => {
                        self.gcx().dcx().emit_error(
                            "cannot dereference a non-pointer/reference value".into(),
                            Some(expression.span),
                        );
                        Ty::error(self.gcx())
                    }
                }
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
            hir::ExpressionKind::AssignOp(..) => todo!(),
            hir::ExpressionKind::Assign(lhs, rhs) => {
                self.synth_assign_expression(expression, lhs, rhs, cs)
            }
            hir::ExpressionKind::CastAs(..) => todo!(),
            hir::ExpressionKind::PatternBinding(..) => todo!(),
            hir::ExpressionKind::Block(block) => {
                self.synth_block_expression(block, expectation, cs)
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
                            "cannot assign through a non-pointer/reference value".into(),
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
                        if !binding.mutable {
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
                let TyKind::Adt(def) = base_ty.kind() else {
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

                match receiver_ty.kind() {
                    TyKind::Pointer(_, mutbl) | TyKind::Reference(_, mutbl) => {
                        mutbl == hir::Mutability::Mutable
                    }
                    _ => self.require_mut_place(target, cs),
                }
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
            crate::sema::tycheck::solve::Goal::Equal(lhs_ty, rhs_ty),
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
            match &stmt.kind {
                hir::StatementKind::Expression(expr) => {
                    let _ = self.synth_with_expectation(expr, None, cs);
                }
                _ => self.check_statement(stmt),
            }
        }

        if let Some(tail) = block.tail.as_deref() {
            self.synth_with_expectation(tail, expectation, cs)
        } else {
            self.gcx().types.void
        }
    }
}

impl<'ctx> Checker<'ctx> {
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
            hir::Literal::Nil => {
                todo!();
            }
        }
    }

    fn synth_identifier_expression(
        &self,
        node_id: NodeID,
        span: Span,
        resolution: &hir::Resolution,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match resolution {
            hir::Resolution::LocalVariable(id) => self.get_local(*id).ty,
            hir::Resolution::Definition(id, kind) => match kind {
                DefinitionKind::Struct => {
                    let Some(nominal) = self.constructor_nominal_from_resolution(resolution) else {
                        return Ty::error(self.gcx());
                    };
                    self.synth_constructor_value_expression(node_id, nominal, span, expectation, cs)
                }
                _ => self.gcx().get_type(*id),
            },
            hir::Resolution::SelfConstructor(..) => {
                let Some(nominal) = self.constructor_nominal_from_resolution(resolution) else {
                    return Ty::error(self.gcx());
                };
                self.synth_constructor_value_expression(node_id, nominal, span, expectation, cs)
            }
            hir::Resolution::FunctionSet(candidates) => {
                let ty = cs.infer_cx.next_ty_var(span);
                let mut branches = vec![];
                for &candidate in candidates {
                    let candidate_ty = self.gcx().get_type(candidate);
                    let goal = Goal::BindOverload(BindOverloadGoalData {
                        node_id,
                        var_ty: ty,
                        candidate_ty,
                        source: candidate,
                    });
                    branches.push(DisjunctionBranch {
                        goal,
                        source: Some(candidate),
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
                self.synth_constructor_value_expression(node_id, nominal, span, expectation, cs)
            }
            hir::Resolution::PrimaryType(..)
            | hir::Resolution::InterfaceSelfTypeParameter(..)
            | hir::Resolution::Foundation(..) => todo!(),
            hir::Resolution::Error => unreachable!(),
        }
    }

    fn synth_constructor_value_expression(
        &self,
        node_id: NodeID,
        nominal: DefinitionID,
        span: Span,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let ty = cs.infer_cx.next_ty_var(span);
        if !self.bind_constructor_overload_set(node_id, nominal, span, ty, cs) {
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
        let callee_ty = self.synth(callee, cs);

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

        let data = ApplyGoalData {
            call_span: expression.span,
            callee_ty,
            callee_source: self.resolve_callee(callee),
            result_ty,
            expect_ty,
            arguments: apply_arguments,
        };
        cs.add_goal(Goal::Apply(data), expression.span);

        result_ty
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
                    DefinitionKind::Extension => match gcx.get_extension_type_head(*id)? {
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
        cs: &mut Cs<'ctx>,
    ) -> bool {
        let gcx = self.gcx();
        let head = TypeHead::Nominal(nominal);
        let name = Symbol::new("new");
        let constructors = gcx.with_type_database(nominal.package(), |db| {
            db.type_head_to_members
                .get(&head)
                .map(|idx| idx.static_functions.get(&name).map(|v| v.members.clone()))
                .flatten()
                .unwrap_or_default()
        });

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
                }),
                source: Some(ctor),
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
        let lhs_ty = self.synth(lhs, cs);
        let rhs_ty = self.synth(rhs, cs);
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = BinOpGoalData {
            lhs: lhs_ty,
            rhs: rhs_ty,
            rho: result_ty,
            expectation,
            operator,
            span: expression.span,
            assigning: false,
        };

        cs.add_goal(Goal::BinaryOp(data), expression.span);
        result_ty
    }
}

impl<'ctx> Checker<'ctx> {
    fn resolve_callee(&self, node: &hir::Expression) -> Option<DefinitionID> {
        match &node.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                self.resolve_resolution_callee(&path.resolution)
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
}

impl<'ctx> Checker<'ctx> {
    fn synth_path_expression(
        &self,
        expression: &hir::Expression,
        path: &hir::ResolvedPath,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match path {
            hir::ResolvedPath::Resolved(path) => self.synth_identifier_expression(
                expression.id,
                expression.span,
                &path.resolution,
                expectation,
                cs,
            ),
            hir::ResolvedPath::Relative(base_ty, segment) => {
                let base_ty = self.lower_type(base_ty);
                let Some(head) = self.type_head_from_value_ty(base_ty) else {
                    self.gcx().dcx().emit_error(
                        "cannot resolve members on this type receiver".into(),
                        Some(expression.span),
                    );
                    return Ty::error(self.gcx());
                };
                self.synth_static_member(expression.id, head, &segment.identifier, expression.span, cs)
            }
        }
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

    fn type_head_from_value_ty(&self, ty: Ty<'ctx>) -> Option<TypeHead> {
        match ty.kind() {
            TyKind::Bool => Some(TypeHead::Primary(
                crate::sema::resolve::models::PrimaryType::Bool,
            )),
            TyKind::Rune => Some(TypeHead::Primary(
                crate::sema::resolve::models::PrimaryType::Rune,
            )),
            TyKind::String => Some(TypeHead::Primary(
                crate::sema::resolve::models::PrimaryType::String,
            )),
            TyKind::Int(k) => Some(TypeHead::Primary(
                crate::sema::resolve::models::PrimaryType::Int(k),
            )),
            TyKind::UInt(k) => Some(TypeHead::Primary(
                crate::sema::resolve::models::PrimaryType::UInt(k),
            )),
            TyKind::Float(k) => Some(TypeHead::Primary(
                crate::sema::resolve::models::PrimaryType::Float(k),
            )),
            TyKind::Adt(def) => Some(TypeHead::Nominal(def.id)),
            TyKind::Reference(_, mutbl) => Some(TypeHead::Reference(mutbl)),
            TyKind::Pointer(_, mutbl) => Some(TypeHead::Pointer(mutbl)),
            TyKind::Tuple(items) => Some(TypeHead::Tuple(items.len() as u16)),
            TyKind::Infer(_) | TyKind::FnPointer { .. } | TyKind::Error => None,
        }
    }

    fn synth_static_member(
        &self,
        node_id: NodeID,
        head: TypeHead,
        name: &crate::span::Identifier,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let candidates = gcx.with_session_type_database(|db| {
            db.type_head_to_members
                .get(&head)
                .and_then(|idx| idx.static_functions.get(&name.symbol))
                .map(|set| set.members.clone())
                .unwrap_or_default()
        });

        if candidates.is_empty() {
            gcx.dcx().emit_error(
                format!("unknown static member '{}'", name.symbol.as_str()),
                Some(span),
            );
            return Ty::error(gcx);
        }

        let ty = cs.infer_cx.next_ty_var(span);
        let mut branches = Vec::with_capacity(candidates.len());
        for candidate in candidates {
            let candidate_ty = gcx.get_type(candidate);
            branches.push(DisjunctionBranch {
                goal: Goal::BindOverload(BindOverloadGoalData {
                    node_id,
                    var_ty: ty,
                    candidate_ty,
                    source: candidate,
                }),
                source: Some(candidate),
            });
        }
        cs.add_goal(Goal::Disjunction(branches), span);
        ty
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

impl<'ctx> Checker<'ctx> {
    fn check_pattern_structure(
        &self,
        pattern: &hir::Pattern,
        scrutinee: Ty<'ctx>,
        cs: &mut Cs<'ctx>,
    ) {
        match &pattern.kind {
            hir::PatternKind::Wildcard => {}
            hir::PatternKind::Identifier(_) => {
                let binding = self.get_local(pattern.id);
                cs.equal(scrutinee, binding.ty, pattern.span);
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
                cs.equal(scrutinee, tuple_ty, pattern.span);

                for (i, pat) in pats.iter().enumerate() {
                    self.check_pattern_structure(pat, elem_tys[i], cs);
                }
            }
            _ => todo!("pattern kind not supported in check_pattern_structure"),
        }
    }
}
