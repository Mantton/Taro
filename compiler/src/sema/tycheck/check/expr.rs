use super::*;
use crate::sema::{models::AliasKind, tycheck::solve::LiteralConstructor};

impl<'ctx> Checker<'ctx> {
    pub(super) fn add_type_constraints(&self, ty: Ty<'ctx>, span: Span, cs: &mut Cs<'ctx>) {
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
                    cs.add_constraints_for_existential(*iface, span);
                }
            }
            TyKind::Array { element, .. } => self.add_type_constraints(element, span, cs),
            TyKind::Tuple(items) => {
                for item in items.iter() {
                    self.add_type_constraints(*item, span, cs);
                }
            }
            TyKind::Pointer(inner, _) | TyKind::Reference(inner) => {
                self.add_type_constraints(inner, span, cs);
            }
            TyKind::FnPointer { inputs, output, .. } => {
                for input in inputs.iter() {
                    self.add_type_constraints(*input, span, cs);
                }
                self.add_type_constraints(output, span, cs);
            }
            _ => {}
        }
    }

    pub(super) fn synth_with_expectation(
        &self,
        node: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        self.expression_contexts
            .borrow_mut()
            .insert(node.id, (node.span, self.unsafe_depth.get() > 0));
        if let Some(ty) = self
            .prechecked_bracket_receivers
            .borrow()
            .get(&node.id)
            .copied()
        {
            return ty;
        }
        let ty = self.synth_expression_kind(node, expectation, cs);
        cs.record_expr_ty(node.id, ty);
        // self.gcx().dcx().emit_info(
        //     format!("Checked {}", ty.format(self.gcx())),
        //     Some(node.span),
        // );
        ty
    }

    pub(super) fn synth(&self, node: &hir::Expression, cs: &mut Cs<'ctx>) -> Ty<'ctx> {
        self.synth_with_expectation(node, None, cs)
    }

    pub(super) fn synth_expression_kind(
        &self,
        expression: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match &expression.kind {
            hir::ExpressionKind::MemberBrackets {
                member,
                type_arguments,
                indexed,
                diagnostics,
            } => self.synth_member_brackets(
                expression,
                member,
                type_arguments,
                indexed.as_deref(),
                diagnostics,
                expectation,
                cs,
            ),
            hir::ExpressionKind::Index {
                target,
                index,
                nodes,
            } => self.synth_index(expression, target, index, *nodes, cs),
            hir::ExpressionKind::Literal(node) => {
                if matches!(node, hir::Literal::Nil) {
                    // Nil has no standalone runtime type. Infer its nullable
                    // target separately and materialize it at this literal,
                    // preserving effects in surrounding blocks and branches.
                    let target =
                        expectation.unwrap_or_else(|| cs.infer_cx.next_ty_var(expression.span));
                    let from = cs.infer_cx.next_nil_var();
                    cs.add_goal(
                        Goal::Coerce {
                            node_id: expression.id,
                            from,
                            to: target,
                        },
                        expression.span,
                    );
                    return target;
                }
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
            hir::ExpressionKind::Reference(inner) => {
                let inner_ty = self.synth_with_expectation(inner, None, cs);
                if inner_ty.is_error() {
                    return Ty::error(self.gcx());
                }
                if matches!(
                    inner.kind,
                    hir::ExpressionKind::Member { .. }
                        | hir::ExpressionKind::Dereference(_)
                        | hir::ExpressionKind::TupleAccess(..)
                ) {
                    cs.without_fallbacks(|cs| cs.solve_intermediate());
                }
                if !self.require_reference_place(inner, cs) {
                    return Ty::error(self.gcx());
                }
                self.receiver_is_addressable(inner, cs);
                self.index_place_requests.borrow_mut().insert(inner.id);
                Ty::new(TyKind::Reference(inner_ty), self.gcx())
            }
            hir::ExpressionKind::Dereference(inner) => {
                let ptr_ty = self.synth_with_expectation(inner, None, cs);
                if ptr_ty.is_error() {
                    return Ty::error(self.gcx());
                }
                let result_ty = cs.infer_cx.next_ty_var(expression.span);
                let receiver_addressable = self.receiver_is_addressable(inner, cs);

                cs.add_goal(
                    Goal::Deref(DerefGoalData {
                        operand_node: inner.id,
                        receiver_addressable,
                        operand_ty: ptr_ty,
                        is_unsafe_context: self.unsafe_depth.get() > 0,
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
                self.synth_cast_expression(expression, value, ty, cs)
            }
            hir::ExpressionKind::CastAsTry(value, ty) => {
                self.synth_try_cast_expression(value, ty, cs)
            }
            hir::ExpressionKind::TypeIs(value, ty) => self.synth_type_is_expression(value, ty, cs),
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
                self.synth_struct_literal(expression, lit, expectation, cs)
            }
            hir::ExpressionKind::Closure(closure) => {
                self.synth_closure_expression(expression, closure, expectation, cs)
            }
            hir::ExpressionKind::Await(inner) => {
                self.synth_await_expression(inner, expression.span, expectation, cs)
            }
            hir::ExpressionKind::Malformed => {
                unreachable!("ICE: trying to typecheck a malformed expression node")
            }
        }
    }
    pub(super) fn synth_cast_expression(
        &self,
        expression: &hir::Expression,
        value: &hir::Expression,
        target: &hir::Type,
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

        // The cast names its own result type. Any expectation is met by the
        // enclosing site's coercion, as for every other expression.
        target_ty
    }

    pub(super) fn synth_try_cast_expression(
        &self,
        value: &hir::Expression,
        target: &hir::Type,
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
        optional_ty
    }

    pub(super) fn synth_type_is_expression(
        &self,
        value: &hir::Expression,
        target: &hir::Type,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let target_ty = self.lower_type(target);
        self.add_type_constraints(target_ty, target.span, cs);
        let value_ty = self.synth(value, cs);

        if target_ty.is_error() || value_ty.is_error() {
            return Ty::error(gcx);
        }

        gcx.types.bool
    }

    pub(super) fn mutable_binding_for_resolution(
        &self,
        resolution: &hir::Resolution,
    ) -> Option<bool> {
        match resolution {
            hir::Resolution::LocalVariable(id) => Some(self.get_local(*id).mutable),
            hir::Resolution::Definition(id, DefinitionKind::ModuleVariable) => self
                .gcx()
                .try_get_static_mutability(*id)
                .map(|m| m == hir::Mutability::Mutable),
            _ => None,
        }
    }

    /// Deref returns a reference into independently addressed storage. Place
    /// checks must inspect that target rather than fields of the wrapper.
    fn receiver_place_info(&self, node: NodeID, cs: &Cs<'ctx>) -> Option<(Ty<'ctx>, bool, bool)> {
        let mut ty = cs.infer_cx.resolve_vars_if_possible(cs.expr_ty(node)?);
        let adjustments = cs.node_adjustments(node);
        if !adjustments
            .iter()
            .any(|adjustment| matches!(adjustment, Adjustment::DerefCall { .. }))
        {
            return Some((ty, false, true));
        }
        let mut writable = true;
        for adjustment in adjustments {
            match adjustment {
                Adjustment::DerefCall { result, .. } => {
                    ty = cs.structurally_resolve(*result);
                    writable = true;
                }
                Adjustment::Reference => ty = Ty::new(TyKind::Reference(ty), self.gcx()),
                Adjustment::Dereference => match ty.kind() {
                    TyKind::Reference(inner) => {
                        ty = inner;
                        writable = true;
                    }
                    TyKind::Pointer(inner, permission) => {
                        ty = inner;
                        writable = permission == hir::Mutability::Mutable
                            || self.gcx().is_class_type(inner);
                    }
                    _ => return None,
                },
                Adjustment::ClassUpcast { to } => ty = *to,
                _ => {}
            }
        }
        Some((cs.structurally_resolve(ty), true, writable))
    }

    pub(super) fn require_mut_place(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        if matches!(expr.kind, hir::ExpressionKind::MemberBrackets { .. }) {
            let selected = self
                .results
                .borrow()
                .selected_brackets
                .get(&expr.id)
                .cloned();
            return selected.is_some_and(|selected| self.require_mut_place(&selected, cs));
        }
        match &expr.kind {
            hir::ExpressionKind::Index { .. } => {
                self.receiver_is_addressable(expr, cs);
                self.index_place_requests.borrow_mut().insert(expr.id);
                true
            }
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
                let Some((ptr_ty, _, writable)) = self.receiver_place_info(inner.id, cs) else {
                    self.gcx()
                        .dcx()
                        .emit_error("missing type for deref operand".into(), Some(expr.span));
                    return false;
                };

                if !writable {
                    self.gcx().dcx().emit_error(
                        "cannot assign through a `*const` pointer".into(),
                        Some(expr.span),
                    );
                    return false;
                }
                let ptr_ty = cs.infer_cx.resolve_vars_if_possible(ptr_ty);
                if ptr_ty.contains_inference() {
                    return true;
                }
                match ptr_ty.kind() {
                    TyKind::Reference(_) => true,
                    TyKind::Pointer(_, mutbl) => {
                        if mutbl != hir::Mutability::Mutable {
                            self.gcx().dcx().emit_error(
                                "cannot assign through a `*const` pointer".into(),
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
                let Some((receiver_ty, shared_target, writable)) =
                    self.receiver_place_info(target.id, cs)
                else {
                    self.gcx()
                        .dcx()
                        .emit_error("missing type for member receiver".into(), Some(expr.span));
                    return false;
                };

                if !writable {
                    self.gcx().dcx().emit_error(
                        "cannot assign through a `*const` pointer".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                // Mutability through pointer/reference.
                let receiver_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
                if receiver_ty.contains_inference() {
                    return true;
                }
                let (base_ty, via_ptr_mut) = match receiver_ty.kind() {
                    TyKind::Reference(inner) => (inner, true),
                    TyKind::Pointer(inner, mutbl) => (inner, mutbl == hir::Mutability::Mutable),
                    _ => (receiver_ty, true),
                };

                if !via_ptr_mut && !self.gcx().is_class_type(base_ty) {
                    self.gcx().dcx().emit_error(
                        "cannot assign through a `*const` pointer".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                // A reference or `*mut` pointer grants access to its pointee
                // even when the binding holding it is immutable. Inline fields
                // instead inherit every containing place's mutability; recurse
                // so nested fields cannot bypass immutable or readonly ancestors.
                if !matches!(
                    receiver_ty.kind(),
                    TyKind::Pointer(..) | TyKind::Reference(..)
                ) && !shared_target
                    && !self.gcx().is_class_type(base_ty)
                    && !self.require_mut_place(target, cs)
                {
                    return false;
                }

                if let TyKind::Adt(def, _) = base_ty.kind()
                    && self.gcx().definition_kind(def.id) == DefinitionKind::Struct
                {
                    let struct_def = self
                        .gcx()
                        .source_struct_definition(base_ty)
                        .expect("struct source fields");
                    if let Some(field) = struct_def
                        .fields
                        .iter()
                        .find(|field| field.name == name.symbol)
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

                if cs.resolved_property_reads().contains_key(&expr.id) {
                    self.gcx().dcx().emit_error(
                        "cannot assign to a read-only property".into(),
                        Some(expr.span),
                    );
                    return false;
                }

                self.gcx().dcx().emit_error(
                    format!("unknown field '{}'", self.gcx().symbol_text(name.symbol)),
                    Some(expr.span),
                );
                false
            }
            hir::ExpressionKind::TupleAccess(target, _) => {
                let Some((receiver_ty, shared_target, writable)) =
                    self.receiver_place_info(target.id, cs)
                else {
                    return false;
                };

                if shared_target {
                    return writable;
                }

                match cs.infer_cx.resolve_vars_if_possible(receiver_ty).kind() {
                    TyKind::Reference(_) => true,
                    TyKind::Pointer(_, mutbl) => mutbl == hir::Mutability::Mutable,
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

    /// Autoref selects existing storage; it never invents a writable receiver
    /// temporary. Class members and explicit dereferences already select storage.
    pub(super) fn receiver_is_addressable(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        match &expr.kind {
            hir::ExpressionKind::MemberBrackets { .. } => {
                let selected = self
                    .results
                    .borrow()
                    .selected_brackets
                    .get(&expr.id)
                    .cloned();
                selected.is_some_and(|selected| self.receiver_is_addressable(&selected, cs))
            }
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => matches!(
                path.resolution,
                hir::Resolution::LocalVariable(_)
                    | hir::Resolution::Definition(_, DefinitionKind::ModuleVariable)
            ),
            hir::ExpressionKind::Index { .. } => {
                self.receiver_index_roots
                    .borrow_mut()
                    .insert(expr.id, vec![(expr.id, vec![])]);
                true
            }
            hir::ExpressionKind::Dereference(target) => cs.expr_ty(target.id).is_none_or(|ty| {
                !matches!(
                    cs.infer_cx.resolve_vars_if_possible(ty).kind(),
                    TyKind::Pointer(_, hir::Mutability::Immutable)
                )
            }),
            hir::ExpressionKind::Member { target, .. }
            | hir::ExpressionKind::TupleAccess(target, _) => {
                if self.results.borrow().property_read(expr.id).is_some()
                    || cs.resolved_property_reads().contains_key(&expr.id)
                {
                    return false;
                }
                if let Some((_, true, writable)) = self.receiver_place_info(target.id, cs) {
                    return writable;
                }
                if let Some(ty) = cs.expr_ty(target.id) {
                    let ty = cs.infer_cx.resolve_vars_if_possible(ty);
                    if let TyKind::Pointer(inner, hir::Mutability::Immutable) = ty.kind() {
                        return self.gcx().is_class_type(inner);
                    }
                    if matches!(
                        ty.kind(),
                        TyKind::Reference(_) | TyKind::Pointer(_, hir::Mutability::Mutable)
                    ) || self.gcx().is_class_type(ty)
                    {
                        return true;
                    }
                }
                let addressable = self.receiver_is_addressable(target, cs);
                let roots = self.receiver_index_roots.borrow().get(&target.id).cloned();
                if let Some(mut roots) = roots {
                    for (_, path) in &mut roots {
                        path.push(target.id);
                    }
                    self.receiver_index_roots
                        .borrow_mut()
                        .insert(expr.id, roots);
                }
                addressable
            }
            _ => false,
        }
    }

    /// A reference cannot grant write access to a raw const pointee. Reading a
    /// class handle still permits references into the shared object's fields.
    pub(super) fn require_reference_place(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        let receiver = match &expr.kind {
            hir::ExpressionKind::Dereference(target)
            | hir::ExpressionKind::Member { target, .. }
            | hir::ExpressionKind::TupleAccess(target, _) => Some(target.id),
            _ => None,
        };
        if let Some((_, true, writable)) =
            receiver.and_then(|node| self.receiver_place_info(node, cs))
        {
            if !writable {
                self.gcx().dcx().emit_error(
                    "cannot take a reference through a `*const` pointer".into(),
                    Some(expr.span),
                );
            }
            return writable;
        }
        let target = match &expr.kind {
            hir::ExpressionKind::Dereference(target) => target,
            hir::ExpressionKind::Member { target, .. }
            | hir::ExpressionKind::TupleAccess(target, _) => {
                if let Some(ty) = cs.expr_ty(target.id)
                    && !matches!(
                        cs.infer_cx.resolve_vars_if_possible(ty).kind(),
                        TyKind::Pointer(..)
                    )
                {
                    return self.require_reference_place(target, cs);
                }
                target
            }
            _ => return true,
        };
        let Some(ty) = cs.expr_ty(target.id) else {
            return true;
        };
        if let TyKind::Pointer(inner, hir::Mutability::Immutable) =
            cs.infer_cx.resolve_vars_if_possible(ty).kind()
            && !(matches!(expr.kind, hir::ExpressionKind::Member { .. })
                && self.gcx().is_class_type(inner))
        {
            self.gcx().dcx().emit_error(
                "cannot take a reference through a `*const` pointer".into(),
                Some(expr.span),
            );
            return false;
        }
        true
    }

    pub(super) fn synth_assign_expression(
        &self,
        expr: &hir::Expression,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Resolve a computed property before checking place requirements: an
        // interface property is discovered by the solver and is writable via
        // its setter even though it is not itself an addressable place.
        let lhs_ty = self.synth(lhs, cs);
        if lhs_ty.is_error() {
            return Ty::error(self.gcx());
        }
        if matches!(
            lhs.kind,
            hir::ExpressionKind::Member { .. }
                | hir::ExpressionKind::Dereference(_)
                | hir::ExpressionKind::TupleAccess(..)
        ) {
            cs.without_fallbacks(|cs| cs.solve_intermediate());
        }
        let initializes_self_field = if let hir::ExpressionKind::Member { target, .. } = &lhs.kind {
            matches!(&target.kind, hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if matches!(path.resolution, hir::Resolution::LocalVariable(id) if self.constructor_self.get() == Some(id)))
        } else {
            false
        };
        // This only admits direct assignment. MIR proves one-time readonly
        // initialization across branches/loops; mutable borrowing is unchanged.
        let initializes_self_field = initializes_self_field
            && cs.resolved_field_indices().contains_key(&lhs.id)
            && !matches!(&lhs.kind, hir::ExpressionKind::Member { target, .. } if cs.node_adjustments(target.id).iter().any(|adjustment| matches!(adjustment, Adjustment::DerefCall { .. })));
        let index_assignment = self.pending_indices.borrow().contains_key(&lhs.id);
        if index_assignment {
            self.index_setter_uses.borrow_mut().insert(lhs.id);
        }
        if !initializes_self_field && !index_assignment && !self.require_mut_place(lhs, cs) {
            return Ty::error(self.gcx());
        }

        // Type-check the RHS against the LHS type.
        let rhs_ty = self.synth_with_expectation(rhs, Some(lhs_ty), cs);
        if lhs_ty.is_error() || rhs_ty.is_error() {
            return Ty::error(self.gcx());
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

    pub(super) fn synth_block_expression(
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
        } else if crate::sema::tycheck::utils::divergence::ends_in_unbroken_loop(block) {
            Ty::new(TyKind::Never, self.gcx())
        } else {
            self.gcx().types.void
        }
    }

    pub(super) fn synth_unsafe_block_expression(
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

    /// Check a literal against an explicit suffix or an expected numeric type.
    pub(super) fn synth_expression_literal(
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

                    if !integer_expression_literal_fits(*value, ty) {
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
                    if !integer_expression_literal_fits(*value, ty) {
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

    pub(super) fn synth_identifier_expression(
        &self,
        node_id: NodeID,
        span: Span,
        resolution: &hir::Resolution,
        _expectation: Option<Ty<'ctx>>,
        instantiation_args: Option<GenericArguments<'ctx>>,
        static_owner: Option<Ty<'ctx>>,
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
                    DefinitionKind::Struct | DefinitionKind::Enum | DefinitionKind::TypeAlias => {
                        self.emit_type_name_value_error(span)
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
                    DefinitionKind::Module | DefinitionKind::Namespace => {
                        self.gcx().dcx().emit_error(
                            format!("a {} cannot be used as a value", kind.description()).into(),
                            Some(span),
                        );
                        Ty::error(self.gcx())
                    }
                    _ => {
                        if !allow_unsafe_callable_values
                            && self.is_unsafe_callable_definition(*id)
                            && matches!(
                                kind,
                                DefinitionKind::Function | DefinitionKind::AssociatedFunction
                            )
                        {
                            return self.emit_unsafe_callable_value_error(*id, span);
                        }
                        self.gcx().get_type(*id)
                    }
                }
            }
            hir::Resolution::SelfConstructor(..) => self.emit_type_name_value_error(span),
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
                        static_owner,
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
                        matches_async_preference: prefer_async.is_some_and(|want_async| {
                            self.gcx().definition_is_async(candidate) == want_async
                        }),
                        deref_steps: 0,
                    });
                }
                cs.add_goal(Goal::Disjunction(branches), span);
                ty
            }
            hir::Resolution::SelfTypeAlias(..) => self.emit_type_name_value_error(span),
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
                let kind = self.gcx().definition_kind(def_id);
                match kind {
                    DefinitionKind::Struct | DefinitionKind::Enum => {
                        self.emit_type_name_value_error(span)
                    }
                    _ => {
                        // For other types (interfaces, aliases), just return the type
                        self.gcx().get_type(def_id)
                    }
                }
            }
            hir::Resolution::Error => unreachable!(),
        }
    }

    /// A type path has no implicit value meaning. In particular, `new` is an
    /// ordinary associated factory, never an implicit constructor overload set.
    pub(super) fn emit_type_name_value_error(&self, span: Span) -> Ty<'ctx> {
        self.gcx().dcx().emit_error(
            "a type name cannot select `new` implicitly; use an explicit `::new` factory".into(),
            Some(span),
        );
        Ty::error(self.gcx())
    }

    pub(super) fn synth_call_expression(
        &self,
        expression: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        expect_ty: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        self.record_await_scope_call(expression.id);
        let prefer_async_call = self.call_is_awaited();
        // Opening is authority of this inferred call, never a conformance of
        // an explicitly named existential type or a stored generic wrapper.
        let inferred_path = match &callee.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => path
                .segments
                .last()
                .is_some_and(|segment| segment.arguments.is_none()),
            hir::ExpressionKind::Path(hir::ResolvedPath::Relative(_, segment)) => {
                segment.arguments.is_none()
            }
            _ => false,
        };
        if inferred_path {
            cs.allow_inferred_opening(callee.id);
        }

        // Select member brackets using normal lookup, but a following call
        // invokes the method directly. Reference results depend on its receiver,
        // not the lifetime of an unnecessary temporary callback environment.
        let mut prechecked_bracket_callee = None;
        if matches!(callee.kind, hir::ExpressionKind::MemberBrackets { .. }) {
            let prior = self.direct_method_selection.replace(Some(callee.id));
            let selected_ty = self.synth(callee, cs);
            self.direct_method_selection.set(prior);
            if selected_ty.is_error() {
                return selected_ty;
            }
            prechecked_bracket_callee = Some(selected_ty);
            let selected = self
                .results
                .borrow()
                .selected_brackets
                .get(&callee.id)
                .cloned();
            if let Some(hir::Expression {
                kind: hir::ExpressionKind::Member { target, name },
                ..
            }) = selected
                && let Some(source) = cs.resolved_overload_sources().get(&callee.id).copied()
            {
                let instantiation = cs.instantiation(callee.id).unwrap_or_default();
                self.results
                    .borrow_mut()
                    .selected_method_calls
                    .insert(expression.id, (source, instantiation));
                let method = hir::Expression {
                    id: expression.id,
                    span: expression.span,
                    kind: hir::ExpressionKind::MethodCall {
                        receiver: target.clone(),
                        name,
                        arguments: arguments.to_vec(),
                    },
                };
                self.results
                    .borrow_mut()
                    .elaborated_method_calls
                    .insert(expression.id, method.clone());
                let receiver_ty = cs.expr_ty(target.id).expect("checked specialized receiver");
                return self.with_prechecked_bracket_receiver(target.id, receiver_ty, || {
                    self.synth_method_call_expression(
                        &method, &target, &name, arguments, expect_ty, cs,
                    )
                });
            }
        }

        let mut constructor_result = None;
        let selected = self
            .results
            .borrow()
            .selected_method_calls
            .get(&expression.id)
            .copied();
        let callee_ty = if let Some(prechecked) = prechecked_bracket_callee {
            prechecked
        } else if let Some((source, arguments)) = selected {
            let ty = cs.infer_cx.next_ty_var(callee.span);
            cs.add_goal(
                Goal::BindOverload(BindOverloadGoalData {
                    static_owner: None,
                    node_id: callee.id,
                    var_ty: ty,
                    candidate_ty: self.gcx().get_type(source),
                    source,
                    instantiation_args: Some(arguments),
                }),
                callee.span,
            );
            cs.record_expr_ty(callee.id, ty);
            cs.without_fallbacks(|cs| cs.solve_intermediate());
            cs.structurally_resolve(ty)
        } else {
            match &callee.kind {
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
                    let resolution = match path {
                        hir::ResolvedPath::Resolved(path) => &path.resolution,
                        hir::ResolvedPath::Relative(_, segment) => &segment.resolution,
                    };
                    let is_type = match resolution {
                        hir::Resolution::Definition(
                            _,
                            DefinitionKind::Struct | DefinitionKind::TypeAlias,
                        )
                        | hir::Resolution::SelfTypeAlias(_) => true,
                        hir::Resolution::StdItem(item) => {
                            self.gcx().std_item_def(*item).is_some_and(|id| {
                                self.gcx().definition_kind(id) == DefinitionKind::Struct
                            })
                        }
                        _ => false,
                    };
                    let result_ty = if is_type {
                        let base = hir::Type {
                            id: callee.id,
                            kind: hir::TypeKind::Nominal(path.clone()),
                            span: callee.span,
                        };
                        let target = self.lower_type(&base);
                        self.add_type_constraints(target, base.span, cs);
                        constructor_result = Some(target);
                        let Some(head) = type_head_from_value_ty(target) else {
                            return self.emit_type_name_value_error(callee.span);
                        };
                        let name = crate::span::Identifier {
                            symbol: self.gcx().intern_symbol("init"),
                            span: callee.span,
                        };
                        let resolution = self.resolve_static_member_resolution(
                            head,
                            target,
                            &name,
                            callee.span,
                            true,
                        );
                        let resolution = self.narrow_callable_shape(resolution, arguments);
                        self.record_value_path_resolution(callee.id, &resolution);
                        // Extension parameters need not have the nominal type's
                        // order (or shape). Infer them through the constructor's
                        // result, just as for super.init, rather than reusing the
                        // class arguments positionally as extension arguments.
                        self.instantiate_value_path(
                            callee.id,
                            callee.span,
                            &resolution,
                            None,
                            None,
                            None,
                            true,
                            Some(prefer_async_call),
                            cs,
                        )
                    } else {
                        self.synth_path_expression_with_policy(
                            callee,
                            path,
                            None,
                            true,
                            Some(prefer_async_call),
                            cs,
                        )
                    };
                    cs.record_expr_ty(callee.id, result_ty);
                    result_ty
                }
                _ => self.synth(callee, cs),
            }
        };

        let callable_ty = self.callable_value_type(cs.structurally_resolve(callee_ty));
        let callee_def = self.resolve_callee(callee, cs);
        let arg_expectations = if !callee_ty.is_error() {
            self.argument_expectations_for_call(
                callee,
                arguments,
                callable_ty,
                constructor_result.or(expect_ty),
                callee_def,
                cs,
            )
        } else {
            None
        };

        let apply_arguments: Vec<ApplyArgument<'ctx>> = cs.with_deferred_callee(callee.id, |cs| {
            arguments
                .iter()
                .enumerate()
                .map(|(index, n)| {
                    let expected = arg_expectations
                        .as_ref()
                        .and_then(|items| items.get(index))
                        .and_then(|item| *item);
                    let ty = if let Some(expected) = expected {
                        let is_closure =
                            matches!(n.expression.kind, hir::ExpressionKind::Closure(_));
                        if is_closure {
                            self.with_closure_argument_context(
                                n.expression.id,
                                expected.expects_async_callable,
                                || {
                                    self.synth_with_expectation(
                                        &n.expression,
                                        Some(expected.ty),
                                        cs,
                                    )
                                },
                            )
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
                .collect()
        });

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
        if let Some(target) = constructor_result {
            cs.add_goal(Goal::ConstructorResult(result_ty, target), expression.span);
        }
        cs.record_expr_ty(expression.id, result_ty);

        let is_known_async_call = callee_def
            .is_some_and(|def_id| self.gcx().definition_is_async(def_id))
            || self.type_is_async_callable(callee_ty);
        if is_known_async_call {
            self.results.borrow_mut().record_async_call(expression.id);
        }

        let uses_function_overload_set = matches!(
            self.results.borrow().value_resolution(callee.id),
            Some(hir::Resolution::FunctionSet(_))
        ) || match &callee.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                matches!(path.resolution, hir::Resolution::FunctionSet(_))
            }
            hir::ExpressionKind::Path(hir::ResolvedPath::Relative(_, segment)) => {
                matches!(segment.resolution, hir::Resolution::FunctionSet(_))
            }
            _ => false,
        };
        let may_resolve_async_via_overload = uses_function_overload_set
            || matches!(callee.kind, hir::ExpressionKind::InferredMember { .. });

        let data = ApplyGoalData {
            call_node_id: expression.id,
            callee_node_id: Some(callee.id),
            call_span: expression.span,
            callee_ty,
            callee_source: callee_def,
            is_unsafe_context: self.unsafe_depth.get() > 0,
            result_ty,
            arguments: apply_arguments,
            skip_labels: false,
            input_only_selection: false,
        };
        cs.add_goal(Goal::Apply(data), expression.span);

        if !is_known_async_call
            && (may_resolve_async_via_overload || callee_ty.contains_inference())
        {
            self.defer_callable_async_surface_check(expression.id, callee.id, expression.span);
            return result_ty;
        }

        self.finish_async_call_surface_check(expression.id, expression.span, result_ty)
    }

    /// Arity and labels do not depend on argument types. Selecting a unique
    /// constructor shape before checking expressions supplies collection literals
    /// and callbacks with their context. Ambiguous type overloads stay unresolved.
    pub(super) fn narrow_callable_shape(
        &self,
        resolution: hir::Resolution,
        arguments: &[hir::ExpressionArgument],
    ) -> hir::Resolution {
        let hir::Resolution::FunctionSet(candidates) = &resolution else {
            return resolution;
        };
        let gcx = self.gcx();
        let matching: Vec<_> = candidates
            .iter()
            .copied()
            .filter(|&id| {
                let signature = gcx.get_signature(id);
                validate_arity(signature, arguments.len()).is_ok()
                    && match_arguments_to_parameters(
                        &signature.inputs,
                        signature.is_variadic,
                        arguments.iter().map(|argument| {
                            (
                                argument.label.map(|label| label.identifier),
                                argument.expression.span,
                            )
                        }),
                        false,
                    )
                    .is_ok()
            })
            .collect();
        if let [id] = matching.as_slice() {
            hir::Resolution::Definition(*id, gcx.definition_kind(*id))
        } else {
            resolution
        }
    }

    pub(super) fn argument_expectations_for_call(
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
            TyKind::FnPointer { inputs, output, .. } | TyKind::Closure { inputs, output, .. } => {
                (inputs.to_vec(), output)
            }
            _ => {
                let callable = crate::sema::tycheck::utils::callable::existential_callable(
                    self.gcx(),
                    callee_ty,
                )?;
                let (inputs, output) = callable.signature(self.gcx())?;
                (inputs.to_vec(), output)
            }
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
                    resolved.push(bound.fn_signature_ty.unwrap_or(instantiated_ty));
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

    pub(super) fn map_argument_expectations(
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

        self.map_argument_expectations_for_signature(
            &signature,
            parameter_tys,
            parameter_expects_async,
            arguments,
        )
    }

    fn map_argument_expectations_for_signature(
        &self,
        signature: &crate::sema::models::LabeledFunctionSignature<'ctx>,
        parameter_tys: &[Ty<'ctx>],
        parameter_expects_async: &[bool],
        arguments: &[hir::ExpressionArgument],
    ) -> Option<Vec<Option<ArgumentExpectation<'ctx>>>> {
        validate_arity(signature, arguments.len()).ok()?;
        let positions = match_arguments_to_parameters(
            &signature.inputs,
            signature.is_variadic,
            arguments
                .iter()
                .map(|arg| (arg.label.map(|label| label.identifier), arg.expression.span)),
            false,
        )
        .ok()?;

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
    pub(super) fn try_resolve_fn_bound(
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

                let Some(kind) = crate::sema::models::callable_kind(gcx, interface.id) else {
                    continue;
                };
                let expects_async_callable = kind == crate::sema::models::ClosureKind::AsyncFn;

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

                // An unknown Args pack does not imply one closure parameter.
                // Preserve the async expectation while conformance inference
                // determines its arity from the actual closure inputs.
                let fn_signature_ty = match args_ty.kind() {
                    TyKind::Tuple(inputs) => {
                        Some(gcx.store.interners.intern_ty(TyKind::FnPointer {
                            effects: crate::sema::models::FunctionPointerEffects {
                                kind,
                                ..Default::default()
                            },
                            inputs,
                            output: output_ty,
                        }))
                    }
                    _ => None,
                };
                return Some(ResolvedCallableBound {
                    fn_signature_ty,
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
    pub(super) fn infer_call_generic_args(
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

    pub(super) fn record_generic_bindings_from_ty(
        pattern: Ty<'ctx>,
        actual: Ty<'ctx>,
        inferred: &mut [Option<GenericArgument<'ctx>>],
    ) {
        match pattern.kind() {
            TyKind::Parameter(param) => {
                Self::record_generic_binding(param.index, GenericArgument::Type(actual), inferred);
            }
            TyKind::Reference(pattern_inner) | TyKind::Pointer(pattern_inner, _) => {
                if let TyKind::Reference(actual_inner) | TyKind::Pointer(actual_inner, _) =
                    actual.kind()
                {
                    Self::record_generic_bindings_from_ty(pattern_inner, actual_inner, inferred);
                }
            }
            TyKind::Array {
                element: pattern_element,
                len: pattern_len,
            } => {
                let TyKind::Array {
                    element: actual_element,
                    len: actual_len,
                } = actual.kind()
                else {
                    return;
                };
                Self::record_generic_bindings_from_ty(pattern_element, actual_element, inferred);
                Self::record_generic_bindings_from_const(pattern_len, actual_len, inferred);
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
                effects: _,
                inputs: pattern_inputs,
                output: pattern_output,
            } => {
                let TyKind::FnPointer {
                    effects: _,
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

    pub(super) fn record_generic_bindings_from_arg(
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

    pub(super) fn record_generic_bindings_from_const(
        pattern: Const<'ctx>,
        actual: Const<'ctx>,
        inferred: &mut [Option<GenericArgument<'ctx>>],
    ) {
        if let ConstKind::Param(param) = pattern.kind {
            Self::record_generic_binding(param.index, GenericArgument::Const(actual), inferred);
        }
        Self::record_generic_bindings_from_ty(pattern.ty, actual.ty, inferred);
    }

    pub(super) fn record_generic_binding(
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

    pub(super) fn inferred_member_argument_expectations(
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
        let mut base_ty = cs.infer_cx.resolve_vars_if_possible(base_ty);

        let head = type_head_from_value_ty(base_ty)?;
        let mut resolution =
            self.resolve_static_member_resolution(head, base_ty, name, span, false);
        // An overload set is still a successful outer lookup. Its own
        // signatures, rather than a success factory, must guide the arguments.
        if matches!(resolution, hir::Resolution::Error)
            && let Some((success, _)) = self.gcx().result_parts(base_ty)
        {
            let success = cs.structurally_resolve(success);
            let head = type_head_from_value_ty(success)?;
            resolution = self.resolve_static_member_resolution(head, success, name, span, false);
            base_ty = success;
        }
        let base_args = match base_ty.kind() {
            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
            _ => None,
        };

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

    pub(super) fn synth_method_call_expression(
        &self,
        expression: &hir::Expression,
        receiver: &hir::Expression,
        name: &crate::span::Identifier,
        arguments: &[hir::ExpressionArgument],
        expect_ty: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        self.record_await_scope_call(expression.id);
        let prefer_async_call = self.call_is_awaited();

        if name.symbol.as_str() == "init"
            && matches!(&receiver.kind, hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if path.segments.len() == 1 && path.segments[0].identifier.symbol.as_str() == "self"
                    && matches!(path.resolution, hir::Resolution::LocalVariable(id) if self.constructor_self.get() == Some(id)))
        {
            return self.synth_self_initializer(expression, receiver, name, arguments, cs);
        }
        // Static member invocation on a type (e.g., `List[Int].new()`).
        if name.symbol.as_str() == "init"
            && matches!(&receiver.kind, hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if path.segments.len() == 1 && path.segments[0].identifier.symbol.as_str() == "super")
        {
            return self.synth_base_initializer(expression, receiver, name, arguments, cs);
        }
        if let hir::ExpressionKind::Path(path) = &receiver.kind {
            let (resolution, base_args, _) =
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
                            Some(base_ty),
                            cs,
                        );
                        let callee_ty = self.instantiate_value_path(
                            receiver.id,
                            receiver.span,
                            &resolution,
                            instantiation_args,
                            Some(base_ty),
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
                            callee_node_id: None,
                            call_span: expression.span,
                            callee_ty,
                            callee_source: resolution.definition_id(),
                            is_unsafe_context: self.unsafe_depth.get() > 0,
                            result_ty,
                            arguments: apply_arguments,
                            skip_labels: false,
                            input_only_selection: false,
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

        let is_super = matches!(&receiver.kind,hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) if path.segments.len() == 1 && path.segments[0].identifier.symbol.as_str() == "super");
        let recv_ty = if is_super {
            let hir::ExpressionKind::Path(path) = &receiver.kind else {
                unreachable!()
            };
            let original =
                self.synth_path_expression_with_policy(receiver, path, None, false, None, cs);
            cs.record_expr_ty(receiver.id, original);
            if let Some(base) = self.gcx().class_base(original) {
                let target = base;
                cs.append_adjustments(
                    receiver.id,
                    vec![crate::sema::tycheck::solve::Adjustment::ClassUpcast { to: target }],
                );
                self.gcx()
                    .store
                    .class_super_calls
                    .borrow_mut()
                    .entry(self.gcx().package_index())
                    .or_default()
                    .insert(expression.span);
                target
            } else {
                self.gcx().dcx().emit_error(
                    "super requires an instance receiver with a base class".into(),
                    Some(receiver.span),
                );
                Ty::error(self.gcx())
            }
        } else {
            self.synth(receiver, cs)
        };
        // Collection literals need the receiver's parameter types even when
        // it was inferred from an earlier expression, such as a pointer cast.
        // Keep closure inference on its existing path: its speculative callable
        // expectations use variables separate from the selected method's args.
        let has_collection_argument = arguments.iter().any(|arg| {
            matches!(
                arg.expression.kind,
                hir::ExpressionKind::Array(_) | hir::ExpressionKind::Tuple(_)
            )
        });
        if has_collection_argument && cs.infer_cx.resolve_vars_if_possible(recv_ty).is_infer() {
            cs.solve_intermediate();
        }
        let arg_expectations = if recv_ty.is_error() {
            None
        } else {
            self.method_argument_expectations(recv_ty, name, arguments, expression.span, cs)
        };

        let args: Vec<ApplyArgument<'ctx>> = arguments
            .iter()
            .enumerate()
            .map(|(index, n)| {
                let expected = arg_expectations
                    .as_ref()
                    .and_then(|items| items.get(index))
                    .and_then(|item| *item);
                let ty = if let Some(expected) = expected {
                    let is_closure = matches!(n.expression.kind, hir::ExpressionKind::Closure(_));
                    if is_closure {
                        self.with_closure_argument_context(
                            n.expression.id,
                            expected.expects_async_callable,
                            || self.synth_with_expectation(&n.expression, Some(expected.ty), cs),
                        )
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
                receiver_addressable: self.receiver_is_addressable(receiver, cs),
                selected: self
                    .results
                    .borrow()
                    .selected_method_calls
                    .get(&expression.id)
                    .copied(),
                node_id: expression.id,
                receiver: recv_ty,
                reciever_node: receiver.id,
                reciever_span: receiver.span,
                is_unsafe_context: self.unsafe_depth.get() > 0,
                method_ty: method_ty,
                prefer_async: prefer_async_call,
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
    pub(super) fn method_argument_expectations(
        &self,
        receiver_ty: Ty<'ctx>,
        name: &crate::span::Identifier,
        arguments: &[hir::ExpressionArgument],
        _span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Option<Vec<Option<ArgumentExpectation<'ctx>>>> {
        let gcx = self.gcx();

        let mut candidate_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
        if candidate_ty.is_error() || candidate_ty.is_infer() {
            return None;
        }

        // Method resolution considers every autoderef level. Keep the receiver
        // type paired with each candidate: it supplies the right substitutions
        // for pointer/array impls, while an inapplicable same-named method at an
        // earlier level must not hide a viable method on the pointee.
        let mut candidates = Vec::new();
        loop {
            // Inherited methods are declared in their owner's coordinates.
            // Pair them with that instantiated ancestor before supplying a
            // collection/callback context, just as actual method lookup does.
            let ancestry = gcx.class_ancestry(candidate_ty);
            let owners = if ancestry.is_empty() {
                vec![candidate_ty]
            } else {
                ancestry
            };
            for owner in owners {
                for lookup in [owner, Ty::new(TyKind::Reference(owner), gcx)] {
                    if let Some(head) = type_head_from_value_ty(lookup) {
                        for def_id in self.collect_inherent_instance_candidates(head, name.symbol) {
                            let applicable = gcx.definition_parent(def_id)
                                .and_then(|parent| gcx.get_impl_target_ty(parent).map(|target| (parent, target)))
                                .is_none_or(|(parent, target)| cs.infer_cx.probe(|_| {
                                    let arguments = cs.infer_cx.fresh_args_for_def(parent, name.span);
                                    let target = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(gcx, target, arguments);
                                    crate::sema::tycheck::utils::unify::TypeUnifier::new(cs.infer_cx.clone())
                                        .unify(
                                            crate::sema::tycheck::utils::normalize_aliases(gcx, target),
                                            crate::sema::tycheck::utils::normalize_aliases(gcx, lookup),
                                        ).is_ok()
                                }));
                            if applicable {
                                candidates.push((lookup, def_id));
                            }
                        }
                    }
                }
            }

            let Some(inner) = candidate_ty.dereference() else {
                break;
            };
            candidate_ty = cs.infer_cx.resolve_vars_if_possible(inner);
            if candidate_ty.is_error() || candidate_ty.is_infer() {
                break;
            }
        }
        if candidates.is_empty() {
            return None;
        }

        // An explicit &T finds the same &T extension both directly and by
        // dereferencing then auto-referencing T. Freshening that candidate twice
        // creates unrelated callable-output variables and discards its context.
        let mut seen_candidates = rustc_hash::FxHashSet::default();
        candidates.retain(|candidate| seen_candidates.insert(*candidate));
        let mut candidate_inputs: Vec<Vec<Option<ArgumentExpectation<'ctx>>>> = vec![];

        for (base_ty, def_id) in candidates {
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
                let mut inferred = vec![None; identity_args.len()];

                if generics.parent_count > 0 {
                    let Some(parent) = generics.parent else {
                        continue;
                    };
                    let Some(impl_target) = gcx.get_impl_target_ty(parent) else {
                        continue;
                    };
                    Self::record_generic_bindings_from_ty(
                        crate::sema::tycheck::utils::normalize_aliases(gcx, impl_target),
                        crate::sema::tycheck::utils::normalize_aliases(gcx, base_ty),
                        &mut inferred,
                    );
                    if inferred
                        .iter()
                        .take(generics.parent_count)
                        .any(Option::is_none)
                    {
                        continue;
                    }
                }

                let args = identity_args
                    .iter()
                    .enumerate()
                    .map(|(index, identity)| inferred[index].unwrap_or(*identity))
                    .collect();
                Some(gcx.store.interners.intern_generic_args(args))
            };
            let mut signature = if let Some(args) = instantiation_args {
                instantiate_signature_with_args(gcx, signature, args)
            } else {
                signature.clone()
            };

            let instantiated_inputs: Vec<Ty<'ctx>> =
                signature.inputs.iter().map(|input| input.ty).collect();
            if instantiated_inputs.is_empty() {
                continue;
            }

            let mut parameter_tys = Vec::with_capacity(instantiated_inputs.len().saturating_sub(1));
            let mut parameter_expects_async =
                Vec::with_capacity(instantiated_inputs.len().saturating_sub(1));
            for (&original_ty, &instantiated_ty) in original_inputs
                .iter()
                .skip(1)
                .zip(instantiated_inputs.iter().skip(1))
            {
                if let Some(bound_args) = instantiation_args
                    && let Some(bound) = self.try_resolve_fn_bound(original_ty, def_id, bound_args)
                {
                    let expectation_ty = self.freshen_method_expectation_ty(
                        def_id,
                        bound.fn_signature_ty.unwrap_or(instantiated_ty),
                        name.span,
                        cs,
                    );
                    parameter_tys.push(expectation_ty);
                    parameter_expects_async.push(bound.expects_async_callable);
                } else {
                    // A method-local type parameter is inferred by the selected
                    // call candidate. Creating an unrelated inference variable
                    // here only supplies a speculative argument expectation;
                    // it is not shared with overload selection and can survive
                    // as a false "could not be inferred" diagnostic even when
                    // the real candidate is fully determined by the argument.
                    // Callable bounds take the branch above because closures do
                    // need their parameter/result types before their bodies are
                    // checked. Ordinary generic values are synthesized without
                    // an expectation and constrained by the Apply goal instead.
                    let own_generics = self.gcx().generics_of(def_id);
                    let mentions_method_parameter = own_generics
                        .parameters
                        .iter()
                        .any(|param| type_mentions_generic_parameter(instantiated_ty, param.index));
                    if mentions_method_parameter {
                        return None;
                    }

                    parameter_tys.push(instantiated_ty);
                    parameter_expects_async.push(self.ty_is_known_async_callable(instantiated_ty));
                }
            }

            if signature.inputs.is_empty() {
                continue;
            }
            signature.inputs.remove(0);

            let Some(input_expectations) = self.map_argument_expectations_for_signature(
                &signature,
                &parameter_tys,
                &parameter_expects_async,
                arguments,
            ) else {
                continue;
            };
            candidate_inputs.push(input_expectations);
        }

        if candidate_inputs.is_empty() {
            return None;
        }

        let first = candidate_inputs[0].clone();
        if candidate_inputs.iter().all(|inputs| *inputs == first) {
            Some(first)
        } else {
            None
        }
    }

    pub(super) fn freshen_method_expectation_ty(
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
                TyKind::Reference(inner) | TyKind::Pointer(inner, _) => {
                    collect_generic_param_indices(inner, indices);
                }
                TyKind::Tuple(items) => {
                    for &item in items.iter() {
                        collect_generic_param_indices(item, indices);
                    }
                }
                TyKind::FnPointer { inputs, output, .. } => {
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

        let mut args: Vec<GenericArgument<'ctx>> =
            GenericsBuilder::identity_for_item(self.gcx(), def_id)
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

    pub(super) fn collect_inherent_instance_candidates(
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

    pub(super) fn synth_if_expression(
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
                let resolved_then = cs.infer_cx.resolve_vars_if_possible(then_ty);
                let resolved_else = cs.infer_cx.resolve_vars_if_possible(else_ty);

                // A desugared `while` ends in `if condition { body } else {
                // break }`. When every path through `body` also returns or
                // continues, both branches are `Never`. Do not create a fresh
                // result variable that neither diverging branch can bind.
                if expectation.is_none()
                    && matches!(resolved_then.kind(), TyKind::Never)
                    && matches!(resolved_else.kind(), TyKind::Never)
                {
                    return Ty::new(TyKind::Never, self.gcx());
                }

                let result_ty =
                    expectation.unwrap_or_else(|| cs.infer_cx.next_ty_var(expression.span));

                if expectation.is_some() || matches!(resolved_then.kind(), TyKind::Never) {
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
                if expectation.is_some() || matches!(resolved_else.kind(), TyKind::Never) {
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

    pub(super) fn synth_pattern_binding_expression(
        &self,
        _expression: &hir::Expression,
        condition: &hir::PatternBindingCondition,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let source_name = condition.source.diagnostic_name();

        // Typecheck the expression being matched
        let expr_ty = self.synth(&condition.expression, cs);
        if expr_ty.is_error() {
            GatherLocalsVisitor::from_binding_condition(cs, self, condition);
            self.mark_pattern_bindings_error(&condition.pattern);
            return Ty::error(self.gcx());
        }

        // Resolve pending inference before the Optional-shape check so a
        // freshly-synthesized scrutinee isn't misreported as non-Optional.
        cs.solve_intermediate();
        let expr_ty = cs.infer_cx.resolve_vars_if_possible(expr_ty);

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
        GatherLocalsVisitor::from_binding_condition(cs, self, condition);

        // Check the pattern against the expression's type
        let scrutinee_id = condition.expression.id;
        self.check_pattern(&condition.pattern, expr_ty, scrutinee_id, cs);
        cs.solve_intermediate();

        // Pattern binding conditions always evaluate to bool
        self.gcx().types.bool
    }

    pub(super) fn synth_match_expression(
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
                self.commit_constraint_results(&mut scrutinee_cs);
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

                if !matches!(resolved_arm_ty.kind(), TyKind::Never) {
                    all_arms_never = false;
                }
                // Contextual arms use ordinary coercions. Without a supplied
                // result type, equality retains common-type inference; Never
                // never binds that common type on its own.
                if had_expectation || matches!(resolved_arm_ty.kind(), TyKind::Never) {
                    arm_cs.add_goal(
                        Goal::Coerce {
                            node_id: arm.body.id,
                            from: arm_ty,
                            to: result_ty,
                        },
                        arm.body.span,
                    );
                } else {
                    arm_cs.equal(result_ty, arm_ty, arm.body.span);
                }

                // Solve and commit each arm independently
                arm_cs.solve_intermediate();
                self.commit_constraint_results(&mut arm_cs);
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

    pub(super) fn synth_optional_unwrap_match(
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

                self.commit_constraint_results(&mut arm_cs);
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
            self.commit_constraint_results(&mut none_cs);
            cs.merge(none_cs);

            let resolved = shared_infer_cx.resolve_vars_if_possible(result_ty);
            if resolved.is_infer() {
                Ty::error(self.gcx())
            } else {
                resolved
            }
        })
    }

    pub(super) fn synth_unary_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::UnaryOperator,
        operand: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Numeric expectations guide literals, but boxing/Optional wrapping
        // belongs to the completed expression, not its operand.
        let numeric_expectation = expectation.filter(|ty| {
            matches!(
                cs.structurally_resolve(*ty).kind(),
                TyKind::Int(_) | TyKind::UInt(_) | TyKind::Float(_)
            )
        });
        let operand_expectation = match operator {
            hir::UnaryOperator::Negate | hir::UnaryOperator::BitwiseNot => numeric_expectation,
            _ => None,
        };
        let operand_ty = self.synth_with_expectation(operand, operand_expectation, cs);
        if operand_ty.is_error() {
            return Ty::error(self.gcx());
        }
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = UnOpGoalData {
            receiver_addressable: self.receiver_is_addressable(operand, cs),
            lhs: operand_ty,
            rho: result_ty,
            operator,
            span: expression.span,
            node_id: expression.id,
            rhs_id: operand.id,
        };

        cs.add_goal(Goal::UnaryOp(data), expression.span);
        result_ty
    }

    pub(super) fn synth_binary_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::BinaryOperator,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Only a numeric expectation can guide the operands' literal types.
        // Forwarding an erased/Optional result type into nested operators would
        // coerce their results before this operator consumes them.
        let numeric_expectation = expectation.filter(|ty| {
            matches!(
                cs.structurally_resolve(*ty).kind(),
                TyKind::Int(_) | TyKind::UInt(_) | TyKind::Float(_)
            )
        });
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
            | hir::BinaryOperator::BitShr => numeric_expectation,
            // Comparison/boolean ops return bool, not operand type
            _ => None,
        };
        let lhs_ty = self.synth_with_expectation(lhs, operand_expectation, cs);
        // Only primitive arithmetic has the same operand/result type. A
        // custom operator's associated Output never supplies its RHS type.
        let rhs_expectation = match cs.structurally_resolve(lhs_ty).kind() {
            TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Infer(
                crate::sema::models::InferTy::IntVar(_) | crate::sema::models::InferTy::FloatVar(_),
            ) => operand_expectation,
            _ => None,
        };
        let rhs_ty = self.synth_with_expectation(rhs, rhs_expectation, cs);
        if lhs_ty.is_error() || rhs_ty.is_error() {
            return Ty::error(self.gcx());
        }
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = BinOpGoalData {
            receiver_addressable: self.receiver_is_addressable(lhs, cs),
            lhs: lhs_ty,
            rhs: rhs_ty,
            rho: result_ty,
            operator,
            span: expression.span,
            node_id: expression.id,
            lhs_id: lhs.id,
            rhs_id: rhs.id,
        };

        cs.add_goal(Goal::BinaryOp(data), expression.span);
        result_ty
    }

    pub(super) fn synth_assign_op_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::BinaryOperator,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Evaluate the receiver once. Whether its caller slot must be writable
        // depends on the selected operator, not merely assignment syntax.
        let lhs_ty = self.synth(lhs, cs);
        if lhs_ty.is_error() {
            return Ty::error(self.gcx());
        }
        cs.solve_intermediate();

        let rhs_ty = self.synth(rhs, cs);
        if rhs_ty.is_error() {
            return Ty::error(self.gcx());
        }

        let data = AssignOpGoalData {
            receiver_addressable: self.receiver_is_addressable(lhs, cs),
            lhs: lhs_ty,
            rhs: rhs_ty,
            operator,
            span: expression.span,
            node_id: expression.id,
            lhs_id: lhs.id,
            rhs_id: rhs.id,
        };

        cs.add_goal(Goal::AssignOp(data), expression.span);
        self.pending_compound_assignments
            .borrow_mut()
            .push((expression.id, lhs.clone()));

        // Assign ops return void/unit
        self.gcx().types.void
    }

    /// Only intrinsic writeback assigns the caller's slot. Custom operators
    /// use ordinary method semantics, including writable reference values.
    pub(super) fn finalize_compound_assignments(&self, cs: &mut Cs<'ctx>) {
        let pending = std::mem::take(&mut *self.pending_compound_assignments.borrow_mut());
        let overloads = cs.resolved_overload_sources();
        let properties = cs.resolved_property_reads();
        for (node, lhs) in pending {
            if cs.expr_ty(lhs.id).is_none() {
                self.pending_compound_assignments
                    .borrow_mut()
                    .push((node, lhs));
                continue;
            }
            if overloads.contains_key(&node) {
                continue;
            }
            if self.pending_indices.borrow().contains_key(&lhs.id) {
                self.index_compound_uses.borrow_mut().insert(lhs.id);
                continue;
            }
            let Some(_) = properties.get(&lhs.id) else {
                self.require_mut_place(&lhs, cs);
                continue;
            };
            let hir::ExpressionKind::Member { name, .. } = &lhs.kind else {
                unreachable!("property compound assignment must originate from a member");
            };
            self.gcx().dcx().emit_error(
                format!("cannot apply compound assignment to read-only property '{}'; property has no setter", self.gcx().symbol_text(name.symbol)),
                Some(lhs.span),
            );
        }
    }

    pub(super) fn synth_path_expression_with_policy(
        &self,
        expression: &hir::Expression,
        path: &hir::ResolvedPath,
        expectation: Option<Ty<'ctx>>,
        allow_unsafe_callable_values: bool,
        prefer_async: Option<bool>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let (resolution, base_args, static_owner) =
            self.resolve_value_path_resolution_with_args(path, expression.span, true, cs);
        self.record_value_path_resolution(expression.id, &resolution);
        let segment = match path {
            hir::ResolvedPath::Resolved(path) => {
                path.segments.last().expect("path must have segments")
            }
            hir::ResolvedPath::Relative(_, segment) => segment,
        };
        let instantiation_args = self.lower_value_path_instantiation_args(
            &resolution,
            segment,
            base_args,
            static_owner,
            cs,
        );
        // Note: For relative paths like `Optional.some`, we don't need to add type constraints
        // for the base type `Optional` since it's only used for name resolution, not as a value.
        // Adding constraints here creates spurious type variables that cause inference failures.
        self.instantiate_value_path(
            expression.id,
            expression.span,
            &resolution,
            instantiation_args,
            static_owner,
            expectation,
            allow_unsafe_callable_values,
            prefer_async,
            cs,
        )
    }

    pub(super) fn synth_path_expression(
        &self,
        expression: &hir::Expression,
        path: &hir::ResolvedPath,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        if matches!(path,hir::ResolvedPath::Resolved(path) if path.segments.len() == 1 && path.segments[0].identifier.symbol.as_str() == "super")
        {
            self.gcx().dcx().emit_error(
                "super is only valid as the receiver of a base method call".into(),
                Some(expression.span),
            );
            return Ty::error(self.gcx());
        }
        self.synth_path_expression_with_policy(expression, path, expectation, false, None, cs)
    }

    pub(super) fn synth_member_expression(
        &self,
        expression: &hir::Expression,
        target: &hir::Expression,
        name: &crate::span::Identifier,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        self.synth_member_expression_with_arguments(expression, target, name, expectation, None, cs)
    }

    pub(super) fn synth_member_expression_with_arguments(
        &self,
        expression: &hir::Expression,
        target: &hir::Expression,
        name: &crate::span::Identifier,
        expectation: Option<Ty<'ctx>>,
        explicit_arguments: Option<&hir::TypeArguments>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        cs.without_fallbacks(|cs| {
            // Earlier declarations may still constrain this receiver. The call
            // checker separately defers its unfinished callee overload.
            // Instance receiver (`value.member`) uses synthesized receiver type.
            let receiver_ty = self.synth_with_expectation(target, None, cs);
            if receiver_ty.is_error() {
                return Ty::error(self.gcx());
            }
            if matches!(
                &target.kind,
                hir::ExpressionKind::Path(hir::ResolvedPath::Relative(..))
            ) {
                // Resolution cannot distinguish an associated type from a value
                // when parsing a chain such as `Self::member.field`. Once known,
                // a type must still use `::`, never fictitious instance storage.
                let resolution = self.results.borrow().value_resolution(target.id);
                if matches!(
                    resolution,
                    Some(
                        hir::Resolution::Definition(
                            _,
                            DefinitionKind::AssociatedType
                                | DefinitionKind::TypeAlias
                                | DefinitionKind::TypeParameter
                                | DefinitionKind::Struct
                                | DefinitionKind::Enum
                                | DefinitionKind::Interface
                        ) | hir::Resolution::SelfConstructor(..)
                            | hir::Resolution::SelfTypeAlias(..)
                            | hir::Resolution::InterfaceSelfTypeParameter(..)
                            | hir::Resolution::PrimaryType(..)
                    )
                ) {
                    self.gcx().dcx().emit_error(
                        format!("qualified access to `{}` requires `::`", name.symbol).into(),
                        Some(crate::span::Span {
                            start: target.span.end,
                            end: name.span.start,
                            file: expression.span.file,
                        }),
                    );
                    return Ty::error(self.gcx());
                }
            }
            let receiver_adjustments = cs.receiver_adjustments(target.id);

            // A field read on an already-known struct has a known type, so bind it
            // now instead of leaving a variable for the member goal to resolve.
            // Consumers that run before the deferred queue drains — argument
            // expectations for `receiver.field.method(...)`, most visibly — would
            // otherwise see an unresolved receiver and give up. The goal is still
            // emitted, and equating it against this type turns a mismatch into a
            // reported error rather than a silent divergence.
            let known_field = self.known_field_ty(receiver_ty, name.symbol, cs);
            let result_ty = known_field.unwrap_or_else(|| cs.infer_cx.next_ty_var(expression.span));
            let signature_hint = expectation.and_then(|expected| {
                let inputs = self.extract_closure_expected_inputs(expected, cs)?;
                let output = self.extract_closure_expected_output(expected, cs)?;
                Some(Ty::new(
                    TyKind::FnPointer {
                        effects: Default::default(),
                        inputs: self.gcx().store.interners.intern_ty_list(inputs),
                        output,
                    },
                    self.gcx(),
                ))
            });
            cs.add_goal(
                Goal::Member(MemberGoalData {
                    classify_only: false,
                    receiver_addressable: self.receiver_is_addressable(target, cs),
                    explicit_arguments: explicit_arguments.cloned(),
                    node_id: expression.id,
                    receiver_node: target.id,
                    receiver: receiver_ty,
                    signature_hint,
                    name: *name,
                    result: result_ty,
                    span: expression.span,
                }),
                expression.span,
            );

            // Ordinary known fields need no callable environment. Keep their
            // goals deferred, as before, instead of repeatedly draining the
            // solver for every field in a large function.
            if known_field.is_some() {
                return result_ty;
            }
            cs.solve_intermediate();
            if !cs.resolved_field_indices().contains_key(&expression.id)
                && !cs.resolved_property_reads().contains_key(&expression.id)
                && let Some(source) = cs.resolved_overload_sources().get(&expression.id).copied()
                && matches!(
                    cs.structurally_resolve(result_ty).kind(),
                    TyKind::FnPointer { .. }
                )
            {
                if self.direct_method_selection.get() == Some(expression.id) {
                    cs.restore_receiver_adjustments(target.id, receiver_adjustments);
                    return cs.structurally_resolve(result_ty);
                }
                return self.synth_bound_method(
                    expression,
                    target,
                    *name,
                    source,
                    cs.structurally_resolve(result_ty),
                    cs,
                );
            }

            // The expectation is only a hint here. Equating it with the member's
            // result would force the field type to match exactly and defeat any
            // coercion the consuming context applies, such as boxing into an
            // existential or wrapping into an `Optional`. Contexts that require a
            // conversion emit their own coercion goal for this node.
            let _ = expectation;
            result_ty
        })
    }

    pub(super) fn synth_inferred_member_expression(
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

        result_ty
    }

    /// Type of the field `name` reached from `receiver_ty`, when that is already
    /// determined.
    ///
    /// Mirrors what `solve_member` does for a field: autoderef, then look the
    /// name up on the struct. Autoderef only peels references and pointers, and
    /// neither carries fields, so checking the fully peeled type alone cannot
    /// disagree about which field is found. Anything the member goal resolves by
    /// another route — a computed property, an interface requirement — returns
    /// `None` here and is left to that goal.
    fn known_field_ty(
        &self,
        receiver_ty: Ty<'ctx>,
        name: Symbol,
        cs: &mut Cs<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let mut base_ty = cs.infer_cx.resolve_vars_if_possible(receiver_ty);
        loop {
            if base_ty.is_error() || base_ty.is_infer() {
                return None;
            }
            match base_ty.kind() {
                TyKind::Reference(inner) | TyKind::Pointer(inner, _) => {
                    base_ty = cs.infer_cx.resolve_vars_if_possible(inner);
                }
                _ => break,
            }
        }

        let TyKind::Adt(def, args) = base_ty.kind() else {
            return None;
        };
        if self.gcx().definition_kind(def.id) != DefinitionKind::Struct {
            return None;
        }
        let struct_def = self.gcx().get_struct_definition(def.id);
        let struct_def =
            crate::sema::tycheck::utils::instantiate::instantiate_struct_definition_with_args(
                self.gcx(),
                struct_def,
                args,
            );
        let field = struct_def.fields.iter().find(|field| field.name == name)?;
        // An inaccessible field is an error the member goal reports; binding its
        // type here would only hide that.
        if !self
            .gcx()
            .is_visibility_allowed(field.visibility, self.current_def)
        {
            return None;
        }
        Some(field.ty)
    }

    pub(super) fn synth_struct_literal(
        &self,
        expression: &hir::Expression,
        lit: &hir::StructLiteral,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let span = expression.span;
        let (mut struct_ty, constructor, type_span) = match &lit.path {
            hir::ConstructorPath::Qualified { path } => {
                let type_span = match path {
                    hir::ResolvedPath::Resolved(path) => path.span,
                    hir::ResolvedPath::Relative(_, segment) => segment.span,
                };
                let (resolution, args, _) =
                    self.resolve_value_path_resolution_with_args(path, type_span, false, cs);
                if matches!(
                    resolution,
                    hir::Resolution::Definition(_, DefinitionKind::VariantConstructor(..))
                ) {
                    self.record_value_path_resolution(expression.id, &resolution);
                    let context = cs.infer_cx.next_ty_var(span);
                    let Some((variant, ty)) = self.resolve_enum_variant_from_resolution(
                        context, resolution, type_span, cs, args,
                    ) else {
                        return Ty::error(gcx);
                    };
                    if !self.require_struct_variant(variant, type_span) {
                        return Ty::error(gcx);
                    }
                    (
                        ty,
                        LiteralConstructor::Variant(variant.ctor_def_id),
                        type_span,
                    )
                } else {
                    let node = hir::Type {
                        id: expression.id,
                        kind: hir::TypeKind::Nominal(path.clone()),
                        span: type_span,
                    };
                    let ty = self.lower_type(&node);
                    self.add_type_constraints(ty, type_span, cs);
                    (ty, LiteralConstructor::Struct, type_span)
                }
            }
            hir::ConstructorPath::Inferred {
                name,
                span: path_span,
            } => {
                let context = expectation
                    .map(|ty| cs.structurally_resolve(ty))
                    .unwrap_or_else(|| cs.infer_cx.next_ty_var(span));
                if context.is_infer() {
                    (
                        context,
                        LiteralConstructor::InferredVariant {
                            node_id: expression.id,
                            name: *name,
                        },
                        *path_span,
                    )
                } else {
                    let Some((variant, ty)) = self.resolve_inferred_enum_variant_pattern(
                        context,
                        expression.id,
                        name,
                        *path_span,
                        cs,
                    ) else {
                        return Ty::error(gcx);
                    };
                    if !self.require_struct_variant(variant, *path_span) {
                        return Ty::error(gcx);
                    }
                    (
                        ty,
                        LiteralConstructor::Variant(variant.ctor_def_id),
                        *path_span,
                    )
                }
            }
        };
        if lit.base.is_some() && !matches!(constructor, LiteralConstructor::Struct) {
            gcx.dcx().emit_error(
                "struct updates require a struct type; enum variants cannot use `..base`".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }
        struct_ty = cs.structurally_resolve(struct_ty);
        if struct_ty.is_error() {
            return struct_ty;
        }
        if let Some(expected) = expectation {
            let expected = cs.infer_cx.resolve_vars_if_possible(expected);
            if let (TyKind::Adt(actual, _), TyKind::Adt(wanted, _)) =
                (struct_ty.kind(), expected.kind())
                && actual.id == wanted.id
            {
                cs.equal(struct_ty, expected, span);
            }
        }
        if matches!(constructor, LiteralConstructor::Struct) {
            let TyKind::Adt(def, _) = struct_ty.kind() else {
                gcx.dcx().emit_error(
                    format!("expected struct type, found {}", struct_ty.format(gcx)),
                    Some(type_span),
                );
                return Ty::error(gcx);
            };
            if def.kind != crate::sema::models::AdtKind::Struct {
                gcx.dcx().emit_error(
                    "braces require a struct type or a named enum variant".into(),
                    Some(type_span),
                );
                return Ty::error(gcx);
            }
            if gcx.get_struct_definition(def.id).has_initializer || gcx.is_class_type(struct_ty) {
                gcx.dcx().emit_error(
                    if gcx.is_class_type(struct_ty) {
                        "a class must be constructed by calling its initializer"
                    } else {
                        "a struct declaring init must be constructed by calling its initializer"
                    }
                    .into(),
                    Some(span),
                );
                return Ty::error(gcx);
            }
        }
        let declared = match constructor {
            LiteralConstructor::Struct => {
                crate::sema::tycheck::utils::named_fields::named_fields(gcx, struct_ty, None)
            }
            LiteralConstructor::Variant(id) => {
                crate::sema::tycheck::utils::named_fields::named_fields(gcx, struct_ty, Some(id))
            }
            LiteralConstructor::InferredVariant { .. } => None,
        };
        let mut fields = Vec::with_capacity(lit.fields.len());
        let mut had_error = false;
        for field in &lit.fields {
            let (name, label_span) = if let Some(label) = &field.label {
                (label.identifier.symbol, label.span)
            } else {
                let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) =
                    &field.expression.kind
                else {
                    unreachable!("validated field shorthand")
                };
                let segment = path.segments.last().expect("shorthand identifier");
                (segment.identifier.symbol, segment.identifier.span)
            };
            // Context reaches inferred members before their constructor goals
            // are built, including fields whose generic arguments are pending.
            let deferred = matches!(constructor, LiteralConstructor::InferredVariant { .. });
            let field_expectation = if deferred {
                Some(cs.infer_cx.next_ty_var(field.expression.span))
            } else {
                declared.as_ref().and_then(|declared| {
                    declared
                        .fields
                        .iter()
                        .find(|field| field.name == name)
                        .map(|field| field.ty)
                })
            };
            let ty = self.synth_with_expectation(&field.expression, field_expectation, cs);
            had_error |= ty.is_error();
            fields.push(StructLiteralField {
                expectation: if deferred { field_expectation } else { None },
                name,
                node_id: field.expression.id,
                ty,
                value_span: field.expression.span,
                label_span,
            });
        }
        if let Some(base) = &lit.base {
            let base_ty = self.synth_with_expectation(base, Some(struct_ty), cs);
            had_error |= base_ty.is_error();
            // Updates require this exact value type, with no implicit reference
            // reads, Deref calls, interface erasure or other coercion.
            cs.equal(struct_ty, base_ty, base.span);
        }
        if had_error {
            return Ty::error(gcx);
        }
        cs.add_goal(
            Goal::StructLiteral(StructLiteralGoalData {
                ty_span: type_span,
                span,
                struct_ty,
                constructor,
                fields,
                base_span: lit.base.as_ref().map(|base| base.span),
            }),
            span,
        );
        struct_ty
    }
    pub(super) fn synth_tuple_expression(
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
            // A contextual tuple element is a value initialization site, just
            // like a local binding. Preserve its coercion (boxing, reborrowing,
            // function-pointer conversion) on the element's own expression.
            if let Some(expected) = elem_expectation {
                cs.add_goal(
                    Goal::Coerce {
                        node_id: element.id,
                        from: ty,
                        to: expected,
                    },
                    element.span,
                );
                element_types.push(expected);
            } else {
                element_types.push(ty);
            }
        }

        if had_error {
            return Ty::error(self.gcx());
        }

        Ty::new(
            TyKind::Tuple(self.gcx().store.interners.intern_ty_list(element_types)),
            self.gcx(),
        )
    }

    pub(super) fn synth_array_expression(
        &self,
        expression: &hir::Expression,
        elements: &[Box<hir::Expression>],
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let list_def_id = gcx.std_item_def(hir::StdItem::List);
        let expectation = expectation.map(|ty| cs.structurally_resolve(ty));
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
            if expected_elem.is_some() {
                // The annotation fixes the element representation, so each
                // initializer gets ordinary value coercions before storage.
                cs.add_goal(
                    Goal::Coerce {
                        node_id: elem.id,
                        from: ty,
                        to: element_ty,
                    },
                    elem.span,
                );
            } else {
                // Uncontextual literals infer one exact element type; do not
                // invent a common erased interface for heterogeneous values.
                cs.equal(element_ty, ty, elem.span);
            }
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

        // A generic parameter may become a List or an array only after the
        // other call arguments/result have been constrained. Keep its literal
        // representation open until then, including nested element literals.
        if let Some(ty) = expectation.filter(|ty| {
            ty.is_infer()
                || matches!(
                    ty.kind(),
                    TyKind::Alias {
                        kind: AliasKind::Projection,
                        ..
                    }
                )
        }) {
            cs.add_goal(
                Goal::CollectionLiteral {
                    ty,
                    element: element_ty,
                    len: len_const,
                },
                expression.span,
            );
            return ty;
        }

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

    pub(super) fn synth_repeat_expression(
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
        if matches!(len_const.kind, ConstKind::Param(_)) {
            // THIR/MIR repetition currently stores a concrete count. Do not
            // let a symbolic parameter reach its former debug assertion /
            // optimized-build zero fallback. Const-generic array types and
            // named concrete constants remain valid.
            gcx.dcx().emit_error(
                "array repetition requires a concrete count; const-generic repeat counts are not supported yet".into(),
                Some(count.value.span),
            );
            return Ty::error(gcx);
        }
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

    pub(super) fn synth_tuple_access_expression(
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
                receiver_addressable: self.receiver_is_addressable(receiver, cs),
                node_id: expression.id,
                receiver_node_id: receiver.id,
                receiver: receiver_ty,
                index: idx_val,
                result: result_ty,
                span: expression.span,
            }),
            expression.span,
        );

        // See `synth_member_expression`: the expectation is a hint, and
        // equating it here would defeat coercions at the use site.
        let _ = expectation;

        result_ty
    }
}

fn type_mentions_generic_parameter<'ctx>(ty: Ty<'ctx>, index: usize) -> bool {
    fn const_mentions_generic_parameter<'ctx>(value: Const<'ctx>, index: usize) -> bool {
        matches!(value.kind, ConstKind::Param(parameter) if parameter.index == index)
            || type_mentions_generic_parameter(value.ty, index)
    }

    fn argument_mentions_generic_parameter<'ctx>(
        argument: GenericArgument<'ctx>,
        index: usize,
    ) -> bool {
        match argument {
            GenericArgument::Type(ty) => type_mentions_generic_parameter(ty, index),
            GenericArgument::Const(value) => const_mentions_generic_parameter(value, index),
        }
    }

    match ty.kind() {
        TyKind::Parameter(parameter) => parameter.index == index,
        TyKind::Array { element, len } => {
            type_mentions_generic_parameter(element, index)
                || const_mentions_generic_parameter(len, index)
        }
        TyKind::Pointer(inner, _) | TyKind::Reference(inner) => {
            type_mentions_generic_parameter(inner, index)
        }
        TyKind::Tuple(items) => items
            .iter()
            .any(|item| type_mentions_generic_parameter(*item, index)),
        TyKind::FnPointer { inputs, output, .. } => {
            inputs
                .iter()
                .any(|input| type_mentions_generic_parameter(*input, index))
                || type_mentions_generic_parameter(output, index)
        }
        TyKind::Closure {
            captured_generics,
            inputs,
            output,
            ..
        } => {
            captured_generics
                .iter()
                .any(|argument| argument_mentions_generic_parameter(*argument, index))
                || inputs
                    .iter()
                    .any(|input| type_mentions_generic_parameter(*input, index))
                || type_mentions_generic_parameter(output, index)
        }
        TyKind::Adt(_, arguments)
        | TyKind::Alias {
            args: arguments, ..
        } => arguments
            .iter()
            .any(|argument| argument_mentions_generic_parameter(*argument, index)),
        TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|interface| {
            interface
                .arguments
                .iter()
                .any(|argument| argument_mentions_generic_parameter(*argument, index))
                || interface
                    .bindings
                    .iter()
                    .any(|binding| type_mentions_generic_parameter(binding.ty, index))
        }),
        _ => false,
    }
}
