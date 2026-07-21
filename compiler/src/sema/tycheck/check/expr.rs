use super::*;

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

    pub(super) fn synth_with_expectation(
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
    pub(super) fn synth_cast_expression(
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

    pub(super) fn synth_try_cast_expression(
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

    pub(super) fn synth_type_is_expression(
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

    pub(super) fn lookup_member_property_on_base_ty(
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

    pub(super) fn require_mut_place(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
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

                if let Some(property) = cs.resolved_property_reads().get(&expr.id).copied() {
                    if property.setter_id.is_none() {
                        self.gcx().dcx().emit_error(
                            "cannot assign to a read-only property".into(),
                            Some(expr.span),
                        );
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

    pub(super) fn can_mutably_borrow_receiver(
        &self,
        expr: &hir::Expression,
        cs: &Cs<'ctx>,
    ) -> bool {
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

    pub(super) fn require_mut_borrow(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
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
                // A direct `&mut pointer_slot` borrows the slot, not the
                // pointee. Pointer/reference mutability is therefore relevant
                // only in the Dereference branch below; the path itself obeys
                // its binding or static declaration's mutability.
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
                    if let Some(field) = struct_def
                        .fields
                        .iter()
                        .find(|field| field.name == name.symbol)
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

    fn require_mut_receiver_borrow(&self, expr: &hir::Expression, cs: &Cs<'ctx>) -> bool {
        if let Some(expr_ty) = cs.expr_ty(expr.id) {
            let expr_ty = cs.infer_cx.resolve_vars_if_possible(expr_ty);
            match expr_ty.kind() {
                TyKind::Error => return true,
                TyKind::Pointer(_, hir::Mutability::Mutable)
                | TyKind::Reference(_, hir::Mutability::Mutable) => return true,
                TyKind::Pointer(_, hir::Mutability::Immutable)
                | TyKind::Reference(_, hir::Mutability::Immutable) => {
                    self.gcx().dcx().emit_error(
                        "cannot borrow through an immutable pointer/reference".into(),
                        Some(expr.span),
                    );
                    return false;
                }
                _ => {}
            }
        }

        // A method/property receiver is implicitly dereferenced, so an immutable
        // binding that stores `&mut T` may still mutate `T`. Explicit `&mut slot`
        // uses `require_mut_borrow` directly because it borrows the storage slot.
        self.require_mut_borrow(expr, cs)
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
        if matches!(lhs.kind, hir::ExpressionKind::Member { .. }) {
            cs.solve_intermediate();
        }
        if !self.require_mut_place(lhs, cs) {
            return Ty::error(self.gcx());
        }

        // Type-check the RHS against the LHS type.
        let rhs_ty = self.synth_with_expectation(rhs, Some(lhs_ty), cs);
        if lhs_ty.is_error() || rhs_ty.is_error() {
            return Ty::error(self.gcx());
        }

        if let Some(property) = cs.resolved_property_reads().get(&lhs.id).copied()
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

    /// `await expr` — verify expr is a direct async call, then return its ready type.
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

    pub(super) fn synth_identifier_expression(
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
                    DefinitionKind::TypeAlias => {
                        let Some((nominal, constructor_args)) =
                            self.type_alias_constructor_target(*id, instantiation_args)
                        else {
                            let name = self.gcx().definition_ident(*id).symbol;
                            self.gcx().dcx().emit_error(
                                format!(
                                    "type alias '{}' does not name a constructible struct",
                                    self.gcx().symbol_text(name)
                                )
                                .into(),
                                Some(span),
                            );
                            return Ty::error(self.gcx());
                        };
                        self.synth_constructor_value_expression(
                            node_id,
                            nominal,
                            span,
                            expectation,
                            constructor_args,
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

    pub(super) fn synth_constructor_value_expression(
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

    pub(super) fn synth_call_expression(
        &self,
        expression: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        expect_ty: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let prefer_async_call = self.direct_await_operand.get() == Some(expression.id);

        // Register targeted Sendable diagnostics before resolving the callee:
        // path and closure inference can both run intermediate solver passes.
        if let Some(context) = self.compiler_call_context(expression, callee, arguments) {
            cs.record_compiler_call_context(callee.id, context);
        }

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

    fn compiler_call_context(
        &self,
        expression: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
    ) -> Option<CompilerCallContext> {
        let hir::ExpressionKind::Path(path) = &callee.kind else {
            return None;
        };
        let resolution = match path {
            hir::ResolvedPath::Resolved(path) => &path.resolution,
            hir::ResolvedPath::Relative(_, segment) => &segment.resolution,
        };
        let candidates: &[DefinitionID] = match resolution {
            hir::Resolution::FunctionSet(candidates) => candidates,
            hir::Resolution::Definition(id, DefinitionKind::Function) => std::slice::from_ref(id),
            _ => return None,
        };
        for &candidate in candidates {
            let name = self.gcx().definition_symbol_or_fallback(candidate);
            if self.gcx().symbol_eq(name, "blocking")
                && self.definition_is_in_std_module(candidate, "task")
                && let Some(closure) = arguments.first()
            {
                return Some(CompilerCallContext::Blocking {
                    callee: candidate,
                    closure_span: closure.expression.span,
                    call_span: expression.span,
                });
            }
            if self.gcx().symbol_eq(name, "addCleanup")
                && self.definition_is_in_std_module(candidate, "runtime")
                && let (Some(state), Some(callback)) = (arguments.get(1), arguments.get(2))
            {
                return Some(CompilerCallContext::AddCleanup {
                    callee: candidate,
                    state_span: state.expression.span,
                    callback_span: callback.expression.span,
                });
            }
        }
        None
    }

    fn definition_is_in_std_module(&self, id: DefinitionID, module: &str) -> bool {
        let Some(std_package) = self.gcx().std_package_index() else {
            return false;
        };
        if id.package() != std_package {
            return false;
        }

        let output = self.gcx().resolution_output(std_package);
        let mut current = id;
        while let Some(parent) = output.definition_to_parent.get(&current).copied() {
            if parent == current {
                break;
            }
            current = parent;
            if matches!(
                output.definition_to_kind.get(&current),
                Some(DefinitionKind::Module)
            ) && output
                .definition_to_ident
                .get(&current)
                .is_some_and(|ident| self.gcx().symbol_eq(ident.symbol, module))
            {
                return true;
            }
        }
        false
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

    pub(super) fn synth_method_call_expression(
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
    pub(super) fn method_argument_expectations(
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
                    let expectation_ty = self.freshen_method_expectation_ty(
                        def_id,
                        bound.fn_signature_ty,
                        name.span,
                        cs,
                    );
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

    pub(super) fn method_call_can_yield_mutable_reference(
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

    pub(super) fn constructor_nominal_from_resolution(
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

    fn type_alias_constructor_target(
        &self,
        alias_id: DefinitionID,
        alias_args: Option<GenericArguments<'ctx>>,
    ) -> Option<(DefinitionID, Option<GenericArguments<'ctx>>)> {
        let gcx = self.gcx();
        let mut target = gcx.try_get_alias_type(alias_id)?;
        if let Some(args) = alias_args {
            target = instantiate_ty_with_args(gcx, target, args);
        }
        target = crate::sema::tycheck::utils::normalize_aliases(gcx, target);

        let TyKind::Adt(def, target_args) = target.kind() else {
            return None;
        };
        if def.kind != crate::sema::models::AdtKind::Struct {
            return None;
        }

        // Constructor methods inherit the target struct's generic parameters, not
        // the alias's. Forward the normalized target arguments so aliases that
        // reorder or fix parameters bind the same constructor as the named struct.
        let target_args = if target_args.is_empty() {
            None
        } else {
            Some(target_args)
        };
        Some((def.id, target_args))
    }

    pub(super) fn bind_constructor_overload_set(
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
            GatherLocalsVisitor::from_match_arm(cs, self, &condition.pattern);
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
        GatherLocalsVisitor::from_match_arm(cs, self, &condition.pattern);

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

    pub(super) fn synth_unary_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::UnaryOperator,
        operand: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // For negate/bitwise-not the result type equals the operand type, so
        // forward the expectation to help infer literal types
        // (e.g. `let x: int8 = -56`), mirroring synth_binary_expression.
        let operand_expectation = match operator {
            hir::UnaryOperator::Negate | hir::UnaryOperator::BitwiseNot => expectation,
            _ => None,
        };
        let operand_ty = self.synth_with_expectation(operand, operand_expectation, cs);
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

    pub(super) fn synth_binary_expression(
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

    pub(super) fn synth_assign_op_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::BinaryOperator,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Resolve the member before asking whether the LHS is a mutable place. A
        // computed property is a value, not a place, but compound assignment can
        // still update it by reading into a temporary and writing through its setter.
        let lhs_ty = self.synth(lhs, cs);
        if lhs_ty.is_error() {
            return Ty::error(self.gcx());
        }
        cs.solve_intermediate();

        let property_read = cs.resolved_property_reads().get(&lhs.id).copied();
        if let Some(property) = property_read {
            let hir::ExpressionKind::Member { target, name } = &lhs.kind else {
                unreachable!("resolved property read must originate from a member expression");
            };

            let Some(setter_id) = property.setter_id else {
                self.gcx().dcx().emit_error(
                    format!(
                        "cannot apply compound assignment to read-only property '{}'; property has no setter",
                        self.gcx().symbol_text(name.symbol)
                    ),
                    Some(lhs.span),
                );
                return Ty::error(self.gcx());
            };

            if property.getter_is_async {
                self.cancel_async_property_surface_check(lhs.id);
                self.gcx().dcx().emit_error(
                    format!(
                        "async getter for property '{}' cannot be used in compound assignment",
                        self.gcx().symbol_text(name.symbol)
                    ),
                    Some(lhs.span),
                );
                return Ty::error(self.gcx());
            }

            if !self.require_mut_receiver_borrow(target, cs) {
                return Ty::error(self.gcx());
            }

            let getter_sig = self.gcx().get_signature(property.getter_id);
            let getter_consumes_receiver = getter_sig
                .inputs
                .first()
                .is_some_and(|input| !matches!(input.ty.kind(), TyKind::Reference(_, _)));
            if getter_consumes_receiver && !self.gcx().is_type_copyable(property.receiver_ty) {
                self.gcx().dcx().emit_error(
                    format!(
                        "compound assignment to property '{}' cannot use a consuming getter on non-Copy receiver type '{}'",
                        self.gcx().symbol_text(name.symbol),
                        property.receiver_ty.format(self.gcx())
                    ),
                    Some(lhs.span),
                );
                return Ty::error(self.gcx());
            }

            cs.record_property_write(
                expression.id,
                crate::sema::tycheck::solve::ResolvedPropertyWrite {
                    property_id: property.property_id,
                    setter_id,
                    ty: property.ty,
                },
            );
        } else if !self.require_mut_place(lhs, cs) {
            return Ty::error(self.gcx());
        }

        let rhs_ty = self.synth(rhs, cs);
        if rhs_ty.is_error() {
            return Ty::error(self.gcx());
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

    pub(super) fn synth_path_expression_with_policy(
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

    pub(super) fn synth_path_expression(
        &self,
        expression: &hir::Expression,
        path: &hir::ResolvedPath,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
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

    pub(super) fn synth_struct_literal(
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

    pub(super) fn synth_array_expression(
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
                node_id: expression.id,
                receiver_node_id: receiver.id,
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
