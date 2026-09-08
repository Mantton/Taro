use super::*;

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
    pub(super) fn check_pattern(
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

        // Destructuring needs the initializer's structure before pending
        // coercions are solved. Do not force unrelated overloads to resolve.
        if !matches!(
            pattern.kind,
            hir::PatternKind::Binding { .. } | hir::PatternKind::Wildcard
        ) && cs
            .infer_cx
            .resolve_vars_if_possible(ctx.adjusted_ty)
            .is_infer()
        {
            if let Some(scrutinee_ty) = cs.expr_ty(scrutinee_node_id) {
                let resolved = cs.infer_cx.resolve_vars_if_possible(scrutinee_ty);
                if !resolved.is_infer() {
                    ctx.adjusted_ty = resolved;
                }
            }
        }

        if matches!(pattern.kind, hir::PatternKind::Reference { .. })
            && cs
                .infer_cx
                .resolve_vars_if_possible(ctx.adjusted_ty)
                .is_infer()
        {
            cs.solve_intermediate();
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

                let elem_tys = match cs.infer_cx.resolve_vars_if_possible(ctx.adjusted_ty).kind() {
                    TyKind::Tuple(items) if items.len() == pats.len() => items.to_vec(),
                    _ => pats
                        .iter()
                        .map(|_| cs.infer_cx.next_ty_var(pattern.span))
                        .collect(),
                };

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
            hir::PatternKind::Literal { value } => {
                let expected = cs.infer_cx.resolve_vars_if_possible(ctx.adjusted_ty);
                if let hir::Literal::Integer { value, .. } = value
                    && *value < 0
                    && matches!(expected.kind(), TyKind::UInt(_))
                {
                    self.gcx().dcx().emit_error(
                        format!(
                            "integer literal '{}' is out of range for type '{}'",
                            value,
                            expected.format(self.gcx())
                        ),
                        Some(pattern.span),
                    );
                }
                let lit_ty = self.synth_expression_literal(value, pattern.span, Some(expected), cs);
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

    pub(super) fn compute_pattern_field_mapping(
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

    pub(super) fn resolve_enum_variant_pattern(
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

    pub(super) fn resolve_enum_tuple_variant_pattern(
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

    pub(super) fn resolve_enum_variant_from_resolution(
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
    pub(super) fn resolve_inferred_enum_variant_pattern(
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

    pub(super) fn mark_pattern_bindings_error(&self, pattern: &hir::Pattern) {
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
