use super::*;

impl<'ctx> Checker<'ctx> {
    /// Structural match patterns read through references; bindings always copy values.
    pub(super) fn check_pattern(
        &self,
        pattern: &hir::Pattern,
        scrutinee: Ty<'ctx>,
        scrutinee_node_id: NodeID,
        cs: &mut Cs<'ctx>,
    ) {
        let mut ctx = scrutinee;
        self.check_pattern_with_context(pattern, &mut ctx, scrutinee_node_id, true, cs);
    }

    /// Local destructuring retains explicit value reads. Match/if-case targets
    /// have structural autodereferencing; ordinary local declarations do not.
    pub(super) fn check_local_pattern(
        &self,
        pattern: &hir::Pattern,
        scrutinee: Ty<'ctx>,
        scrutinee_node_id: NodeID,
        cs: &mut Cs<'ctx>,
    ) {
        let mut ty = scrutinee;
        self.check_pattern_with_context(pattern, &mut ty, scrutinee_node_id, false, cs);
    }

    fn check_pattern_with_context(
        &self,
        pattern: &hir::Pattern,
        ctx: &mut Ty<'ctx>,
        scrutinee_node_id: NodeID,
        autoderef: bool,
        cs: &mut Cs<'ctx>,
    ) {
        // Destructuring needs the initializer's structure before pending
        // coercions are solved. Do not force unrelated overloads to resolve.
        if !matches!(
            pattern.kind,
            hir::PatternKind::Binding { .. } | hir::PatternKind::Wildcard
        ) && cs.infer_cx.resolve_vars_if_possible(*ctx).is_infer()
        {
            if let Some(scrutinee_ty) = cs.expr_ty(scrutinee_node_id) {
                let resolved = cs.infer_cx.resolve_vars_if_possible(scrutinee_ty);
                if !resolved.is_infer() {
                    *ctx = resolved;
                }
            }
        }

        // A structural pattern reads the referent. A plain identifier copies
        // the reference itself; reference-typed payload bindings remain &T.
        if !matches!(
            pattern.kind,
            hir::PatternKind::Binding { .. }
                | hir::PatternKind::Wildcard
                | hir::PatternKind::Rest
                | hir::PatternKind::Or(..)
        ) {
            while let TyKind::Reference(inner) = cs.infer_cx.resolve_vars_if_possible(*ctx).kind() {
                if !autoderef {
                    self.gcx().dcx().emit_error(
                        "local destructuring requires an explicit dereference".into(),
                        Some(pattern.span),
                    );
                    self.mark_pattern_bindings_error(pattern);
                    return;
                }
                *ctx = inner;
            }
        }

        // Now check the pattern against the adjusted type
        self.check_pattern_inner(pattern, ctx, autoderef, cs);
    }

    /// Check the pattern against its value type.
    fn check_pattern_inner(
        &self,
        pattern: &hir::Pattern,
        ctx: &mut Ty<'ctx>,
        autoderef: bool,
        cs: &mut Cs<'ctx>,
    ) {
        cs.record_expr_ty(pattern.id, *ctx);
        match &pattern.kind {
            hir::PatternKind::Wildcard => {}
            hir::PatternKind::Rest => {}
            hir::PatternKind::Binding { .. } => {
                let binding = self.get_local(pattern.id);
                cs.equal(*ctx, binding.ty, pattern.span);
            }
            hir::PatternKind::Tuple(pats, _) => {
                let has_rest = pats
                    .iter()
                    .any(|pat| matches!(pat.kind, hir::PatternKind::Rest));
                if has_rest {
                    let resolved_scrutinee = cs.infer_cx.resolve_vars_if_possible(*ctx);
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
                    cs.equal(*ctx, tuple_ty, pattern.span);

                    for (pat_index, field_index) in field_mapping {
                        let mut sub_ctx = elem_tys[field_index];

                        self.check_pattern_with_context(
                            &pats[pat_index],
                            &mut sub_ctx,
                            pats[pat_index].id,
                            autoderef,
                            cs,
                        );
                    }
                    return;
                }

                let elem_tys = match cs.infer_cx.resolve_vars_if_possible(*ctx).kind() {
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
                cs.equal(*ctx, tuple_ty, pattern.span);

                for (i, pat) in pats.iter().enumerate() {
                    let mut sub_ctx = elem_tys[i];

                    self.check_pattern_with_context(pat, &mut sub_ctx, pat.id, autoderef, cs);
                }
            }
            hir::PatternKind::Member(path) => {
                let Some((variant, enum_ty)) =
                    self.resolve_enum_variant_pattern(*ctx, pattern.id, path, pattern.span, cs)
                else {
                    return;
                };

                if !matches!(variant.kind, crate::sema::models::EnumVariantKind::Unit) {
                    self.gcx().dcx().emit_error(
                        format!(
                            "enum variant '{}' requires {} fields",
                            self.gcx().symbol_text(variant.name),
                            if matches!(
                                variant.kind,
                                crate::sema::models::EnumVariantKind::Struct(..)
                            ) {
                                "named"
                            } else {
                                "tuple"
                            }
                        )
                        .into(),
                        Some(pattern.span),
                    );
                    return;
                }

                cs.equal(*ctx, enum_ty, pattern.span);
            }
            hir::PatternKind::PathTuple { path, fields, .. } => {
                let Some((variant, enum_ty, variant_fields)) = self
                    .resolve_enum_tuple_variant_pattern(*ctx, pattern.id, path, pattern.span, cs)
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

                cs.equal(*ctx, enum_ty, pattern.span);

                for (pat_index, field_index) in field_mapping {
                    let field = variant_fields[field_index];
                    let mut sub_ctx = field.ty;

                    self.check_pattern_with_context(
                        &fields[pat_index],
                        &mut sub_ctx,
                        fields[pat_index].id,
                        autoderef,
                        cs,
                    );
                }
            }
            hir::PatternKind::PathNamed {
                path, fields, rest, ..
            } => {
                let (ty, constructor) = match path {
                    hir::ConstructorPath::Qualified { path } => {
                        let (resolution, args, _) = self.resolve_value_path_resolution_with_args(
                            path,
                            pattern.span,
                            false,
                            cs,
                        );
                        if matches!(
                            resolution,
                            hir::Resolution::Definition(_, DefinitionKind::VariantConstructor(..))
                        ) {
                            self.record_value_path_resolution(pattern.id, &resolution);
                            let Some((variant, ty)) = self.resolve_enum_variant_from_resolution(
                                *ctx,
                                resolution,
                                pattern.span,
                                cs,
                                args,
                            ) else {
                                self.mark_pattern_bindings_error(pattern);
                                return;
                            };
                            if !self.require_struct_variant(variant, pattern.span) {
                                self.mark_pattern_bindings_error(pattern);
                                return;
                            }
                            (ty, Some(variant.ctor_def_id))
                        } else {
                            let node = hir::Type {
                                id: pattern.id,
                                kind: hir::TypeKind::Nominal(path.clone()),
                                span: pattern.span,
                            };
                            let ty = cs.structurally_resolve(self.lower_type(&node));
                            self.add_type_constraints(ty, pattern.span, cs);
                            cs.equal(*ctx, ty, pattern.span);
                            (ty, None)
                        }
                    }
                    hir::ConstructorPath::Inferred { name, span } => {
                        let Some((variant, ty)) = self.resolve_inferred_enum_variant_pattern(
                            *ctx, pattern.id, name, *span, cs,
                        ) else {
                            self.mark_pattern_bindings_error(pattern);
                            return;
                        };
                        if !self.require_struct_variant(variant, pattern.span) {
                            self.mark_pattern_bindings_error(pattern);
                            return;
                        }
                        (ty, Some(variant.ctor_def_id))
                    }
                };
                let gcx = self.gcx();
                let Some(declared) =
                    crate::sema::tycheck::utils::named_fields::named_fields(gcx, ty, constructor)
                else {
                    if !ty.is_error() {
                        gcx.dcx().emit_error(
                            "named patterns require a struct or named enum variant".into(),
                            Some(pattern.span),
                        );
                    }
                    self.mark_pattern_bindings_error(pattern);
                    return;
                };
                cs.record_expr_ty(pattern.id, ty);
                let mut used = vec![false; declared.fields.len()];
                for field in fields {
                    let Some((index, definition)) = declared
                        .fields
                        .iter()
                        .enumerate()
                        .find(|(_, candidate)| candidate.name == field.name.symbol)
                    else {
                        gcx.dcx().emit_error(
                            format!(
                                "no field '{}' on type {}",
                                gcx.symbol_text(field.name.symbol),
                                ty.format(gcx)
                            ),
                            Some(field.name.span),
                        );
                        self.mark_pattern_bindings_error(pattern);
                        return;
                    };
                    if definition.visibility.is_some_and(|visibility| {
                        !gcx.is_visibility_allowed(visibility, self.current_def)
                    }) {
                        gcx.dcx().emit_error(
                            format!(
                                "field '{}' of {} is not visible here",
                                gcx.symbol_text(field.name.symbol),
                                ty.format(gcx)
                            ),
                            Some(field.name.span),
                        );
                        self.mark_pattern_bindings_error(pattern);
                        return;
                    }
                    used[index] = true;
                    let mut field_ty = definition.ty;
                    self.check_pattern_with_context(
                        &field.pattern,
                        &mut field_ty,
                        field.pattern.id,
                        autoderef,
                        cs,
                    );
                }
                if !rest && let Some(index) = used.iter().position(|used| !used) {
                    gcx.dcx().emit_error(format!("named pattern is missing field '{}'; add `..` to ignore remaining fields", gcx.symbol_text(declared.fields[index].name)), Some(pattern.span));
                    self.mark_pattern_bindings_error(pattern);
                }
            }
            hir::PatternKind::Or(patterns, _) => {
                for pat in patterns {
                    let mut sub_ctx = *ctx;

                    self.check_pattern_with_context(pat, &mut sub_ctx, pat.id, autoderef, cs);
                }
            }
            hir::PatternKind::Literal { value } => {
                let expected = cs.infer_cx.resolve_vars_if_possible(*ctx);
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
                cs.equal(*ctx, lit_ty, pattern.span);
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
        path: &hir::ConstructorPath,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Option<(crate::sema::models::EnumVariant<'ctx>, Ty<'ctx>)> {
        match path {
            hir::ConstructorPath::Qualified { path } => {
                // Note: Similar to value paths, we don't need to add type constraints
                // for the base type in relative patterns like `Optional.none`.
                // The base type is only used for name resolution.
                let (resolution, base_args, _) =
                    self.resolve_value_path_resolution_with_args(path, span, true, cs);
                self.record_value_path_resolution(id, &resolution);
                self.resolve_enum_variant_from_resolution(
                    scrutinee, resolution, span, cs, base_args,
                )
            }
            hir::ConstructorPath::Inferred {
                name,
                span: inferred_span,
            } => {
                self.resolve_inferred_enum_variant_pattern(scrutinee, id, name, *inferred_span, cs)
            }
        }
    }

    pub(super) fn require_struct_variant(
        &self,
        variant: crate::sema::models::EnumVariant<'ctx>,
        span: Span,
    ) -> bool {
        if matches!(
            variant.kind,
            crate::sema::models::EnumVariantKind::Struct(..)
        ) {
            return true;
        }
        self.gcx().dcx().emit_error(
            format!(
                "enum variant '{}' does not have named fields",
                self.gcx().symbol_text(variant.name)
            ),
            Some(span),
        );
        false
    }

    pub(super) fn resolve_enum_tuple_variant_pattern(
        &self,
        scrutinee: Ty<'ctx>,
        id: NodeID,
        path: &hir::ConstructorPath,
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
        let scrutinee = cs.structurally_resolve(scrutinee);
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

            hir::PatternKind::Tuple(patterns, _)
            | hir::PatternKind::Or(patterns, _)
            | hir::PatternKind::PathTuple {
                fields: patterns, ..
            } => {
                for pat in patterns {
                    self.mark_pattern_bindings_error(pat);
                }
            }
            hir::PatternKind::PathNamed { fields, .. } => {
                for field in fields {
                    self.mark_pattern_bindings_error(&field.pattern);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod named_field_tests {
    use crate::test_support::{analyze_script_diagnostics, analyze_script_mir_diagnostics};

    #[test]
    fn named_construction_and_value_patterns_typecheck() {
        let diagnostics = analyze_script_mir_diagnostics(
            r#"
            struct Point[T] { x: T; y: T }
            enum Shape[T] { case rect { width: T; height: T }; case empty {}; case dot(T) }
            func make() -> Shape[int64] { .rect { height: 4, width: 3 } }
            func read(_ shape: &Shape[int64]) -> int64 {
                match shape {
                    case .rect { height, width: w } => w
                    case .empty {} => 0
                    case .dot(value) => value
                }
            }
            func point(_ value: Point[int64]) -> int64 {
                match value { case Point { y: other, .. } => other; }
            }
            enum Maybe { case yes(int64); case no }
            enum Container { case value { item: Maybe } }
            func identity[T](_ value: T) -> T { value }
            func change(_ shape: &Shape[int64]) { *shape = .empty {} }
            func main() {
                var shape: Shape[int64] = identity(.rect { width: 3, height: 4 })
                change(&shape)
                var container: Container = identity(.value { item: .yes(5) })
                var Point { x, .. } = Point { x: 1_i64, y: 2_i64 }
            }
        "#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn named_fields_reject_wrong_shapes_and_incomplete_patterns() {
        for (source, expected) in [
            (
                "enum E { case tuple(int32) }; func make() -> E { E::tuple { value: 1 } }; func main() {}",
                "does not have named fields",
            ),
            (
                "enum E { case item { x: int32; y: int32 } }; func make() -> E { E::item { x: 1 } }; func main() {}",
                "missing field 'y'",
            ),
            (
                "enum E { case item { x: int32 } }; func make() -> E { E::item { bad: 1 } }; func main() {}",
                "no field 'bad'",
            ),
            (
                "struct P { x: int32; y: int32 }; func read(_ p: P) { match p { case P { x } => {}; } }; func main() {}",
                "named pattern is missing field 'y'",
            ),
            (
                "enum E { case tuple(int32) }; func read(_ e: E) { match e { case .tuple { value } => {}; } }; func main() {}",
                "does not have named fields",
            ),
            (
                "struct P { x: int32 }; func read(_ p: P) { match p { case P { missing } => {}; } }; func main() {}",
                "no field 'missing'",
            ),
            (
                "enum E { case tuple(int32) }; func identity[T](_ value: T) -> T { value }; func main() { var value: E = identity(.tuple {}); }",
                "does not have named fields",
            ),
        ] {
            let diagnostics = analyze_script_diagnostics(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(expected)),
                "expected {expected:?}: {diagnostics:#?}"
            );
        }
    }
}
