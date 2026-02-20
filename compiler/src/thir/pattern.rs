use crate::{
    compile::context::GlobalContext,
    hir::{self, NodeID, PatternPath, Resolution},
    sema::models::TyKind,
    sema::tycheck::results::TypeCheckResults,
    thir::{Constant, ConstantKind, FieldIndex, FieldPattern, Pattern, PatternKind},
};

pub fn pattern_from_hir<'ctx>(
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
    pattern: &hir::Pattern,
) -> Pattern<'ctx> {
    let mut ctx = PatternLoweringContext { gcx, results };
    ctx.lower_pattern(pattern)
}

struct PatternLoweringContext<'ctx, 'r> {
    gcx: GlobalContext<'ctx>,
    results: &'r TypeCheckResults<'ctx>,
}

impl<'ctx, 'r> PatternLoweringContext<'ctx, 'r> {
    fn lower_pattern(&mut self, pattern: &hir::Pattern) -> Pattern<'ctx> {
        self.lower_pattern_unadjusted(pattern)
    }

    fn lower_pattern_unadjusted(&mut self, pattern: &hir::Pattern) -> Pattern<'ctx> {
        let ty = self.results.node_type(pattern.id);
        let span = pattern.span;

        let kind = match &pattern.kind {
            hir::PatternKind::Wildcard => PatternKind::Wild,
            hir::PatternKind::Binding { name, mode } => {
                // Get the inferred binding mode from typechecking
                // Fall back to the HIR mode if not recorded (shouldn't happen in practice)
                let actual_mode = self.results.binding_mode(pattern.id).unwrap_or(*mode);

                PatternKind::Binding {
                    name: name.symbol.clone(),
                    local: pattern.id,
                    ty,
                    mode: actual_mode,
                }
            }

            hir::PatternKind::Reference { pattern: inner, .. } => {
                let inner = self.lower_pattern(inner);
                PatternKind::Deref {
                    pattern: Box::new(inner),
                }
            }

            hir::PatternKind::Tuple(pats, _) => {
                let field_count = match ty.kind() {
                    TyKind::Tuple(items) => items.len(),
                    _ => pats
                        .iter()
                        .filter(|pattern| !matches!(pattern.kind, hir::PatternKind::Rest))
                        .count(),
                };
                let subpatterns = self
                    .pattern_field_mapping_with_rest(pats, field_count)
                    .into_iter()
                    .map(|(pattern_index, field_index)| FieldPattern {
                        index: FieldIndex::from_usize(field_index),
                        pattern: self.lower_pattern(&pats[pattern_index]),
                    })
                    .collect();
                PatternKind::Leaf { subpatterns }
            }
            hir::PatternKind::Member(path) => {
                let resolution = self.path_resolution(path, pattern.id);
                let data = self.variant_of_resolution(resolution);
                PatternKind::Variant {
                    definition: data.0,
                    variant: data.1,
                    subpatterns: vec![],
                }
            }
            hir::PatternKind::PathTuple { path, fields, .. } => {
                let resolution = self.path_resolution(path, pattern.id);
                let data = self.variant_of_resolution(resolution);
                let field_count = match data.1.kind {
                    crate::sema::models::EnumVariantKind::Tuple(variant_fields) => {
                        variant_fields.len()
                    }
                    crate::sema::models::EnumVariantKind::Unit => 0,
                };
                let subpatterns: Vec<_> = self
                    .pattern_field_mapping_with_rest(fields, field_count)
                    .into_iter()
                    .map(|(pattern_index, field_index)| FieldPattern {
                        index: FieldIndex::from_usize(field_index),
                        pattern: self.lower_pattern(&fields[pattern_index]),
                    })
                    .collect();
                PatternKind::Variant {
                    definition: data.0,
                    variant: data.1,
                    subpatterns,
                }
            }
            hir::PatternKind::Rest => PatternKind::Wild,
            hir::PatternKind::Or(pats, _) => {
                let patterns = pats.iter().map(|p| self.lower_pattern(p)).collect();
                PatternKind::Or(patterns)
            }
            hir::PatternKind::Literal(lit) => {
                let ty = self.results.node_type(pattern.id);
                PatternKind::Constant {
                    value: Constant {
                        ty,
                        value: self.lower_literal(lit),
                    },
                }
            }
        };

        Pattern { ty, span, kind }
    }

    fn pattern_field_mapping_with_rest(
        &self,
        patterns: &[hir::Pattern],
        field_count: usize,
    ) -> Vec<(usize, usize)> {
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
            return Vec::new();
        }

        let Some(rest_index) = rest_positions.first().copied() else {
            let count = patterns.len().min(field_count);
            return (0..count).map(|index| (index, index)).collect();
        };

        let explicit_field_count = patterns.len().saturating_sub(1);
        if explicit_field_count > field_count {
            return Vec::new();
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

        mapping
    }

    fn path_resolution(&self, path: &PatternPath, id: NodeID) -> hir::Resolution {
        match path {
            PatternPath::Qualified { path } => match path {
                hir::ResolvedPath::Resolved(path) => path.resolution.clone(),
                hir::ResolvedPath::Relative(..) => {
                    let resolution = self.results.value_resolution(id);
                    resolution.expect("expected path resolution")
                }
            },
            PatternPath::Inferred { .. } => {
                // Inferred patterns are resolved by the typechecker and the resolution is recorded
                let resolution = self.results.value_resolution(id);
                resolution.expect("expected resolution for inferred pattern")
            }
        }
    }

    fn variant_of_resolution(
        &self,
        resolution: Resolution,
    ) -> (
        crate::sema::models::AdtDef,
        crate::sema::models::EnumVariant<'ctx>,
    ) {
        let hir::Resolution::Definition(ctor_id, hir::DefinitionKind::VariantConstructor(..)) =
            resolution
        else {
            unreachable!()
        };

        let Some(parent_id) = self.gcx.definition_parent(ctor_id) else {
            unreachable!()
        };

        let enum_id = match self.gcx.definition_kind(parent_id) {
            hir::DefinitionKind::Enum => parent_id,
            hir::DefinitionKind::Variant => match self.gcx.definition_parent(parent_id) {
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
        let Some(variant) = def.variants.iter().find(|v| v.ctor_def_id == ctor_id) else {
            unreachable!()
        };

        (def.adt_def.clone(), variant.clone())
    }

    fn lower_literal(&self, lit: &hir::Literal) -> ConstantKind {
        match lit {
            hir::Literal::Bool(b) => ConstantKind::Bool(*b),
            hir::Literal::Rune(r) => ConstantKind::Rune(*r),
            hir::Literal::String(s) => ConstantKind::String(s.clone()),
            hir::Literal::Integer(i) => ConstantKind::Integer(*i),
            hir::Literal::Float(f) => ConstantKind::Float(*f),
            hir::Literal::Nil => ConstantKind::Unit,
        }
    }
}
