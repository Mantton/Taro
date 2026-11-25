use crate::{
    compile::context::GlobalContext,
    hir::{self, ConstructorPath, NodeID, Resolution},
    sema::models::TyKind,
    sema::tycheck::results::TypeCheckResults,
    thir::{Constant, ConstantKind, FieldIndex, FieldPattern, Pattern, PatternKind},
};

pub fn pattern_from_hir<'ctx>(
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
    pattern: &hir::Pattern,
) -> Pattern<'ctx> {
    // Resolution binds the arm body to the first occurrence of each name.
    // The decision tree may visit variants in declaration order instead.
    let mut first = rustc_hash::FxHashMap::default();
    let mut locals = rustc_hash::FxHashMap::default();
    if pattern.has_alternatives() {
        pattern.for_each_binding(&mut |id, name| {
            let canonical = *first.entry(name.symbol).or_insert(id);
            if id != canonical {
                locals.insert(id, canonical);
            }
        });
    }
    pattern_from_hir_with_locals(gcx, results, pattern, &locals)
}

pub(super) fn pattern_from_hir_with_locals<'ctx>(
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
    pattern: &hir::Pattern,
    locals: &rustc_hash::FxHashMap<NodeID, NodeID>,
) -> Pattern<'ctx> {
    let mut ctx = PatternLoweringContext { gcx, results, locals };
    ctx.lower_pattern(pattern)
}

struct PatternLoweringContext<'ctx, 'r> {
    gcx: GlobalContext<'ctx>,
    results: &'r TypeCheckResults<'ctx>,
    locals: &'r rustc_hash::FxHashMap<NodeID, NodeID>,
}

impl<'ctx, 'r> PatternLoweringContext<'ctx, 'r> {
    fn lower_pattern(&mut self, pattern: &hir::Pattern) -> Pattern<'ctx> {
        let ty = self.results.node_type(pattern.id);
        let span = pattern.span;

        let kind = match &pattern.kind {
            hir::PatternKind::Wildcard => PatternKind::Wild,
            hir::PatternKind::Binding { name } => PatternKind::Binding {
                name: name.symbol,
                local: self.locals.get(&pattern.id).copied().unwrap_or(pattern.id),
                ty,
            },

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
                let (variant, field_count) = match ty.kind() {
                    TyKind::Adt(def, _) if def.kind == crate::sema::models::AdtKind::Struct =>
                        (None, self.gcx.get_struct_definition(def.id).fields.len()),
                    _ => {
                        let data = self.variant_of_resolution(self.path_resolution(path, pattern.id));
                        let width = match data.1.kind {
                            crate::sema::models::EnumVariantKind::Tuple(fields) |
                            crate::sema::models::EnumVariantKind::Struct(fields) => fields.len(),
                            crate::sema::models::EnumVariantKind::Unit => 0,
                        };
                        (Some(data), width)
                    }
                };
                let subpatterns: Vec<_> = self
                    .pattern_field_mapping_with_rest(fields, field_count)
                    .into_iter()
                    .map(|(pattern_index, field_index)| FieldPattern {
                        index: FieldIndex::from_usize(field_index),
                        pattern: self.lower_pattern(&fields[pattern_index]),
                    })
                    .collect();
                match variant {
                    Some((definition, variant)) => PatternKind::Variant { definition, variant, subpatterns },
                    None => PatternKind::Leaf { subpatterns },
                }
            }
            hir::PatternKind::Rest => PatternKind::Wild,
            hir::PatternKind::PathNamed { path, fields, .. } => {
                let data = if matches!(ty.kind(), TyKind::Adt(def, _) if def.kind == crate::sema::models::AdtKind::Enum)
                {
                    let resolution = self.path_resolution(path, pattern.id);
                    Some(self.variant_of_resolution(resolution))
                } else {
                    None
                };
                let declared = crate::sema::tycheck::utils::named_fields::named_fields(
                    self.gcx,
                    ty,
                    data.as_ref().map(|(_, variant)| variant.ctor_def_id),
                )
                .expect("checked named pattern fields");
                let subpatterns = fields
                    .iter()
                    .map(|field| FieldPattern {
                        index: FieldIndex::from_usize(
                            declared
                                .fields
                                .iter()
                                .position(|definition| definition.name == field.name.symbol)
                                .expect("checked field name"),
                        ),
                        pattern: self.lower_pattern(&field.pattern),
                    })
                    .collect();
                if let Some((definition, variant)) = data {
                    PatternKind::Variant {
                        definition,
                        variant,
                        subpatterns,
                    }
                } else {
                    PatternKind::Leaf { subpatterns }
                }
            }
            hir::PatternKind::Or(pats, _) => {
                let patterns = pats.iter().map(|p| self.lower_pattern(p)).collect();
                PatternKind::Or(patterns)
            }
            hir::PatternKind::At { binding, pattern } => PatternKind::At {
                binding: Box::new(self.lower_pattern(binding)),
                pattern: Box::new(self.lower_pattern(pattern)),
            },
            hir::PatternKind::TypeTest { target, binding } => PatternKind::TypeTest {
                target: self.results.node_type(target.id),
                binding: binding.as_ref().map(|p| Box::new(self.lower_pattern(p))),
            },
            hir::PatternKind::Range { .. } => {
                PatternKind::Range(self.results.pattern_ranges[&pattern.id].clone())
            }
            hir::PatternKind::Literal { value: lit } => {
                let ty = self.results.node_type(pattern.id);
                let value = self.lower_literal(lit);
                PatternKind::Constant {
                    value: Constant { ty, value },
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

    fn path_resolution(&self, path: &ConstructorPath, id: NodeID) -> hir::Resolution {
        match path {
            ConstructorPath::Qualified { path } => match path {
                hir::ResolvedPath::Resolved(path) => path.resolution.clone(),
                hir::ResolvedPath::Relative(..) => {
                    let resolution = self.results.value_resolution(id);
                    resolution.expect("expected path resolution")
                }
            },
            ConstructorPath::Inferred { .. } => {
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
        let (ctor_id, ctor_kind) = match resolution {
            hir::Resolution::Definition(ctor_id, kind) => (ctor_id, kind),
            hir::Resolution::StdItem(item) => {
                let ctor_id = self
                    .gcx
                    .std_item_def(item)
                    .expect("std item used in pattern must resolve to a definition");
                let kind = self.gcx.definition_kind(ctor_id);
                (ctor_id, kind)
            }
            _ => unreachable!(),
        };

        if !matches!(ctor_kind, hir::DefinitionKind::VariantConstructor(..)) {
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

        (def.adt_def, *variant)
    }

    fn lower_literal(&self, lit: &hir::Literal) -> ConstantKind<'ctx> {
        match lit {
            hir::Literal::Bool(b) => ConstantKind::Bool(*b),
            hir::Literal::Rune(r) => ConstantKind::Rune(*r),
            hir::Literal::String(s) => ConstantKind::String(*s),
            hir::Literal::Bytes(s) => ConstantKind::Bytes(*s),
            hir::Literal::Integer { value, .. } => ConstantKind::Integer(*value as u64),
            hir::Literal::Float(f) => ConstantKind::Float(*f),
            hir::Literal::Nil => ConstantKind::Unit,
        }
    }
}
