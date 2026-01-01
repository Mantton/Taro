use crate::{
    compile::context::GlobalContext,
    hir::{self, NodeID, PatternPath, Resolution},
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
                    name: name.symbol,
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
                let subpatterns = pats
                    .iter()
                    .enumerate()
                    .map(|(index, p)| FieldPattern {
                        index: FieldIndex::from_usize(index),
                        pattern: self.lower_pattern(p),
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
                let subpatterns: Vec<_> = fields
                    .iter()
                    .enumerate()
                    .map(|(index, p)| FieldPattern {
                        index: FieldIndex::from_usize(index),
                        pattern: self.lower_pattern(p),
                    })
                    .collect();
                PatternKind::Variant {
                    definition: data.0,
                    variant: data.1,
                    subpatterns,
                }
            }
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
            _ => unimplemented!(
                "Pattern lowering for {:?} not implemented yet",
                pattern.kind
            ),
        };

        Pattern { ty, span, kind }
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
        let Some(&variant) = def.variants.iter().find(|v| v.ctor_def_id == ctor_id) else {
            unreachable!()
        };

        (def.adt_def, variant)
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
}
