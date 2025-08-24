use crate::{
    check::{
        context::func::FnCtx,
        solver::{
            Goal, Obligation,
            shape::{Shape, ShapeField, ShapeKind},
        },
    },
    lower::TypeLowerer,
    ty::{Ty, TyKind, VariantDefinition},
};
use taroc_hir::{CtorKind, DefinitionKind, NodeID, Resolution};

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn add_shape_obligation(&self, pattern: &taroc_hir::Pattern, scrutinee_ty: Ty<'gcx>) {
        let shape = self.lower_pattern_to_shape(pattern);
        let obligation = Obligation {
            goal: Goal::Shape {
                scrutinee_ty,
                shape,
            },
            location: pattern.span,
        };
        self.add_obligation(obligation);
    }

    fn lower_pattern_to_shape(&self, pattern: &taroc_hir::Pattern) -> Shape<'gcx> {
        let span = pattern.span;
        let mk = |patterns: &Vec<taroc_hir::Pattern>| {
            let items: Vec<_> = patterns
                .iter()
                .map(|p| self.lower_pattern_to_shape(p))
                .collect();
            let items = self.gcx.alloc_slice(&items);
            items
        };

        let kind = match &pattern.kind {
            taroc_hir::PatternKind::Wildcard => ShapeKind::Wildcard,
            taroc_hir::PatternKind::Identifier(_) => ShapeKind::Typed(self.local_ty(pattern.id)),
            taroc_hir::PatternKind::Tuple(patterns, ..) => ShapeKind::Tuple(mk(patterns)),
            taroc_hir::PatternKind::Or(patterns, ..) => ShapeKind::Or(mk(patterns)),
            taroc_hir::PatternKind::PathTuple(path, patterns, ..) => {
                let Some(res) = self.resolve_pattern_path_tuple_struct(pattern.id, path) else {
                    self.gcx
                        .diagnostics
                        .error("expected tuple-like enum/struct ctor".into(), path.span);
                    return Shape {
                        span,
                        kind: ShapeKind::Malformed,
                        id: NodeID::new(0),
                    };
                };

                let variant = match res.kind {
                    ResolvedPatternKind::TupleStruct(variant) => variant,
                    _ => unreachable!(),
                };

                let elements = mk(patterns);
                ShapeKind::PathTuple {
                    path_ty: res.ty,
                    variant: variant.id,
                    elements: elements,
                }
            }
            taroc_hir::PatternKind::PathStruct(path, fields, _, rest) => {
                let Some(res) = self.resolve_pattern_path_struct(pattern.id, path) else {
                    self.gcx.diagnostics.error(
                        "expected struct-like enum variant or struct".into(),
                        path.span,
                    );
                    return Shape {
                        span,
                        kind: ShapeKind::Malformed,
                        id: NodeID::new(0),
                    };
                };

                let definition = match res.kind {
                    ResolvedPatternKind::Struct(definition) => definition,
                    _ => unreachable!(),
                };

                let fields = self.gcx.alloc_slice(
                    &fields
                        .iter()
                        .map(|f| self.lower_pattern_field_to_shape(f))
                        .collect::<Vec<_>>(),
                );

                ShapeKind::PathStruct {
                    path_ty: res.ty,
                    variant: definition.id,
                    fields,
                    ignore_rest: *rest,
                }
            }
            taroc_hir::PatternKind::Expression(taroc_hir::PatternExpressionKind::Path(path)) => {
                let Some(res) = self.resolve_pattern_path_unit(pattern.id, path) else {
                    self.gcx()
                        .diagnostics
                        .error("expected unit variant or const".into(), span);
                    return Shape {
                        span,
                        kind: ShapeKind::Malformed,
                        id: NodeID::new(0),
                    };
                };

                ShapeKind::Typed(res.ty)
            }
            taroc_hir::PatternKind::Expression(taroc_hir::PatternExpressionKind::AnonConst(_)) => {
                ShapeKind::Malformed
            }
        };

        let shape = Shape {
            span,
            kind,
            id: pattern.id,
        };
        shape
    }

    fn lower_pattern_field_to_shape(&self, field: &taroc_hir::PatternField) -> ShapeField<'gcx> {
        ShapeField {
            ident: field.identifier,
            span: field.span,
            shape: self.lower_pattern_to_shape(&field.pattern),
        }
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn resolve_pattern_path_unit(
        &self,
        id: NodeID,
        path: &taroc_hir::Path,
    ) -> Option<ResolvedPattern<'ctx>> {
        let res = self.perform_path_resolution(id, path);
        if let Resolution::Error = res {
            return None;
        };
        match res {
            Resolution::Definition(
                _,
                DefinitionKind::AssociatedFunction
                | DefinitionKind::Ctor(_, CtorKind::Fn)
                | DefinitionKind::Variant,
            ) => {
                let msg = format!("expected enum unit variant");
                self.gcx.diagnostics.error(msg, path.span);
                return None;
            }
            Resolution::Definition(
                _,
                DefinitionKind::Ctor(_, CtorKind::Const)
                | DefinitionKind::Constant
                | DefinitionKind::AssociatedConstant,
            ) => {
                // Valid!
            }
            _ => {
                let msg = format!("this expresssion is not allowed here");
                self.gcx.diagnostics.error(msg, path.span);
                return None;
            }
        }

        let ty = self.instantiate_value_path(path, res.clone());
        Some(ResolvedPattern {
            ty,
            kind: ResolvedPatternKind::Path,
        })
    }

    fn resolve_pattern_path_tuple_struct(
        &self,
        id: NodeID,
        path: &taroc_hir::Path,
    ) -> Option<ResolvedPattern<'ctx>> {
        let res = self.perform_path_resolution(id, path);
        if let Resolution::Error = res {
            return None;
        };

        let ty = self.instantiate_value_path(path, res.clone());

        if !ty.is_fn() {
            todo!()
        }

        let ty = match ty.kind() {
            TyKind::FnDef(id, _) => {
                let sig = self.gcx.fn_signature(id);
                sig.output
            }
            _ => unreachable!(),
        };

        let variant = match &res {
            Resolution::Definition(
                _,
                DefinitionKind::AssociatedConstant | DefinitionKind::AssociatedFunction,
            ) => {
                self.gcx.diagnostics.error(
                    "expected tuple-like enum/struct ctor, found associated sybol".into(),
                    path.span,
                );
                return None;
            }
            Resolution::Definition(id, DefinitionKind::Ctor(_, CtorKind::Fn)) => {
                let gcx = self.gcx;
                let variant_id = gcx.parent(*id);
                let enum_id = gcx.parent(variant_id);

                let enum_def =
                    gcx.with_session_type_database(|db| *db.enums.get(&enum_id).expect(""));
                let Some(&variant) = enum_def.variants.iter().find(|v| v.id == variant_id) else {
                    unreachable!("variant definition must exist")
                };
                variant
            }
            _ => unreachable!("unexpected pattern resolution"),
        };

        return Some(ResolvedPattern {
            ty,
            kind: ResolvedPatternKind::TupleStruct(variant),
        });
    }

    fn resolve_pattern_path_struct(
        &self,
        id: NodeID,
        path: &taroc_hir::Path,
    ) -> Option<ResolvedPattern<'ctx>> {
        let (def, ty) = self.check_struct_path(path, id).ok()?;

        Some(ResolvedPattern {
            ty,
            kind: ResolvedPatternKind::Struct(def),
        })
    }
}

struct ResolvedPattern<'ctx> {
    ty: Ty<'ctx>,
    kind: ResolvedPatternKind<'ctx>,
}

enum ResolvedPatternKind<'ctx> {
    Path,
    TupleStruct(&'ctx VariantDefinition<'ctx>),
    Struct(&'ctx VariantDefinition<'ctx>),
}
