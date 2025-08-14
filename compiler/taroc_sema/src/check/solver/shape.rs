use std::collections::HashSet;

use crate::{
    check::solver::{Goal, Obligation, SolverDelegate, SolverResult},
    error::{ExpectedFound, TypeError},
    ty::{Constraint, Ty, TyKind, VariantDefinition},
    utils::instantiate_ty_with_args,
};
use rustc_hash::FxHashMap;
use taroc_hir::DefinitionID;
use taroc_span::{Identifier, Span};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shape<'ctx> {
    pub span: Span,
    pub kind: ShapeKind<'ctx>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ShapeKind<'ctx> {
    Wildcard,
    Typed(Ty<'ctx>),
    Tuple(&'ctx [Shape<'ctx>]),
    PathTuple {
        path_ty: Ty<'ctx>,
        variant: DefinitionID,
        elements: &'ctx [Shape<'ctx>],
    },
    PathStruct {
        path_ty: Ty<'ctx>,
        variant: DefinitionID,
        fields: &'ctx [ShapeField<'ctx>],
        ignore_rest: bool,
    },
    Or(&'ctx [Shape<'ctx>]),
    Malformed,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ShapeField<'ctx> {
    pub ident: Identifier,
    pub shape: Shape<'ctx>,
    pub span: Span,
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_shape(
        &mut self,
        shape: Shape<'ctx>,
        scrutinee_ty: Ty<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(scrutinee_ty);

        if ty.is_ty_var() {
            return SolverResult::Deferred;
        }

        self.check_shape_kind(shape.kind, ty, location)
    }

    fn check_shape_kind(
        &self,
        shape: ShapeKind<'ctx>,
        scrutinee_ty: Ty<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        match shape {
            ShapeKind::Wildcard | ShapeKind::Malformed => SolverResult::Solved(vec![]),
            ShapeKind::Tuple(shapes) => self.check_tuple_shape(shapes, scrutinee_ty, location),
            ShapeKind::Or(shapes) => self.check_or_shape(shapes, scrutinee_ty),
            ShapeKind::Typed(ty) => self.check_typed_shape(ty, scrutinee_ty, location),
            ShapeKind::PathTuple {
                path_ty,
                variant,
                elements,
            } => self.check_tuple_path_shape(scrutinee_ty, path_ty, variant, elements, location),
            ShapeKind::PathStruct {
                path_ty,
                variant,
                fields,
                ignore_rest,
            } => self.check_struct_path_shape(
                scrutinee_ty,
                path_ty,
                variant,
                fields,
                ignore_rest,
                location,
            ),
        }
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    fn check_typed_shape(
        &self,
        ty: Ty<'ctx>,
        expectation: Ty<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        return SolverResult::Solved(vec![Obligation {
            location,
            goal: Goal::Constraint(Constraint::TypeEquality(expectation, ty)),
        }]);
    }
    fn check_tuple_shape(
        &self,
        elements: &'ctx [Shape<'ctx>],
        expectation: Ty<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        let len = elements.len();

        let element_tys = (0..len).map(|_| self.icx().next_ty_var(location)).collect();
        let pat_ty = self.gcx().mk_ty(TyKind::Tuple(
            self.gcx().store.interners.intern_ty_list(&element_tys),
        ));

        // Add Coercion Constraint to Tuple
        let mut sub_obligations = vec![Obligation {
            location,
            goal: Goal::Coerce {
                from: pat_ty,
                to: expectation,
            },
        }];

        // Add nested Pattern obligations
        for (i, &shape) in elements.iter().enumerate() {
            let obligation = Obligation {
                location: shape.span,
                goal: Goal::Shape {
                    shape,
                    scrutinee_ty: element_tys[i],
                },
            };

            sub_obligations.push(obligation);
        }

        return SolverResult::Solved(sub_obligations);
    }

    fn check_or_shape(
        &self,
        shapes: &'ctx [Shape<'ctx>],
        expectation: Ty<'ctx>,
    ) -> SolverResult<'ctx> {
        let mut obligations = vec![];
        for shape in shapes {
            let obligation = Obligation {
                location: shape.span,
                goal: Goal::Shape {
                    scrutinee_ty: expectation,
                    shape: *shape,
                },
            };

            obligations.push(obligation);
        }

        return SolverResult::Solved(obligations);
    }

    fn check_tuple_path_shape(
        &self,
        scrutinee_ty: Ty<'ctx>,
        path_ty: Ty<'ctx>,
        variant_id: DefinitionID,
        elements: &'ctx [Shape<'ctx>],
        location: Span,
    ) -> SolverResult<'ctx> {
        let Some(variant) = self.gcx().with_type_database(variant_id.package(), |db| {
            db.variants.get(&variant_id).cloned()
        }) else {
            unreachable!()
        };
        let fields = &variant.fields;

        // Add Coercion Constraint to scrutinee
        let mut sub_obligations = vec![Obligation {
            location,
            goal: Goal::Constraint(Constraint::TypeEquality(scrutinee_ty, path_ty)),
        }];

        if elements.len() != fields.len() {
            return SolverResult::Error(TypeError::TupleArity(ExpectedFound::new(
                fields.len(),
                elements.len(),
            )));
        }

        let TyKind::Adt(_, args) = path_ty.kind() else {
            unreachable!()
        };

        for (index, &shape) in elements.iter().enumerate() {
            let obligation = Obligation {
                location: shape.span,
                goal: Goal::Shape {
                    scrutinee_ty: instantiate_ty_with_args(self.gcx(), fields[index].ty, args),
                    shape,
                },
            };

            sub_obligations.push(obligation);
        }

        return SolverResult::Solved(sub_obligations);
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    fn check_struct_path_shape(
        &self,
        scrutinee_ty: Ty<'ctx>,
        path_ty: Ty<'ctx>,
        variant_id: DefinitionID,
        fields: &'ctx [ShapeField<'ctx>],
        ignore_rest: bool,
        location: Span,
    ) -> SolverResult<'ctx> {
        let Some(variant) = self.gcx().with_type_database(variant_id.package(), |db| {
            db.variants.get(&variant_id).cloned()
        }) else {
            unreachable!()
        };
        // Add Coercion Constraint to scrutinee
        let mut sub_obligations = vec![Obligation {
            location,
            goal: Goal::Constraint(Constraint::TypeEquality(scrutinee_ty, path_ty)),
        }];

        sub_obligations.extend(self.check_struct_pattern_fields(
            path_ty,
            variant,
            fields,
            ignore_rest,
        ));

        SolverResult::Solved(sub_obligations)
    }

    fn check_struct_pattern_fields(
        &self,
        adt_ty: Ty<'ctx>,
        definition: &'ctx VariantDefinition<'ctx>,
        fields: &'ctx [ShapeField],
        _ignore_rest: bool,
    ) -> Vec<Obligation<'ctx>> {
        let TyKind::Adt(_, args) = adt_ty.kind() else {
            unreachable!("pattern is not of adt type")
        };

        let field_map = definition
            .fields
            .iter_enumerated()
            .map(|(i, f)| (f.name, (i, f)))
            .collect::<FxHashMap<_, _>>();

        let mut used = FxHashMap::default();
        let mut non_exisitent = vec![];
        let mut already_bound = HashSet::new();

        let mut obligations = vec![];
        for field in fields {
            let ident = field.ident.symbol;

            let ty = match used.entry(ident) {
                std::collections::hash_map::Entry::Occupied(pre) => {
                    already_bound.insert((ident, field.span, *pre.get())); // ident, span, previous_span
                    self.gcx().store.common_types.error
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(field.span);
                    field_map
                        .get(&ident)
                        .map(|(_, f)| instantiate_ty_with_args(self.gcx(), f.ty, args))
                        .unwrap_or_else(|| {
                            non_exisitent.push(field);
                            self.gcx().store.common_types.error
                        })
                }
            };

            let obligation = Obligation {
                location: field.span,
                goal: Goal::Shape {
                    scrutinee_ty: ty,
                    shape: field.shape,
                },
            };

            obligations.push(obligation);
        }

        // TODO: report unmentioned fields/ non existent fields

        obligations
    }
}
