use crate::{
    check::solver::{Goal, Obligation, SolverDelegate, SolverResult},
    error::{ExpectedFound, TypeError},
    ty::{Constraint, Ty, TyKind, VariantDefinition},
    utils::instantiate_ty_with_args,
};
use rustc_hash::FxHashMap;
use taroc_hir::{CtorKind, DefinitionKind, NodeID, Resolution};
use taroc_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PatternResolutionGoal<'ctx> {
    pub pattern: &'ctx taroc_hir::Pattern,
    pub scrutinee_ty: Ty<'ctx>,
}

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_pattern_resolve(
        &mut self,
        goal: PatternResolutionGoal<'ctx>,
    ) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(goal.scrutinee_ty);

        if ty.is_ty_var() {
            return SolverResult::Deferred;
        }

        self.check_pattern_kind(
            goal.pattern.id,
            &goal.pattern.kind,
            goal.scrutinee_ty,
            goal.pattern.span,
        )
    }
}

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    fn check_pattern_kind(
        &mut self,
        id: NodeID,
        kind: &'ctx taroc_hir::PatternKind,
        expectation: Ty<'ctx>,
        span: Span,
    ) -> SolverResult<'ctx> {
        match kind {
            taroc_hir::PatternKind::Wildcard => SolverResult::Solved(vec![]),
            taroc_hir::PatternKind::Identifier(_) => {
                self.check_ident_pattern(id, expectation, span)
            }
            taroc_hir::PatternKind::Tuple(patterns, span) => {
                self.check_tuple_pattern(id, patterns, expectation, *span)
            }
            taroc_hir::PatternKind::PathTuple(path, patterns, span) => {
                let res = self.resolve_pattern_path_tuple_struct(id, path);
                self.check_tuple_path_pattern(res, expectation, *span, patterns)
            }
            taroc_hir::PatternKind::PathStruct(path, fields, _, ignore) => {
                let res = self.resolve_pattern_path_struct(id, path);
                self.check_struct_path_pattern(res, expectation, fields, *ignore, path.span)
            }
            taroc_hir::PatternKind::Or(patterns, _) => {
                let mut obligations = vec![];

                for pattern in patterns {
                    let obligation = Obligation {
                        location: pattern.span,
                        goal: Goal::PatternResolution(PatternResolutionGoal {
                            pattern,
                            scrutinee_ty: expectation,
                        }),
                    };

                    obligations.push(obligation);
                }

                return SolverResult::Solved(obligations);
            }
            taroc_hir::PatternKind::Expression(taroc_hir::PatternExpressionKind::Path(path)) => {
                let res = self.resolve_pattern_path_unit(id, path);
                self.check_unit_path_pattern(res, expectation, path.span)
            }
            taroc_hir::PatternKind::Expression(taroc_hir::PatternExpressionKind::AnonConst(_)) => {
                // TODO!
                return SolverResult::Solved(vec![]);
            }
        }
    }

    fn check_ident_pattern(
        &mut self,
        id: NodeID,
        expectation: Ty<'ctx>,
        span: Span,
    ) -> SolverResult<'ctx> {
        let pat_ty = self.fcx.local_ty(id);
        return SolverResult::Solved(vec![Obligation {
            location: span,
            goal: Goal::Constraint(Constraint::TypeEquality(expectation, pat_ty)),
        }]);
    }

    fn check_tuple_pattern(
        &mut self,
        _: NodeID,
        elements: &'ctx [taroc_hir::Pattern],
        expectation: Ty<'ctx>,
        span: Span,
    ) -> SolverResult<'ctx> {
        let len = elements.len();

        let element_tys = (0..len).map(|_| self.icx().next_ty_var(span)).collect();
        let pat_ty = self.gcx().mk_ty(TyKind::Tuple(
            self.gcx().store.interners.intern_ty_list(&element_tys),
        ));

        // Add Coercion Constraint to Tuple
        let mut sub_obligations = vec![Obligation {
            location: span,
            goal: Goal::Coerce {
                from: pat_ty,
                to: expectation,
            },
        }];

        // Add nested Pattern obligations
        for (i, element) in elements.iter().enumerate() {
            let obligation = Obligation {
                location: element.span,
                goal: Goal::PatternResolution(PatternResolutionGoal {
                    pattern: element,
                    scrutinee_ty: element_tys[i],
                }),
            };

            sub_obligations.push(obligation);
        }

        return SolverResult::Solved(sub_obligations);
    }

    fn check_unit_path_pattern(
        &mut self,
        res: Option<ResolvedPattern<'ctx>>,
        expectation: Ty<'ctx>,
        span: Span,
    ) -> SolverResult<'ctx> {
        let Some(res) = res else {
            // TODO: this might want to be an error
            return SolverResult::Solved(vec![]);
        };

        let obligation = Obligation {
            location: span,
            goal: Goal::Constraint(Constraint::TypeEquality(expectation, res.ty)),
        };

        return SolverResult::Solved(vec![obligation]);
    }

    fn check_tuple_path_pattern(
        &mut self,
        res: Option<ResolvedPattern<'ctx>>,
        expectation: Ty<'ctx>,
        span: Span,
        subpats: &'ctx [taroc_hir::Pattern],
    ) -> SolverResult<'ctx> {
        let Some(res) = res else {
            return SolverResult::Error(TypeError::NotATuple);
        };

        let ty = res.ty;
        let (_, variant) = match res.kind {
            ResolvedPatternKind::TupleStruct(res, variant) => (res, variant),
            _ => unreachable!(),
        };

        let fields = &variant.fields;

        // Add Coercion Constraint to scrutinee
        let mut sub_obligations = vec![Obligation {
            location: span,
            goal: Goal::Constraint(Constraint::TypeEquality(expectation, res.ty)),
        }];

        if subpats.len() != fields.len() {
            return SolverResult::Error(TypeError::TupleArity(ExpectedFound::new(
                fields.len(),
                subpats.len(),
            )));
        }

        let TyKind::Adt(_, args) = ty.kind() else {
            unreachable!()
        };

        for (index, pattern) in subpats.iter().enumerate() {
            let obligation = Obligation {
                location: pattern.span,
                goal: Goal::PatternResolution(PatternResolutionGoal {
                    pattern,
                    scrutinee_ty: instantiate_ty_with_args(self.gcx(), fields[index].ty, args),
                }),
            };

            sub_obligations.push(obligation);
        }

        return SolverResult::Solved(sub_obligations);
    }

    fn check_struct_path_pattern(
        &mut self,
        res: Option<ResolvedPattern<'ctx>>,
        expectation: Ty<'ctx>,
        fields: &'ctx [taroc_hir::PatternField],
        ignore_rest: bool,
        path_span: Span,
    ) -> SolverResult<'ctx> {
        let Some(res) = res else {
            return SolverResult::Error(TypeError::NotAStruct(self.gcx().store.common_types.error));
        };

        // Add Coercion Constraint to scrutinee
        let mut sub_obligations = vec![Obligation {
            location: path_span,
            goal: Goal::Constraint(Constraint::TypeEquality(expectation, res.ty)),
        }];

        let definiton = match res.kind {
            ResolvedPatternKind::Struct(definition) => definition,
            _ => unreachable!(),
        };

        sub_obligations.extend(self.check_struct_pattern_fields(
            res.ty,
            definiton,
            fields,
            ignore_rest,
        ));

        SolverResult::Solved(sub_obligations)
    }

    fn check_struct_pattern_fields(
        &self,
        adt_ty: Ty<'ctx>,
        definition: &'ctx VariantDefinition<'ctx>,
        fields: &'ctx [taroc_hir::PatternField],
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

        let mut obligations = vec![];
        for field in fields {
            let ident = field.identifier.symbol;

            let ty = match used.entry(ident) {
                std::collections::hash_map::Entry::Occupied(_) => {
                    // TODO: report field already bound
                    self.fcx.error_ty()
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(field.span);
                    field_map
                        .get(&ident)
                        .map(|(_, f)| instantiate_ty_with_args(self.gcx(), f.ty, args))
                        .unwrap_or_else(|| {
                            non_exisitent.push(field);
                            self.fcx.error_ty()
                        })
                }
            };

            let obligation = Obligation {
                location: field.span,
                goal: Goal::PatternResolution(PatternResolutionGoal {
                    pattern: &field.pattern,
                    scrutinee_ty: ty,
                }),
            };

            obligations.push(obligation);
        }

        // TODO: report unmentioned fields

        obligations
    }
}

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    fn resolve_pattern_path_unit(
        &mut self,
        id: NodeID,
        path: &taroc_hir::Path,
    ) -> Option<ResolvedPattern<'ctx>> {
        let res = self.fcx.perform_path_resolution(id, path);
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
                self.gcx().diagnostics.error(msg, path.span);
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
                let msg = format!("this expresssion is not allowd here");
                self.gcx().diagnostics.error(msg, path.span);
                return None;
            }
        }

        let ty = self.fcx.instantiate_value_path(path, res.clone());
        Some(ResolvedPattern {
            ty,
            kind: ResolvedPatternKind::Path(res),
        })
    }

    fn resolve_pattern_path_tuple_struct(
        &mut self,
        id: NodeID,
        path: &taroc_hir::Path,
    ) -> Option<ResolvedPattern<'ctx>> {
        let res = self.fcx.perform_path_resolution(id, path);
        if let Resolution::Error = res {
            return None;
        };

        let ty = self.fcx.instantiate_value_path(path, res.clone());

        if !ty.is_fn() {
            todo!()
        }

        let ty = match ty.kind() {
            TyKind::FnDef(id, _) => {
                let sig = self.gcx().fn_signature(id);
                sig.output
            }
            _ => unreachable!(),
        };

        let variant = match &res {
            Resolution::Definition(
                _,
                DefinitionKind::AssociatedConstant | DefinitionKind::AssociatedFunction,
            ) => {
                todo!("report unexpected res, requires ctor, found associated symbol")
            }
            Resolution::Definition(id, DefinitionKind::Ctor(_, CtorKind::Fn)) => {
                let gcx = self.gcx();
                let variant_id = gcx.parent(*id);
                let enum_id = gcx.parent(variant_id);

                let enum_def = self
                    .gcx()
                    .with_session_type_database(|db| *db.enums.get(&enum_id).expect(""));
                let Some(&variant) = enum_def.variants.iter().find(|v| v.id == variant_id) else {
                    unreachable!()
                };
                variant
            }
            _ => unreachable!("unexpected pattern resolution"),
        };

        return Some(ResolvedPattern {
            ty,
            kind: ResolvedPatternKind::TupleStruct(res, variant),
        });
    }

    fn resolve_pattern_path_struct(
        &mut self,
        id: NodeID,
        path: &taroc_hir::Path,
    ) -> Option<ResolvedPattern<'ctx>> {
        let (def, ty) = self.fcx.check_struct_path(path, id).ok()?;

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
    Path(Resolution),
    TupleStruct(Resolution, &'ctx VariantDefinition<'ctx>),
    Struct(&'ctx VariantDefinition<'ctx>),
}
