use super::ConstraintSolver;
use crate::{
    sema::{
        error::TypeError,
        models::{
            AdtKind, Const, ConstKind, ConstValue, EnumVariantKind, GenericArgument, Ty, TyKind,
        },
        tycheck::{
            solve::{Goal, LiteralConstructor, Obligation, SolverResult, StructLiteralGoalData},
            utils::named_fields::named_fields,
        },
    },
    span::{Span, Spanned},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub(super) fn solve_collection_literal(
        &mut self,
        span: Span,
        ty: Ty<'ctx>,
        element: Ty<'ctx>,
        len: Const<'ctx>,
    ) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }
        if let TyKind::Adt(def, args) = ty.kind()
            && Some(def.id) == self.gcx().std_item_def(crate::hir::StdItem::List)
            && let Some(expected) = args.get(0).and_then(|arg| arg.ty())
        {
            return self.solve_constraint_equality(span, expected, element);
        }
        let array = Ty::new(TyKind::Array { element, len }, self.gcx());
        self.solve_constraint_equality(span, ty, array)
    }

    /// Shapes depend on the resolved source types. In particular, a call in
    /// spread position may only reveal its array length after overload solving.
    pub(super) fn solve_spread_shape(
        &mut self,
        span: Span,
        result: Ty<'ctx>,
        element: Ty<'ctx>,
        scalars: usize,
        sources: &[Ty<'ctx>],
        contextual: bool,
    ) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let result = self.structurally_resolve(result);
        if contextual && result.is_infer() {
            return SolverResult::Deferred;
        }
        let list = gcx.std_item_def(crate::hir::StdItem::List);
        if let TyKind::Adt(def, args) = result.kind()
            && Some(def.id) == list
            && let Some(expected) = args[0].ty()
        {
            return self.solve_constraint_equality(span, expected, element);
        }
        let mut total = scalars as u64;
        let mut length = None;
        let mut dynamic = false;
        for source in sources {
            let source = self.structurally_resolve(*source);
            if source.is_infer() {
                return SolverResult::Deferred;
            }
            match source.kind() {
                TyKind::Array {
                    len:
                        Const {
                            kind: ConstKind::Value(ConstValue::Integer(n)),
                            ..
                        },
                    ..
                } => {
                    let Some(sum) = u64::try_from(n).ok().and_then(|n| total.checked_add(n)) else {
                        return SolverResult::Error(vec![Spanned::new(
                            TypeError::SpreadLengthOverflow,
                            span,
                        )]);
                    };
                    total = sum;
                }
                TyKind::Array { len, .. } if length.is_none() => length = Some(len),
                _ => dynamic = true,
            }
        }
        // A sole symbolic length is representable, including alongside empty
        // arrays. The type system has no symbolic addition of const parameters.
        let ty = if dynamic || (length.is_some() && total != 0) {
            if matches!(result.kind(), TyKind::Array { .. }) {
                return SolverResult::Error(vec![Spanned::new(
                    TypeError::DynamicArraySpread,
                    span,
                )]);
            }
            let Some(list) = list else {
                return SolverResult::Error(vec![Spanned::new(TypeError::MissingSpreadList, span)]);
            };
            let args = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(element)]);
            Ty::new(
                TyKind::Adt(gcx.get_struct_definition(list).adt_def, args),
                gcx,
            )
        } else {
            let len = length.unwrap_or(Const {
                ty: gcx.types.uint,
                kind: ConstKind::Value(ConstValue::Integer(i128::from(total))),
            });
            Ty::new(TyKind::Array { element, len }, gcx)
        };
        self.solve_constraint_equality(span, result, ty)
    }

    pub fn solve_struct_literal(
        &mut self,
        data: StructLiteralGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let struct_ty = self.structurally_resolve(data.struct_ty);

        // Defer if the struct type is still an inference variable
        if struct_ty.is_infer() {
            return SolverResult::Deferred;
        }

        if struct_ty.is_error() {
            return SolverResult::Solved(vec![]);
        }
        let mut obligations = Vec::new();
        let constructor = match data.constructor {
            LiteralConstructor::Struct => None,
            LiteralConstructor::Variant(id) => Some(id),
            LiteralConstructor::InferredVariant { node_id, name } => {
                let TyKind::Adt(def, args) = struct_ty.kind() else {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::NotAStruct { ty: struct_ty },
                        data.ty_span,
                    )]);
                };
                if def.kind != AdtKind::Enum {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::NotAStruct { ty: struct_ty },
                        data.ty_span,
                    )]);
                }
                let resolution =
                    match self.resolve_static_member_resolution(struct_ty, name, data.ty_span) {
                        Ok(resolution) => resolution,
                        Err(errors) => return SolverResult::Error(errors),
                    };
                let crate::hir::Resolution::Definition(
                    id,
                    crate::sema::resolve::models::DefinitionKind::VariantConstructor(..),
                ) = resolution
                else {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::NotStructVariant { name: name.symbol },
                        data.ty_span,
                    )]);
                };
                if !self
                    .gcx()
                    .get_enum_definition(def.id)
                    .variants
                    .iter()
                    .any(|variant| {
                        variant.ctor_def_id == id
                            && matches!(variant.kind, EnumVariantKind::Struct(..))
                    })
                {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::NotStructVariant { name: name.symbol },
                        data.ty_span,
                    )]);
                }
                self.record_value_resolution(node_id, resolution);
                obligations.extend(self.constraints_for_def(def.id, Some(args), data.ty_span));
                Some(id)
            }
        };
        let Some(declared) = named_fields(self.gcx(), struct_ty, constructor) else {
            let error = Spanned::new(TypeError::NotAStruct { ty: struct_ty }, data.ty_span);
            return SolverResult::Error(vec![error]);
        };
        let declared = declared.fields;
        let mut used_fields = vec![false; declared.len()];

        // Match provided fields to struct definition fields
        for provided_field in &data.fields {
            let mut found = false;
            for (idx, def_field) in declared.iter().enumerate() {
                if def_field.name == provided_field.name {
                    if def_field.visibility.is_some_and(|visibility| {
                        !self
                            .gcx()
                            .is_visibility_allowed(visibility, self.current_def)
                    }) {
                        let error = Spanned::new(
                            TypeError::FieldNotVisible {
                                name: def_field.name,
                                struct_ty,
                            },
                            provided_field.label_span,
                        );
                        return SolverResult::Error(vec![error]);
                    }
                    found = true;
                    used_fields[idx] = true;

                    // Do not record the entry's slot index here: it would be
                    // keyed by the value expression's NodeID and clobber that
                    // expression's own field index when the value is itself a
                    // member access (e.g. `Pair { a: input.b }`). Consumers
                    // resolve literal entries by field name instead.

                    if let Some(hint) = provided_field.expectation {
                        obligations.push(Obligation {
                            location: provided_field.value_span,
                            goal: Goal::Equal(hint, def_field.ty),
                        });
                    }
                    // Create coercion constraint: provided type -> expected type
                    obligations.push(Obligation {
                        location: provided_field.value_span,
                        goal: Goal::Coerce {
                            node_id: provided_field.node_id,
                            from: provided_field.ty,
                            to: def_field.ty,
                        },
                    });
                    break;
                }
            }

            if !found {
                let error = Spanned::new(
                    TypeError::UnknownStructField {
                        name: provided_field.name,
                        struct_ty,
                    },
                    provided_field.label_span,
                );
                return SolverResult::Error(vec![error]);
            }
        }

        // Check for missing required fields
        for (idx, field_used) in used_fields.iter().enumerate() {
            if !field_used {
                let missing_field = &declared[idx];
                if missing_field.visibility.is_some_and(|visibility| {
                    !self
                        .gcx()
                        .is_visibility_allowed(visibility, self.current_def)
                }) {
                    let error = Spanned::new(
                        TypeError::FieldNotVisible {
                            name: missing_field.name,
                            struct_ty,
                        },
                        data.span,
                    );
                    return SolverResult::Error(vec![error]);
                }
                if data.base_span.is_some() || missing_field.default_provider.is_some() {
                    continue;
                }
                let error = Spanned::new(
                    TypeError::MissingStructField {
                        name: missing_field.name,
                        struct_ty,
                    },
                    data.span,
                );
                return SolverResult::Error(vec![error]);
            }
        }

        if let Some(span) = data.base_span
            && used_fields.iter().all(|used| *used)
        {
            self.gcx().dcx().emit_warning("redundant struct update base: all fields are explicitly supplied; the base is still evaluated".into(), Some(span));
        }
        SolverResult::Solved(obligations)
    }
}

#[cfg(test)]
mod update_tests {
    use crate::test_support::analyze_script_mir_diagnostics;
    #[test]
    fn struct_updates_infer_generics_and_read_reference_bases_explicitly() {
        let source = r#"
struct Pair[T] { first: T; second: T }
func update[T](_ base: Pair[T], _ first: T) -> Pair[T] { Pair { first, ..base } }
func fromReference[T](_ base: &Pair[T], _ first: T) -> Pair[T] { Pair { first, ..*base } }
func main() { var base = Pair { first: 1_i32, second: 2_i32 }; var changed = update(base, 3_i32); var copied = fromReference(&base, 4_i32); }
"#;
        let diagnostics = analyze_script_mir_diagnostics(source);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
    #[test]
    fn redundant_update_base_warns_without_rejecting_the_program() {
        let source = "struct One { value: int32 }; func main() { var base = One { value: 1 }; var next = One { value: 2, ..base }; }";
        crate::test_support::check_script(source, |_, _| {});
        let diagnostics = analyze_script_mir_diagnostics(source);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert!(diagnostics[0].message.contains("base is still evaluated"));
    }
    #[test]
    fn updates_reject_enum_variants_initializers_and_nonmatching_value_types() {
        for (source, expected) in [
            (
                "enum Choice { case value { x: int32; y: int32 } }; func f(_ base: Choice) -> Choice { .value { x: 1, ..base } }; func main() {}",
                "enum variants cannot use",
            ),
            (
                "enum Choice { case value { x: int32; y: int32 } }; func f(_ base: Choice) -> Choice { Choice::value { x: 1, ..base } }; func main() {}",
                "enum variants cannot use",
            ),
            (
                "struct Point { x: int32; y: int32 }; extend Point { init() { self.x = 1; self.y = 2 }; }; func f(_ base: Point) -> Point { Point { x: 3, ..base } }; func main() {}",
                "declaring init",
            ),
            (
                "struct Point { x: int32; y: int32 }; func f(_ base: &Point) -> Point { Point { x: 3, ..base } }; func main() {}",
                "expected Point, found &Point",
            ),
            (
                "struct Pair[T] { first: T; second: T }; func f(_ base: Pair[bool]) -> Pair[int32] { Pair[int32] { first: 3, ..base } }; func main() {}",
                "bool",
            ),
        ] {
            let diagnostics = analyze_script_mir_diagnostics(source);
            assert!(
                diagnostics.iter().any(|d| d.message.contains(expected)),
                "{source}: {diagnostics:#?}"
            );
        }
    }
    #[test]
    fn update_places_do_not_copy_the_whole_base() {
        use crate::mir::{Operand, PlaceElem, Rvalue, StatementKind};
        crate::test_support::analyze_script_built_mir(
            "struct Pair { first: int32; second: int32 }; func update(_ base: Pair) -> Pair { Pair { first: 3, ..base } }; func main() {}",
            |bodies, gcx| {
                let body = bodies
                    .iter()
                    .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "update")
                    .unwrap();
                let operands: Vec<_> = body
                    .basic_blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .filter_map(|statement| match &statement.kind {
                        StatementKind::Assign(_, Rvalue::Aggregate { fields, .. }) => Some(fields),
                        _ => None,
                    })
                    .flatten()
                    .collect();
                assert!(operands.iter().any(|operand| matches!(operand, Operand::Copy(place) if matches!(place.projection.last(), Some(PlaceElem::Field(index, _)) if index.index() == 1))));
                assert!(!body.basic_blocks.iter().flat_map(|block| &block.statements).any(|statement| matches!(&statement.kind, StatementKind::Assign(_, Rvalue::Use(Operand::Copy(place))) if place.projection.is_empty() && matches!(body.locals[place.local].ty.kind(), crate::sema::models::TyKind::Adt(..)))));
            },
        );
    }
}
