use super::ConstraintSolver;
use crate::{
    sema::{
        error::TypeError,
        models::{Const, Ty, TyKind},
        resolve::models::DefinitionKind,
        tycheck::{
            solve::{Goal, Obligation, SolverResult, StructLiteralGoalData},
            utils::instantiate::instantiate_struct_definition_with_args,
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

    pub fn solve_struct_literal(
        &mut self,
        data: StructLiteralGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let struct_ty = self.icx.resolve_vars_if_possible(data.struct_ty);

        // Defer if the struct type is still an inference variable
        if struct_ty.is_infer() {
            return SolverResult::Deferred;
        }

        // Extract ADT definition
        let TyKind::Adt(adt_def, args) = struct_ty.kind() else {
            let error = Spanned::new(TypeError::NotAStruct { ty: struct_ty }, data.ty_span);
            return SolverResult::Error(vec![error]);
        };

        // Verify it's a struct, not an enum
        if self.gcx().definition_kind(adt_def.id) != DefinitionKind::Struct {
            let error = Spanned::new(TypeError::NotAStruct { ty: struct_ty }, data.ty_span);
            return SolverResult::Error(vec![error]);
        }

        // Get struct definition and fields
        let struct_def = self.gcx().get_struct_definition(adt_def.id);
        let struct_def = instantiate_struct_definition_with_args(self.gcx(), struct_def, args);
        let mut obligations = Vec::new();
        let mut used_fields = vec![false; struct_def.fields.len()];

        // Match provided fields to struct definition fields
        for provided_field in &data.fields {
            let mut found = false;
            for (idx, def_field) in struct_def.fields.iter().enumerate() {
                if def_field.name == provided_field.name {
                    if !self
                        .gcx()
                        .is_visibility_allowed(def_field.visibility, self.current_def)
                    {
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
                let missing_field = &struct_def.fields[idx];
                if !self
                    .gcx()
                    .is_visibility_allowed(missing_field.visibility, self.current_def)
                {
                    let error = Spanned::new(
                        TypeError::FieldNotVisible {
                            name: missing_field.name,
                            struct_ty,
                        },
                        data.span,
                    );
                    return SolverResult::Error(vec![error]);
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

        SolverResult::Solved(obligations)
    }
}
