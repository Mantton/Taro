use super::ConstraintSolver;
use crate::{
    sema::{
        error::TypeError,
        models::TyKind,
        resolve::models::DefinitionKind,
        tycheck::{
            solve::{Goal, Obligation, SolverResult, StructLiteralGoalData},
            utils::instantiate::instantiate_struct_definition_with_args,
        },
    },
    span::Spanned,
};

impl<'ctx> ConstraintSolver<'ctx> {
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

                    self.record_field_index(provided_field.node_id, idx);

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
