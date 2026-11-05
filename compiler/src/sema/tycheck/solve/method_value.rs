//! Receiverless signature selection precedes environment construction. Keep
//! overload probing free of synthetic closure/capture publication.
use super::{
    BindInterfaceMethodGoalData, BindMethodValueGoalData, BindOverloadGoalData, ConstraintSolver,
    Goal, MethodValueSignatureGoalData, Obligation, SolverResult,
};
use crate::{
    sema::{
        error::TypeError,
        models::{Ty, TyKind},
        tycheck::utils::{instantiate::instantiate_ty_with_args, normalize_aliases},
    },
    span::{Span, Spanned},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub(super) fn solve_bind_method_value(
        &mut self,
        location: Span,
        data: BindMethodValueGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        if self.gcx().definition_is_unsafe(data.source) {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::UnsafeCallableValueNotAllowed {
                    name: self.gcx().definition_symbol_or_fallback(data.source),
                },
                location,
            )]);
        }
        let arguments = match self.explicit_method_value_arguments(location, &data) {
            Ok(arguments) => arguments,
            Err(error) => return SolverResult::Error(vec![Spanned::new(error, location)]),
        };
        let method_ty = self.icx.next_ty_var(location);
        let bind = match data.call_info {
            Some(call_info) => Goal::BindInterfaceMethod(BindInterfaceMethodGoalData {
                node_id: data.node_id,
                var_ty: method_ty,
                candidate_ty: data.candidate_ty,
                call_info,
                instantiation_args: arguments,
            }),
            None => Goal::BindOverload(BindOverloadGoalData {
                static_owner: None,
                node_id: data.node_id,
                var_ty: method_ty,
                candidate_ty: data.candidate_ty,
                source: data.source,
                instantiation_args: arguments,
            }),
        };
        SolverResult::Solved(vec![
            Obligation {
                location,
                goal: bind,
            },
            Obligation {
                location,
                goal: Goal::MethodValueSignature(MethodValueSignatureGoalData {
                    node_id: data.node_id,
                    source: data.source,
                    method_ty,
                    callback_ty: data.var_ty,
                    receiver: data.receiver,
                    signature_hint: data.signature_hint,
                }),
            },
        ])
    }

    /// Convert explicit syntax only inside its method candidate's probe. Const
    /// arguments need the formal scalar type, and parent arguments come from
    /// the actual receiver. Failed candidates publish no diagnostics or captures.
    fn explicit_method_value_arguments(
        &mut self,
        location: Span,
        data: &BindMethodValueGoalData<'ctx>,
    ) -> Result<Option<crate::sema::models::GenericArguments<'ctx>>, TypeError<'ctx>> {
        use crate::sema::{
            models::{Const, GenericArgument, GenericParameterDefinitionKind},
            tycheck::{
                lower::{DefTyLoweringCtx, TypeLowerer},
                utils::{
                    generics::{GenericsBuilder, const_param_from_type_arg},
                    instantiate::instantiate_ty_with_args,
                },
            },
        };
        let Some(explicit) = &data.explicit_arguments else {
            return Ok(data.instantiation_args);
        };
        let gcx = self.gcx();
        let generics = gcx.generics_of(data.source);
        if explicit.arguments.len() > generics.parameters.len() {
            return Err(TypeError::ExplicitMethodArguments(format!(
                "excess method generic arguments: expected at most {}, provided {}",
                generics.parameters.len(),
                explicit.arguments.len()
            )));
        }
        let identity = GenericsBuilder::identity_for_item(gcx, data.source);
        // Only the receiver's parent parameters need probing variables. Fresh
        // method-own variables replaced by explicit arguments would remain as
        // orphan inference obligations and incorrectly fail final inference.
        let initial = GenericsBuilder::for_item(gcx, data.source, |parameter, _| {
            if parameter.index >= generics.parent_count {
                return identity[parameter.index];
            }
            if gcx.erased_access_context(data.source).is_some() {
                return identity[parameter.index];
            }
            data.instantiation_args
                .and_then(|arguments| arguments.get(parameter.index).copied())
                .unwrap_or_else(|| self.icx.var_for_generic_param(parameter, location))
        });
        let input = gcx.get_signature(data.source).inputs[0].ty;
        let formal = instantiate_ty_with_args(gcx, input, initial);
        let formal = normalize_aliases(gcx, formal);
        let actual = self.structurally_resolve(data.receiver);
        let owner = gcx.class_ancestry(actual).into_iter().find(|ancestor|
            matches!((ancestor.kind(), formal.kind()), (TyKind::Adt(a, _), TyKind::Adt(b, _)) if a.id == b.id)).unwrap_or(actual);
        self.unify(formal, owner)?;
        let parent = self.icx.resolve_args_if_possible(initial);
        let lower = DefTyLoweringCtx::new(self.current_def, gcx);
        let (arguments, diagnostics) = gcx.dcx().with_deferred_diagnostics(||
            GenericsBuilder::for_item(gcx, data.source, |parameter, prefix| {
                if parameter.index < generics.parent_count { return parent[parameter.index]; }
                let prefix = gcx.store.interners.intern_generic_args_slice(prefix);
                let Some(argument) = explicit.arguments.get(parameter.index - generics.parent_count) else {
                    return self.instantiate_missing_generic_arg(data.source, parameter, prefix.as_slice(), location);
                };
                match (&parameter.kind, argument) {
                    (GenericParameterDefinitionKind::Type { .. }, crate::hir::TypeArgument::Type(ty)) =>
                        GenericArgument::Type(lower.lowerer().lower_type(ty)),
                    (GenericParameterDefinitionKind::Const { .. }, argument) => {
                        let expected = gcx.try_generic_const_param_ty(parameter.id).expect("collected const parameter type");
                        let expected = instantiate_ty_with_args(gcx, expected, prefix);
                        let value = match argument {
                            crate::hir::TypeArgument::Const(value) => lower.lowerer().lower_const_argument(expected, value),
                            crate::hir::TypeArgument::Type(value) => {
                                if let Some(value) = const_param_from_type_arg(gcx, lower.lowerer(), value) {
                                    if value.ty != expected { gcx.dcx().emit_error("const argument type does not match the method parameter".into(), Some(explicit.span)); }
                                    Const { ty: expected, kind: value.kind }
                                } else {
                                    gcx.dcx().emit_error("expected const method argument".into(), Some(value.span));
                                    lower.lowerer().error_const()
                                }
                            }
                            _ => {
                                gcx.dcx().emit_error("associated type bindings are not method arguments".into(), Some(explicit.span));
                                lower.lowerer().error_const()
                            }
                        };
                        GenericArgument::Const(value)
                    }
                    _ => {
                        gcx.dcx().emit_error("expected type method argument".into(), Some(explicit.span));
                        GenericArgument::Type(gcx.types.error)
                    }
                }
            }));
        if let Some(error) = diagnostics
            .into_iter()
            .find(|diagnostic| diagnostic.level == crate::diagnostics::DiagnosticLevel::Error)
        {
            return Err(TypeError::ExplicitMethodArguments(error.message));
        }
        Ok(Some(arguments))
    }

    pub(super) fn solve_method_value_signature(
        &mut self,
        location: Span,
        data: MethodValueSignatureGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(data.method_ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }
        let TyKind::FnPointer {
            inputs, mut output, ..
        } = ty.kind()
        else {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::NotCallable { found: ty },
                location,
            )]);
        };
        let Some(receiver) = inputs.first().copied() else {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::NotCallable { found: ty },
                location,
            )]);
        };
        let receiver = normalize_aliases(self.gcx(), receiver);
        if self.gcx().definition_is_async(data.source) {
            let arguments = self
                .instantiation_args
                .get(&data.node_id)
                .copied()
                .unwrap_or_default();
            output = instantiate_ty_with_args(
                self.gcx(),
                self.gcx().function_body_output(data.source),
                arguments,
            );
        }
        let actual_receiver = self.structurally_resolve(data.receiver);
        if let Some(refined) = self.gcx().class_self_result(actual_receiver, data.source) {
            output = refined;
        }
        // The capture remains the actual subclass slot. Infer the inherited
        // declaration's generic coordinates from its matching ancestor.
        let receiver_match = self
            .gcx()
            .class_ancestry(actual_receiver)
            .into_iter()
            .find(|ancestor| {
                matches!((ancestor.kind(), receiver.kind()),
                (TyKind::Adt(a, _), TyKind::Adt(b, _)) if a.id == b.id)
            })
            .unwrap_or(actual_receiver);
        let callback = Ty::new(
            TyKind::FnPointer {
                effects: Default::default(),
                inputs: self
                    .gcx()
                    .store
                    .interners
                    .intern_ty_list(inputs[1..].to_vec()),
                output,
            },
            self.gcx(),
        );
        let mut obligations = vec![
            Obligation {
                location,
                goal: Goal::ConstraintEqual(receiver, receiver_match),
            },
            Obligation {
                location,
                goal: Goal::ConstraintEqual(data.callback_ty, callback),
            },
        ];
        if let Some(hint) = data.signature_hint {
            obligations.push(Obligation {
                location,
                goal: Goal::ConstraintEqual(callback, hint),
            });
        }
        SolverResult::Solved(obligations)
    }
}
