use crate::{
    GlobalContext,
    check::{
        nodes::utils::associated_functions_for_ty,
        solver::{
            Goal, MethodCallGoal, Obligation, OverloadArgument, SolverDelegate, SolverResult,
        },
    },
    error::TypeError,
    ty::{Ty, TyKind},
    utils::{instantiate_constraint_with_args, instantiate_ty_with_args, labeled_signature_to_ty},
};
use taroc_hir::DefinitionID;
use taroc_span::{Identifier, Span};
use crate::infer::{OverloadCallKind, OverloadResolution};

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_method_call(&mut self, goal: MethodCallGoal<'ctx>) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let recv_ty = self.structurally_resolve(goal.receiver_ty);
        let Some(_) = gcx.try_simple_type(recv_ty) else {
            return SolverResult::Deferred;
        };

        // Iteratively Collect All Possible Candidates By Auto Dereferening the reciever ty
        let mut candidates =
            self.collect_all_method_candidates(recv_ty, goal.call_span, goal.method);
        if candidates.is_empty() {
            return SolverResult::Error(TypeError::UnknownMethod(goal.method.symbol, recv_ty));
        };

        candidates.retain(|&c| quick_match_method(c, goal.arguments, goal.label_agnostic, gcx));
        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        if let [candidate] = candidates.as_slice() {
            let obligations = self.select_fn_for_method(
                *candidate,
                recv_ty,
                &goal,
                Some(OverloadCallKind::Method),
            );
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(candidate, recv_ty, &goal) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            let obligations = self.select_fn_for_method(
                *candidate,
                recv_ty,
                &goal,
                Some(OverloadCallKind::Method),
            );
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }

    pub fn evaluate_method_candidate(
        &self,
        candidate: DefinitionID,
        recv_ty: crate::ty::Ty<'ctx>,
        goal: &MethodCallGoal<'ctx>,
    ) -> bool {
        self.icx().probe(|_| {
            let mut ctx = SolverDelegate::new(self.icx(), self.param_env);
            let obligations = ctx.select_fn_for_method(
                candidate,
                recv_ty,
                goal,
                Some(OverloadCallKind::Method),
            );
            ctx.add_obligations(obligations);
            let result = ctx.solve_nested_goals();
            result.is_ok()
        })
    }

    pub fn select_fn_for_method(
        &mut self,
        candidate: DefinitionID,
        recv_ty: Ty<'ctx>,
        goal: &MethodCallGoal<'ctx>,
        record_kind: Option<OverloadCallKind>,
    ) -> Vec<Obligation<'ctx>> {
        let mut pending = vec![];
        let gcx = self.gcx();
        let signature = gcx.fn_signature(candidate);
        let fn_args = self.icx().fresh_args_for_def(candidate, goal.call_span);
        let fn_sig_ty =
            instantiate_ty_with_args(gcx, labeled_signature_to_ty(signature, gcx), fn_args);

        let (inputs, output) = match fn_sig_ty.kind() {
            TyKind::Function { inputs, output, .. } => (inputs, output),
            _ => unreachable!(),
        };

        if !inputs.is_empty() {
            pending.push(Obligation {
                location: goal.call_span,
                goal: Goal::RecieverCoerce {
                    from: recv_ty,
                    to: inputs[0],
                },
            });
        }

        for (arg, param) in goal.arguments.iter().zip(inputs.iter().skip(1)) {
            pending.push(Obligation {
                location: arg.span,
                goal: Goal::Coerce {
                    from: arg.ty,
                    to: *param,
                },
            });
        }

        pending.push(Obligation {
            location: goal.call_span,
            goal: Goal::Coerce {
                from: goal.result_var,
                to: output,
            },
        });

        if let Some(expected) = goal.expected_result_ty {
            pending.push(Obligation {
                location: goal.call_span,
                goal: Goal::Coerce {
                    from: goal.result_var,
                    to: expected,
                },
            });
        }

        gcx.canon_predicates_of(candidate).iter().for_each(|sp| {
            let c = instantiate_constraint_with_args(gcx, sp.value, fn_args);
            pending.push(Obligation {
                location: goal.call_span,
                goal: Goal::Constraint(c),
            });
        });

        if let Some(kind) = record_kind {
            self.icx()
                .record_overload_call(goal.call_span, kind, OverloadResolution::Member(candidate));
        }

        pending
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn collect_all_method_candidates(
        &self,
        recv_ty: Ty<'ctx>,
        recv_span: Span,
        method: Identifier,
    ) -> Vec<DefinitionID> {
        let mut candidates = vec![];
        let mut autoderef = self.autoderef(recv_span, recv_ty);
        while let Some(recv) = autoderef.next() {
            let recv_candidates = associated_functions_for_ty(method, recv, self.gcx());
            candidates.extend(recv_candidates);
        }
        candidates.dedup();
        candidates
    }
}

fn quick_match_method<'ctx>(
    candidate: DefinitionID,
    call_arguments: &'ctx [OverloadArgument<'ctx>],
    label_agnostic: bool,
    gcx: GlobalContext<'ctx>,
) -> bool {
    let fn_sig = gcx.fn_signature(candidate);
    if fn_sig.inputs.is_empty() {
        return false;
    }

    let call_arity = call_arguments.len();
    let min_required = fn_sig.min_parameter_count().saturating_sub(1);
    let param_count = fn_sig.inputs.len() - 1;

    if call_arity < min_required {
        return false;
    }
    if call_arity > param_count && !fn_sig.is_variadic {
        return false;
    }

    let upto = call_arity.min(param_count);
    if !label_agnostic {
        for index in 0..upto {
            let call_label = call_arguments[index].label.map(|f| f.symbol);
            let decl_label = fn_sig.inputs[index + 1].label;
            let decl_defaulted = min_required < param_count && index >= min_required;
            match (decl_label, decl_defaulted, call_label) {
                (None, _, Some(_)) => return false,
                (Some(_), false, None) => return false,
                (Some(d), false, Some(c)) if c != d => return false,
                _ => {}
            }
        }
    }

    true
}
