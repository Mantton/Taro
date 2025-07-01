use crate::{
    GlobalContext,
    check::solver::{
        Goal, Obligation, OverloadArgument, OverloadGoal, SolverDelegate, SolverResult,
    },
    error::TypeError,
    ty::{Constraint, InferTy, TyKind},
    utils::{instantiate_constraint_with_args, instantiate_ty_with_args, labeled_signature_to_ty},
};
use taroc_hir::DefinitionID;

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_application(&mut self, goal: OverloadGoal<'ctx>) -> SolverResult<'ctx> {
        let ty = self.icx().shallow_resolve(goal.callee_var);
        let fid = match ty.kind() {
            TyKind::Infer(InferTy::FnVar(fid)) => fid,
            TyKind::Infer(InferTy::TyVar(..)) => {
                self.gcx().diagnostics.warn(
                    format!("Defering Due to {}", ty.format(self.gcx())),
                    goal.callee_span,
                );
                return SolverResult::Deferred;
            }
            _ => {
                todo!("handle non-funtion var type")
            }
        };

        let data = self.icx().inner.borrow_mut().fn_variables().var_data(fid);
        let mut data = data.borrow_mut();

        // Quick Filter
        {
            data.candidates
                .retain(|&c| quick_match(c, &goal.arguments, self.gcx()));
            data.update(self.gcx());
        }

        // No survivors, exit resolution
        if data.candidates.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        };

        // single survivor, add obligations as subgoals
        if let [candidate] = data.candidates.as_slice() {
            let obligations = self.select_fn_for_application(*candidate, &goal);
            return SolverResult::Solved(obligations);
        }

        // mulitple survivors, check each
        let mut valid_candidates = vec![];
        for &candidate in &data.candidates {
            let ok = self.evaluate_candidate(candidate, &goal);
            if ok {
                valid_candidates.push(candidate);
            }
        }

        // single survivor after check, add obligations as subgoals
        if let [candidate] = data.candidates.as_slice() {
            let obligations = self.select_fn_for_application(*candidate, &goal);
            return SolverResult::Solved(obligations);
        }

        // multiple survivors after pass
        // we want to defer this obligation with the new, trimmed obligation list
        data.candidates = valid_candidates;
        return SolverResult::Deferred;
    }

    fn evaluate_candidate(&self, candidate: DefinitionID, goal: &OverloadGoal<'ctx>) -> bool {
        self.icx().probe(|_| {
            let mut ctx = SolverDelegate::new(self.fcx, self.param_env);
            let obligations = ctx.select_fn_for_application(candidate, goal);
            ctx.add_obligations(obligations);
            let result = ctx.solve_nested_goals();
            result.is_ok()
        })
    }

    fn select_fn_for_application(
        &mut self,
        candidate: DefinitionID,
        goal: &OverloadGoal<'ctx>,
    ) -> Vec<Obligation<'ctx>> {
        let mut pending = vec![];
        let gcx = self.gcx();
        let signature = gcx.fn_signature(candidate);
        let fn_args = self.icx().fresh_args_for_def(candidate, goal.callee_span);
        let fn_ty = instantiate_ty_with_args(gcx, gcx.type_of(candidate), fn_args);

        let fn_sig_ty =
            instantiate_ty_with_args(gcx, labeled_signature_to_ty(signature, gcx), fn_args);

        // Unify alpha ty with resolved candidate ty
        let alpha = goal.callee_var;
        let obligation = Obligation {
            location: goal.callee_span,
            goal: Goal::Constraint(Constraint::TypeEquality(alpha, fn_ty)),
        };
        pending.push(obligation);

        let (fn_inputs, fn_output) = match fn_sig_ty.kind() {
            TyKind::Function { inputs, output } => (inputs, output),
            _ => unreachable!(),
        };

        for (arg, param) in goal.arguments.iter().zip(fn_inputs) {
            let obligation = Obligation {
                location: arg.span,
                goal: Goal::Coerce {
                    from: arg.ty,
                    to: *param,
                },
            };
            pending.push(obligation);
        }

        // result | return
        let obligation = Obligation {
            location: goal.callee_span,
            goal: Goal::Coerce {
                from: goal.result_var,
                to: fn_output,
            },
        };

        pending.push(obligation);

        // Instantiate Function Predicates
        gcx.canon_predicates_of(candidate)
            .iter()
            .for_each(|spanned| {
                let constraint = instantiate_constraint_with_args(gcx, spanned.value, fn_args);
                pending.push(Obligation {
                    location: goal.callee_span,
                    goal: Goal::Constraint(constraint),
                });
            });

        pending
    }
}

/// Fast syntactic filter.  *No instantiation, no unification.*
fn quick_match<'ctx>(
    candidate: DefinitionID,
    call_arguments: &'ctx [OverloadArgument<'ctx>],
    gcx: GlobalContext<'ctx>,
) -> bool {
    let fn_sig = gcx.fn_signature(candidate);
    let call_arity = call_arguments.len();
    let min_required = fn_sig.min_parameter_count();
    let param_count = fn_sig.inputs.len();
    // ---- arity / defaults / variadic --------------------------------
    if call_arity < min_required {
        return false;
    }
    if call_arity > param_count && !fn_sig.is_variadic {
        return false;
    }

    // Labels
    let upto = call_arity.min(param_count);

    for index in 0..upto {
        let call_label = call_arguments[index].label.map(|f| f.symbol);
        let decl_label = fn_sig.inputs[index].label;
        let decl_defaulted = min_required < param_count && index >= min_required;

        match (decl_label, decl_defaulted, call_label) {
            // ❶ parameter is *unlabelled* in decl
            (None, _, Some(_)) => return false, // label where none exists
            // ❷ parameter has compulsory label
            (Some(_), false, None) => return false, // label missing
            (Some(d), false, Some(c)) if c != d => return false, // wrong label
            // ❸ parameter label is optional (defaulted) – always accept
            _ => {}
        }
    }

    return true;
}
