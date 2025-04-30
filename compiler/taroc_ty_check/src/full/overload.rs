use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionID, Mutability, NodeID, OperatorKind};
use taroc_span::{Span, Spanned, Symbol};
use taroc_ty::{Adjustment, LabeledFunctionSignature, Ty, TyKind};

use crate::{
    models::{SubstitutionMap, TaggedAdjustments, UnificationError},
    utils,
};

use super::{FunctionChecker, solve::SolverError};

struct CandidateEvaluationData<'ctx> {
    pub specificity: usize,
    pub return_ty: Ty<'ctx>,
    pub adjustments: TaggedAdjustments,
}

#[derive(Debug, Clone)]
pub enum CandidateEvaluationError<'ctx> {
    ArityMismatch {
        expected: usize,
        found: usize,
    },
    // TODO: Add ArityMismatchVariadic if needed
    LabelMismatch {
        arg_span: Span, // Span of the argument with the wrong/missing/unexpected label
        param_label: Option<Symbol>, // Expected label (None if positional)
        arg_label: Option<taroc_hir::Label>, // Label found on argument (None if positional)
    },
    MissingArgument {
        call_span: Span, // Span of the function call itself
        param_label: Option<Symbol>,
        param_index: usize,
    },
    TooManyPositionalArgs {
        first_extra_arg_span: Span, // Span of the first argument that couldn't be matched
    },
    ArgumentTypeMismatch {
        // Contains expected, found types
        error_detail: SolverError<'ctx>, // Reusing SolverErrorKind for detail (e.g., TypeMismatch variant)
        arg_span: Span,                  // Span of the specific argument expression that failed
    },
    ReturnTypeMismatch {
        expected: Ty<'ctx>,
        found: Ty<'ctx>, // The candidate's return type (potentially instantiated)
                         // Span would typically be the call site span
    },
    ConstraintFailure {
        // The list of errors from solve_constraints for this candidate
        solver_errors: Vec<Spanned<SolverError<'ctx>>>,
    },
}

pub type CandidateEvaluationResult<'ctx> =
    Result<CandidateEvaluationData<'ctx>, CandidateEvaluationError<'ctx>>;

impl<'ctx> FunctionChecker<'ctx> {
    pub fn resolve_overloads(
        &mut self,
        schemes: &Vec<LabeledFunctionSignature<'ctx>>,
        callsite_arguments: Option<&Vec<taroc_hir::ExpressionArgument>>,
        return_ty: Option<Ty<'ctx>>,
        call_span: Span,
        check_labels: bool,
    ) -> Ty<'ctx> {
        // --- 2. Evaluate all candidates ---
        let mut successes: Vec<(
            CandidateEvaluationData<'ctx>,
            &LabeledFunctionSignature<'ctx>,
        )> = Vec::new();
        // Store EvalError along with the scheme that caused it for better reporting
        let mut failures: Vec<(
            &LabeledFunctionSignature<'ctx>,
            CandidateEvaluationError<'ctx>,
        )> = Vec::new();

        for scheme in schemes {
            // Pass both HIR args (for spans/structure inside evaluator) and synthesized info
            let result = self.evaluate_overload_candidate(
                scheme,
                callsite_arguments,
                return_ty,
                call_span,
                check_labels,
            );

            match result {
                // Include scheme ref in success tuple for ambiguity reporting
                Ok(data) => successes.push((data, scheme)),
                Err(eval_error) => failures.push((scheme, eval_error)),
            }
        }

        // --- 3. Check for resolution failure (no viable candidates) ---
        if successes.is_empty() {
            if schemes.is_empty() {
                self.context.diagnostics.error(
                    "internal error: no candidate functions provided for overload resolution"
                        .to_string(),
                    call_span,
                );
            } else {
                // Use the dedicated helper to report detailed failure reasons
                // self.report_resolution_failure(call_span, &failures);
                todo!("report error")
            }
            return self.error_ty(); // Return error type
        }

        // --- 4. Handle Ambiguity / Pick Best Candidate ---
        // Sort viable candidates by score (lower score is better)
        successes.sort_by_key(|(data, _)| data.specificity);

        // Check for ambiguity: more than one candidate has the *same lowest score*
        if successes.len() > 1 && successes[0].0.specificity == successes[1].0.specificity {
            let best_score = successes[0].0.specificity;
            // Find all candidates tied for the best score
            let ambiguous_candidates: Vec<&LabeledFunctionSignature<'ctx>> = successes
                .iter()
                .take_while(|(data, _)| data.specificity == best_score)
                .map(|(_, scheme)| *scheme) // Extract the scheme
                .collect();

            // Report ambiguity error, listing the tied candidates
            {
                let message = format!("ambiguous use of {}", Symbol::with("KKLJSDLJFSL"));
                self.context.diagnostics.error(message, call_span);
            }

            for ambiguous_scheme in ambiguous_candidates {
                // TODO: report possible candidate
            }
            return self.error_ty();
        }

        // --- 5. Process the single best candidate ---
        // remove(0) is safe due to sorting and ambiguity check
        let (data, scheme) = successes.remove(0);

        // Store the final, merged adjustments determined *during* the winner's evaluation
        // (assuming evaluate_overload_candidate now returns the final merged map)
        for (node_id, adjs) in data.adjustments {
            if !adjs.is_empty() {
                self.context.add_adjustments(adjs, node_id);
            }
        }
        return self.context.type_of(scheme.id);
    }

    fn evaluate_overload_candidate(
        &mut self,
        scheme: &LabeledFunctionSignature<'ctx>,
        callsite_arguments: Option<&Vec<taroc_hir::ExpressionArgument>>,
        expected_return_ty: Option<Ty<'ctx>>,
        call_span: Span, // Overall call span needed for some errors
        check_labels: bool,
    ) -> CandidateEvaluationResult<'ctx> {
        let snapshot = self.context.snapshot(); // For rollback
        let evaluation_result = (|| {
            // Closure for easy error handling + restore

            // --- Argument Synthesis & Matching ---
            let (callsite_args_typed, num_callsite_args) =
                if let Some(args_hir) = callsite_arguments {
                    (self.synthesize_call_arguments(args_hir), args_hir.len())
                } else {
                    (Vec::new(), 0)
                };

            let candidate_params = &scheme.inputs;
            let candidate_return_ty = scheme.output;
            let mut subst = SubstitutionMap::new();

            // Arity Check
            if !scheme.is_variadic && num_callsite_args != candidate_params.len() {
                return Err(CandidateEvaluationError::ArityMismatch {
                    expected: candidate_params.len(),
                    found: num_callsite_args,
                });
            }

            let mut arg_adjustments: FxHashMap<NodeID, Vec<Adjustment>> = FxHashMap::default();
            let mut matched_type_info: Vec<(Ty<'ctx>, Ty<'ctx>, Vec<Adjustment>)> =
                Vec::with_capacity(candidate_params.len());
            let args_hir_iter = callsite_arguments.map_or([].iter(), |v| v.iter());
            let zipped_iter = args_hir_iter
                .zip(&callsite_args_typed)
                .zip(candidate_params);
            let mut param_matched = vec![false; candidate_params.len()]; // Needed for missing arg check

            // Use a variable to track the first extra positional argument span
            let mut first_extra_arg_span: Option<Span> = None;

            for (idx, ((arg_expr, (arg_ty, arg_node_id)), param)) in zipped_iter.enumerate() {
                // Keep track of first potential extra arg span
                if idx >= candidate_params.len() && first_extra_arg_span.is_none() {
                    first_extra_arg_span = Some(arg_expr.span);
                }
                // Check if we are trying to match beyond the number of parameters (needed for variadics later)
                if idx >= candidate_params.len() {
                    // This case should ideally be handled by a more robust arity check or variadic logic
                    // If non-variadic, the initial arity check should have caught this.
                    // If variadic, this argument should match the variadic parameter. Skip for now.
                    continue; // Or handle variadic matching
                }

                param_matched[idx] = true; // Mark param as potentially matched positionally

                // 1. Label Validation
                if check_labels
                    && arg_expr.label.as_ref().map(|f| f.identifier.symbol) != param.label
                {
                    // Return specific error
                    return Err(CandidateEvaluationError::LabelMismatch {
                        arg_span: arg_expr.span,
                        param_label: param.label,
                        arg_label: arg_expr.label.clone(),
                    });
                }

                // 2. Type Checking
                let param_ty = self.instantiate_with_map(param.ty, &mut subst);
                match self.coerce_or_unify(*arg_ty, param_ty) {
                    Ok(adjustments) => {
                        if !adjustments.is_empty() {
                            arg_adjustments
                                .entry(*arg_node_id)
                                .or_default()
                                .extend(adjustments.clone());
                        }
                        matched_type_info.push((*arg_ty, param_ty, adjustments));
                    }
                    Err(unification_error) => {
                        // Convert unification error to SolverError kind
                        let solver_error_kind = match unification_error {
                            UnificationError::TypeMismatch => SolverError::TypeMismatch {
                                expected: param_ty,
                                found: *arg_ty,
                            },
                            UnificationError::OccursCheckFailed => {
                                SolverError::OccursCheck(*arg_ty, param_ty)
                            }
                        };
                        // Return specific error
                        return Err(CandidateEvaluationError::ArgumentTypeMismatch {
                            error_detail: solver_error_kind,
                            arg_span: arg_expr.expression.span, // Span of the expression part
                        });
                    }
                }
            } // End loop

            // --- Post-Loop Checks ---
            // Check for Too Many Positional Arguments (only relevant if previous checks didn't cover it)
            if !scheme.is_variadic && num_callsite_args > candidate_params.len() {
                // Get span of the first extra argument
                let extra_span = callsite_arguments
                    .and_then(|args| args.get(candidate_params.len()))
                    .map(|arg| arg.span)
                    .unwrap_or(call_span); // Fallback span
                return Err(CandidateEvaluationError::TooManyPositionalArgs {
                    first_extra_arg_span: extra_span,
                });
            }

            // Check for Missing Arguments
            for (idx, matched) in param_matched.iter().enumerate() {
                if !*matched {
                    // TODO: Check if candidate_params[idx] has a default value
                    let param = &candidate_params[idx];
                    // Return specific error
                    return Err(CandidateEvaluationError::MissingArgument {
                        call_span,
                        param_label: param.label,
                        param_index: idx,
                    });
                }
            }

            // --- Return Type Check ---
            // TODO: Instantiate final_return_ty
            let final_return_ty = self.instantiate_with_map(candidate_return_ty, &mut subst);
            if let Some(expected_ret_ty) = expected_return_ty {
                match self.coerce_or_unify(final_return_ty, expected_ret_ty) {
                    Ok(_) => {}
                    Err(_) => {
                        // Return specific error
                        return Err(CandidateEvaluationError::ReturnTypeMismatch {
                            expected: expected_ret_ty,
                            found: final_return_ty,
                        });
                    }
                }
            }

            // --- Constraint Solving ---
            let solve_result = self.solve_constraints();

            let constraint_adjustments = match solve_result {
                Ok(adjustments_from_solve) => adjustments_from_solve,
                Err(solver_errors) => {
                    // Constraint solving failed. Return specific error.
                    return Err(CandidateEvaluationError::ConstraintFailure { solver_errors });
                }
            };

            // --- Merge Adjustments ---
            let mut final_adjustments = arg_adjustments;
            for (node_id, adjs_from_constraints) in constraint_adjustments {
                if !adjs_from_constraints.is_empty() {
                    final_adjustments
                        .entry(node_id)
                        .or_default()
                        .extend(adjs_from_constraints);
                }
            }

            // --- Specificity Ranking ---
            let score = self.rank_specificity(&matched_type_info, final_return_ty);

            // --- Success ---
            Ok((score, final_return_ty, final_adjustments)) // Return Ok tuple
        })(); // End of closure

        // --- Restore Context State ---
        self.context.restore(snapshot);
        println!("Done Candidate");

        // Return the result (Ok or Err) from the closure
        let (specificity, return_ty, adjustments) = evaluation_result?;
        Ok(CandidateEvaluationData {
            specificity,
            return_ty,
            adjustments,
        })
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    /// Compute a specificity score:
    ///  - exact matches              → +0
    ///  - generic binds (type var)   → +1
    ///  - boxing to existential      → +3
    ///  - other conversions (e.g. numeric widens) → +4
    ///
    /// Lower total score = more specific candidate.
    pub fn rank_specificity(
        &self,
        // Represents the matched pairs: (ArgType, ParamType from signature, Adjustments applied to Arg)
        matched_pairs: &[(Ty<'ctx>, Ty<'ctx>, Vec<Adjustment>)],
        // Candidate's return type (currently unused in scoring, but could be added)
        _ret_ty: Ty<'ctx>,
    ) -> usize {
        let mut total_score = 0;

        for (arg_ty, param_ty, adjustments) in matched_pairs {
            if !adjustments.is_empty() {
                // Score based on the first/primary adjustment applied.
                // This assumes the Vec<Adjustment> represents a single logical conversion path.
                match adjustments.first() {
                    Some(Adjustment::AutoRef | Adjustment::AutoMutRef) => {
                        total_score += 2;
                    }
                    Some(
                        Adjustment::MutRefConstCast
                        | Adjustment::MutPtrConstCast
                        | Adjustment::WrapOptional
                        | Adjustment::WrapNilToOptionalNone,
                    ) => {
                        total_score += 3;
                    }
                    // AutoDeref is less common *as an adjustment recorded here* for function args,
                    // but if it were possible via some implicit trait call:
                    Some(Adjustment::AutoDeref) => {
                        total_score += 3;
                    }
                    // Add cases for other adjustments like numeric coercions if they exist
                    // Some(Adjustment::NumericCoercion) => { total_score += 4; }
                    _ => {
                        // Default penalty for any other adjustment/coercion
                        total_score += 4;
                    }
                }
            } else {
                // No adjustments applied. Either exact match or unification succeeded.
                // We need to distinguish. The types provided are likely the state *before*
                // unification resolved inference variables within them.
                // A simple equality check might work for non-generic cases.
                // If types are equal *and* neither contained inference variables originally, it's +0.
                // If types were not equal OR contained inference vars but unified, it's +1.
                // This distinction is hard without more context from the unification process.
                // Let's use a simplified check:
                if arg_ty == param_ty {
                    // Assume this checks for structural equality *before* potential
                    // inference variable binding resolved them.
                    // This is only a true "exact match" if neither contained unbound vars.
                    total_score += 0; // Score for exact match
                } else {
                    // Types were not strictly equal, but unified successfully without adjustments.
                    // This implies generic parameter binding or inference variable unification.
                    total_score += 1; // Score for generic bind / unification match
                }
            }
        }

        total_score
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    pub fn resolve_operator_overload(
        &mut self,
        id: Option<DefinitionID>,
        op: OperatorKind,
        args: Option<&Vec<taroc_hir::ExpressionArgument>>,
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        match id {
            Some(id) => {
                self.resolve_known_definition_operator_overload(id, op, args, expectation, span)
            }
            _ => todo!("operator overload on complex ty"),
        }
    }

    fn resolve_known_definition_operator_overload(
        &mut self,
        id: DefinitionID,
        op: OperatorKind,
        args: Option<&Vec<taroc_hir::ExpressionArgument>>,
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        let functions = self.context.with_type_database(id.package(), |db| {
            db.def_to_functions
                .entry(id)
                .or_insert(Default::default())
                .clone()
        });

        let functions = functions.borrow();
        let functions = functions.operators.get(&op);

        let Some(functions) = functions else {
            let message = format!(
                "operator {op:?} not implemented on type {}",
                self.context.def_symbol(id)
            );
            self.context.diagnostics.error(message, span);
            return self.error_ty();
        };

        let ty = self.resolve_overloads(functions, args, expectation, span, false);
        return ty;
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    pub fn resolve_constructor(&mut self, id: DefinitionID) -> Ty<'ctx> {
        let functions = self.context.with_type_database(id.package(), |db| {
            db.def_to_functions
                .entry(id)
                .or_insert(Default::default())
                .clone()
        });

        let functions = functions.borrow();
        let candidates: Vec<_> = functions
            .constructors
            .iter()
            .clone()
            .map(|v| v.id)
            .collect();

        let kind =
            TyKind::OverloadedFn(self.context.store.interners.intern_slice(&candidates), None);
        return self.mk_ty(kind);
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    pub fn resolve_known_method_call(
        &mut self,
        receiver_node_id: NodeID,
        receiver_def_id: DefinitionID,
        receiver_ty: Ty<'ctx>, // Added: The actual type of the receiver expression
        method_segment: &taroc_hir::PathSegment,
        explicit_arg_tys: &[Ty<'ctx>], // Explicit arguments only
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        let name = method_segment.identifier.symbol;
        let functions = self
            .context
            .with_type_database(receiver_def_id.package(), |db| {
                db.def_to_functions
                    .entry(receiver_def_id)
                    .or_insert(Default::default())
                    .clone()
            });

        let functions = functions.borrow();
        let functions = functions.methods.get(&name);

        let Some(candidates) = functions else {
            let message = format!("no method named {}", name);
            self.context
                .diagnostics
                .error(message, method_segment.identifier.span);
            return self.error_ty();
        };

        // --- Resolve Using Method-Specific Logic ---
        // Pass receiver type and explicit args separately
        self.resolve_method_overloads(
            &candidates,
            receiver_ty,
            receiver_node_id,
            explicit_arg_tys,
            expectation,
            name,
            span,
        )
    }

    /// Resolves method overloading, handling `self`, `&self`, `&mut self` receivers.
    fn resolve_method_overloads(
        &mut self,
        schemes: &Vec<LabeledFunctionSignature<'ctx>>,
        receiver_ty: Ty<'ctx>,
        reciever_id: NodeID,
        explicit_arg_tys: &[Ty<'ctx>],
        return_ty_expectation: Option<Ty<'ctx>>,
        method_name: Symbol,
        span: Span,
    ) -> Ty<'ctx> {
        let mut candidates = vec![];
        const LIMIT: usize = 128;

        for scheme in schemes.iter().take(LIMIT) {
            // Use a sandbox for constraints generated during this candidate check
            let constraints_snapshot = self.context.take_constraints();

            let result = self.evaluate_method_candidate(
                scheme,
                receiver_ty,
                explicit_arg_tys,
                return_ty_expectation,
            );

            // Restore constraints regardless of success/failure
            self.context.set_constraints(constraints_snapshot);

            if let Some(viable_candidate) = result {
                candidates.push(viable_candidate);
            }
        }

        // --- Pick the best candidate ---
        // TODO: Refine sorting/ambiguity check if needed
        candidates.sort_by_key(|(score, _, _)| *score);

        if candidates.is_empty() {
            // TODO: Improve this error message - perhaps list candidates considered and why they failed?
            let message = format!(
                "no matching method overload for '{}' found with receiver type '{}' and argument types ({})",
                method_name, // Use actual method name if available
                receiver_ty,
                explicit_arg_tys
                    .iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            self.context.diagnostics.error(message, span);
            return self.error_ty();
        }

        if candidates.len() > 1 && candidates[0].0 == candidates[1].0 {
            let method_name = schemes
                .first()
                .map(|s| self.context.def_symbol(s.id))
                .unwrap_or_else(|| Symbol::intern("?"));
            let message = format!(
                "ambiguous method call for '{}': multiple candidates match equally well",
                method_name // Use actual method name
            );
            // TODO: List ambiguous candidates
            self.context.diagnostics.error(message, span);
            return self.error_ty();
        }

        // Success!
        let (_score, ret_ty, adjustements) = candidates.remove(0);
        self.context.add_adjustments(adjustements, reciever_id);
        ret_ty
    }

    /// Evaluates a single method candidate against the receiver and arguments.
    /// Returns (score, return_type, adjustments) if viable.
    fn evaluate_method_candidate(
        &mut self,
        scheme: &LabeledFunctionSignature<'ctx>,
        receiver_ty: Ty<'ctx>,
        explicit_arg_tys: &[Ty<'ctx>],
        return_ty_expectation: Option<Ty<'ctx>>,
    ) -> Option<(usize, Ty<'ctx>, Vec<Adjustment>)> {
        // Added Adjustments Vec

        // 1. Instantiate the signature (replaces generics with InferTy variables)
        let signature = utils::convert_labeled_signature_to_signature(&scheme, *self.context);
        let signature = self.instantiate(signature);
        let (candidate_parameter_tys, candidate_return_ty) = match signature.kind() {
            // Expecting fn(SelfParam, ExplicitParam1, ...) -> Ret
            TyKind::Function { inputs, output, .. } => (inputs, output),
            _ => unreachable!("method signature must be a function type after instantiation"),
        };

        // 2. Check Arity (must have at least 1 param for receiver, plus explicit args)
        if candidate_parameter_tys.len() != explicit_arg_tys.len() + 1 {
            //println!("Arity mismatch: Candidate {} params, Explicit {} args", candidate_parameter_tys.len(), explicit_arg_tys.len());
            return None; // Arity mismatch (receiver + explicit args vs candidate params)
        }

        let self_param_ty = candidate_parameter_tys[0];
        let candidate_explicit_param_tys = &candidate_parameter_tys[1..];

        let mut adjustments = Vec::new(); // Collect adjustments here
        let mut score = 0;

        // --- 3. Check Receiver Type ---
        // This is the core difference: match receiver_ty against self_param_ty with auto-ref/deref.
        // We check if receiver_ty *can be coerced or unified* with self_param_ty, potentially
        // applying auto-(mut)-ref.
        let receiver_match_result = self.try_match_receiver(receiver_ty, self_param_ty);

        let Ok((receiver_score, receiver_adjustment)) = receiver_match_result else {
            //println!("Receiver mismatch: Receiver {}, Expected Self {}", receiver_ty, self_param_ty);
            return None; // Receiver doesn't match required self type
        };
        score += receiver_score;
        if let Some(adj) = receiver_adjustment {
            adjustments.push(adj); // TODO: Store adjustment properly keyed to receiver expr
        }

        // --- 4. Check Explicit Argument Types ---
        for (_, (&candidate_param, &provided_arg)) in candidate_explicit_param_tys
            .iter()
            .zip(explicit_arg_tys.iter())
            .enumerate()
        {
            // Use coerce_or_unify for explicit args
            // We need the NodeID of the argument expression here ideally
            let arg_node_id = NodeID::from_usize(0); // Placeholder! Pass real ID down
            match self.try_coerce_or_unify_with_score(arg_node_id, provided_arg, candidate_param) {
                Ok((arg_score, arg_adjustment)) => {
                    score += arg_score;
                    if let Some(adj) = arg_adjustment {
                        adjustments.push(adj); // TODO: Store adjustment keyed to specific arg expr
                    }
                }
                Err(_) => {
                    //println!("Arg {} mismatch: Provided {}, Expected {}", i, provided_arg, candidate_param);
                    return None; // Argument type mismatch
                }
            }
        }

        // --- 5. Check Return Type ---
        if let Some(expected_ret_ty) = return_ty_expectation {
            // Use coerce_or_unify for return type check
            let ret_node_id = NodeID::from_usize(0); // Placeholder! Use call expr span/id
            match self.try_coerce_or_unify_with_score(
                ret_node_id,
                candidate_return_ty,
                expected_ret_ty,
            ) {
                Ok((ret_score, ret_adjustment)) => {
                    score += ret_score; // Add score for return type coercion? Maybe not.
                    if let Some(_) = ret_adjustment {
                        // TODO
                        // Adjustments on the *result* of the call are less common to track this way
                        // adjustments.push(adj);
                    }
                }
                Err(_) => {
                    //println!("Return mismatch: Actual {}, Expected {}", candidate_return_ty, expected_ret_ty);
                    return None; // Return type mismatch
                }
            }
        }

        // --- 6. Solve Constraints ---
        // Constraints might have been generated during unification steps above.
        // TODO: This needs to handle potential failures from constraint solving!
        self.solve_constraints(); // Assume this reports errors via diagnostics if it fails hard

        // TODO: Check if any errors were reported by solve_constraints?

        // If we got here, the candidate is viable
        Some((score, candidate_return_ty, adjustments))
    }

    /// Tries to match the receiver type against the expected self parameter type,
    /// considering auto-ref/deref rules. Returns (score, Option<Adjustment>) on success.
    fn try_match_receiver(
        &mut self,
        receiver_ty: Ty<'ctx>,
        self_param_ty: Ty<'ctx>,
    ) -> Result<(usize, Option<Adjustment>), UnificationError> {
        // Most exact match: Unify directly
        if self.unify(receiver_ty, self_param_ty).is_ok() {
            return Ok((0, None)); // Exact match or unification works
        }

        // Try matching &self
        if let TyKind::Reference(self_inner_ty, Mutability::Immutable) = self_param_ty.kind() {
            // Try auto-ref: Can receiver_ty unify with self_inner_ty?
            if self.unify(receiver_ty, self_inner_ty).is_ok() {
                // Check if receiver is addressable, etc. (might be implicit for now)
                return Ok((1, Some(Adjustment::AutoRef))); // Matched via &
            }
            // TODO: Add check for auto-deref then ref? &self method
        }

        // Try matching &mut self
        if let TyKind::Reference(self_inner_ty, Mutability::Mutable) = self_param_ty.kind() {
            // Try auto-mut-ref: Can receiver_ty unify with self_inner_ty?
            if self.unify(receiver_ty, self_inner_ty).is_ok() {
                // !!! Crucially, we also need to check if the original receiver expression
                // !!! corresponds to a mutable place. This check needs context beyond types.
                // For now, we assume it's possible if types unify.
                return Ok((1, Some(Adjustment::AutoMutRef))); // Matched via &mut
            }
            // TODO: Add check for auto-deref then mut ref?
        }

        // TODO: Try matching `self` by value via auto-deref?
        // if let TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) = receiver_ty.kind() {
        //     // If self_param_ty isn't a ref/ptr, try unifying self_param_ty with inner
        //     if !matches!(self_param_ty.kind(), TyKind::Reference(..) | TyKind::Pointer(..)) {
        //          if self.unify(inner, self_param_ty).is_ok() {
        //              // Requires Deref/DerefMut trait typically
        //              return Ok((2, Some(Adjustment::AutoDeref)));
        //          }
        //     }
        // }

        // If none of the above worked
        Err(UnificationError::TypeMismatch)
    }

    /// Like coerce_or_unify, but returns a score and adjustment info.
    /// Placeholder NodeID needed.
    fn try_coerce_or_unify_with_score(
        &mut self,
        node: NodeID, // Placeholder node ID
        provided: Ty<'ctx>,
        expected: Ty<'ctx>,
    ) -> Result<(usize, Option<Adjustment>), UnificationError> {
        // Try exact match / unification first
        if self.unify(provided, expected).is_ok() {
            return Ok((0, None)); // Score 0 for exact match/unification
        }

        // Then try coercions (add score > 0 for coercions)
        match self.try_coerce(provided, expected) {
            // Assuming try_coerce returns Result<Option<Coercion>, UnificationError>
            Ok(Some(coercion)) => {
                // Assign a score based on the *kind* of coercion if needed, otherwise a flat score.
                let score = match coercion.adjustments.first() {
                    // Simple heuristic
                    Some(Adjustment::MutRefConstCast | Adjustment::MutPtrConstCast) => 3,
                    Some(Adjustment::WrapNilToOptionalNone | Adjustment::WrapOptional) => 2,
                    _ => 4, // Other coercions
                };
                // Return only the *first* adjustment for simplicity here?
                // A single coercion might involve multiple steps in Adjustment enum later.
                Ok((score, coercion.adjustments.into_iter().next()))
            }
            Ok(None) => Err(UnificationError::TypeMismatch), // No coercion applied, and unify failed
            Err(e) => Err(e), // Coercion attempt itself failed unification internally
        }
    }
}
