use super::{
    BindInterfaceMethodGoalData, BindMethodOverloadGoalData, ConstraintSolver, Goal,
    InterfaceCallInfo, MethodCallData, Obligation, SolverResult,
};
use crate::{
    hir::Mutability,
    sema::{
        error::TypeError,
        models::{
            AliasKind, GenericArgument, GenericArguments, InterfaceReference,
            LabeledFunctionSignature, Ty, TyKind,
        },
        resolve::models::DefinitionID,
        tycheck::{
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, BindOverloadGoalData, DisjunctionBranch,
            },
            utils::{AutoReference, instantiate::instantiate_ty_with_args},
        },
    },
    span::{Span, Spanned, Symbol},
};
use rustc_hash::FxHashSet;

struct InterfaceMethodCandidate<'ctx> {
    call_info: InterfaceCallInfo,
    candidate_ty: Ty<'ctx>,
    instantiation_args: Option<GenericArguments<'ctx>>,
    source: DefinitionID,
}

/// A method candidate with its associated receiver type and adjustments.
struct MethodCandidate<'ctx> {
    def_id: DefinitionID,
    receiver_ty: Ty<'ctx>,
    /// Cost of auto-reference: None=0, Immutable=1, Mutable=2
    autoref_cost: u8,
    matches_expectation: bool,
    output_ref_mutability: Option<Mutability>,
    deref_steps: usize,
}

impl<'ctx> ConstraintSolver<'ctx> {
    fn build_adjustments(deref_steps: usize, autoref_cost: u8) -> Vec<Adjustment<'ctx>> {
        let mut adjustments = Vec::with_capacity(deref_steps + usize::from(autoref_cost > 0));
        adjustments.extend((0..deref_steps).map(|_| Adjustment::Dereference));
        match autoref_cost {
            1 => adjustments.push(Adjustment::BorrowImmutable),
            2 => adjustments.push(Adjustment::BorrowMutable),
            _ => {}
        }
        adjustments
    }

    #[inline]
    fn with_receiver_argument(
        arguments: &[ApplyArgument<'ctx>],
        receiver: ApplyArgument<'ctx>,
    ) -> Vec<ApplyArgument<'ctx>> {
        let mut out = Vec::with_capacity(arguments.len() + 1);
        out.push(receiver);
        out.extend_from_slice(arguments);
        out
    }

    pub fn solve_method_call(&mut self, data: MethodCallData<'ctx>) -> SolverResult<'ctx> {
        let MethodCallData {
            node_id,
            receiver,
            reciever_node,
            reciever_span,
            is_unsafe_context,
            name,
            arguments,
            result,
            span,
            method_ty,
            expect_ty,
            ..
        } = &data;

        let resolved_receiver = self.structurally_resolve(*receiver);
        if resolved_receiver.is_error() {
            let obligation = Obligation {
                location: data.span,
                goal: Goal::Equal(data.result, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

        let has_unresolved_expectation = match data.expect_ty {
            None => true,
            Some(expect) => {
                let expect = self.structurally_resolve(expect);
                expect.is_infer() || expect.contains_inference()
            }
        };
        let receiver_is_mut_ref = matches!(
            resolved_receiver.kind(),
            TyKind::Reference(_, Mutability::Mutable)
        );
        let needs_output_ref_mutability = has_unresolved_expectation && receiver_is_mut_ref;
        let expect_requires_mut_ref_output = matches!(
            data.expect_ty.map(|expect| expect.kind()),
            Some(TyKind::Reference(_, Mutability::Mutable))
        );
        let must_read_signature = needs_output_ref_mutability || expect_requires_mut_ref_output;
        let mut signature_output_cache: Vec<(DefinitionID, Option<Mutability>)> = Vec::new();
        if must_read_signature {
            signature_output_cache.reserve(8);
        }

        let rec_candidates = self.reciever_candidates(*receiver);
        // Collect ALL candidates from ALL auto-reference modes.
        let mut all_candidates: Vec<MethodCandidate<'ctx>> =
            Vec::with_capacity(rec_candidates.len() * 3);
        for (candidate_ty, deref_steps) in rec_candidates {
            let candidate_ty = self.structurally_resolve(candidate_ty);
            for r in [
                AutoReference::None,
                AutoReference::Immutable,
                AutoReference::Mutable,
            ] {
                let receiver_ty = match r {
                    AutoReference::None => candidate_ty,
                    AutoReference::Mutable => Ty::new(
                        TyKind::Reference(candidate_ty, Mutability::Mutable),
                        self.gcx(),
                    ),
                    AutoReference::Immutable => Ty::new(
                        TyKind::Reference(candidate_ty, Mutability::Immutable),
                        self.gcx(),
                    ),
                };
                let autoref_cost = match r {
                    AutoReference::None => 0,
                    AutoReference::Immutable => 1,
                    AutoReference::Mutable => 2,
                };

                // Handle interface method calls on abstract receivers:
                // - generic type parameters
                // - associated type projections (e.g., `T.Iterator`)
                if matches!(
                    candidate_ty.kind(),
                    TyKind::Parameter(_)
                        | TyKind::Alias {
                            kind: AliasKind::Projection,
                            ..
                        }
                ) {
                    let bounds = self.bounds_for_type_in_scope(candidate_ty);
                    if !bounds.is_empty() {
                        let list = self.gcx().store.arenas.global.alloc_slice_clone(&bounds);
                        if let Some(result) = self.solve_interface_method_call(
                            &data,
                            candidate_ty,
                            receiver_ty,
                            list,
                            deref_steps,
                            autoref_cost,
                        ) {
                            return result;
                        }
                    }
                }

                // Handle interface method calls on boxed existentials
                if let TyKind::BoxedExistential { interfaces } = candidate_ty.kind() {
                    if let Some(result) = self.solve_interface_method_call(
                        &data,
                        candidate_ty,
                        receiver_ty,
                        interfaces,
                        deref_steps,
                        autoref_cost,
                    ) {
                        return result;
                    }
                }

                // Look up instance method candidates
                let candidates = self.lookup_instance_candidates_method(
                    candidate_ty,
                    receiver_ty,
                    name.symbol,
                    *span,
                );
                let candidates = candidates.unwrap_or_default();

                if candidates.is_empty() {
                    // Concrete types may satisfy interface requirements via conformance,
                    // including default interface methods with no concrete impl body.
                    if let Some(interfaces) = self.concrete_interface_roots(candidate_ty, *span) {
                        if let Some(result) = self.solve_interface_method_call(
                            &data,
                            candidate_ty,
                            receiver_ty,
                            interfaces,
                            deref_steps,
                            autoref_cost,
                        ) {
                            return result;
                        }
                    }

                    continue;
                }

                // Add all candidates with their receiver info
                for def_id in candidates {
                    let output_ref_mutability = if must_read_signature {
                        if let Some((_, cached)) = signature_output_cache
                            .iter()
                            .find(|(cached_id, _)| *cached_id == def_id)
                        {
                            *cached
                        } else {
                            let signature = self.gcx().get_signature(def_id);
                            let output_ref_mutability = match signature.output.kind() {
                                TyKind::Reference(_, mutability) => Some(mutability),
                                _ => None,
                            };
                            signature_output_cache.push((def_id, output_ref_mutability));
                            output_ref_mutability
                        }
                    } else {
                        None
                    };
                    let matches_expectation = !expect_requires_mut_ref_output
                        || output_ref_mutability != Some(Mutability::Immutable);

                    all_candidates.push(MethodCandidate {
                        def_id,
                        receiver_ty,
                        autoref_cost,
                        matches_expectation,
                        output_ref_mutability,
                        deref_steps,
                    });
                }
            }
        }

        // If no expected type is available yet and this call has both mutable- and
        // immutable-reference return candidates, prefer mutable-reference variants.
        //
        // This prevents early commitment to immutable overloads in contexts where
        // downstream constraints later require `&mut`.
        if has_unresolved_expectation && receiver_is_mut_ref {
            let has_mut_ref_output = all_candidates
                .iter()
                .any(|candidate| candidate.output_ref_mutability == Some(Mutability::Mutable));
            let has_imm_ref_output = all_candidates
                .iter()
                .any(|candidate| candidate.output_ref_mutability == Some(Mutability::Immutable));

            if has_mut_ref_output && has_imm_ref_output {
                for candidate in &mut all_candidates {
                    if candidate.output_ref_mutability == Some(Mutability::Immutable) {
                        candidate.matches_expectation = false;
                    }
                }
            }
        }

        // If we found any candidates, create a disjunction
        if !all_candidates.is_empty() {
            // Check if all candidates have the same receiver type
            // If so, we can use the simpler approach with a fixed receiver type
            let first_receiver_ty = all_candidates[0].receiver_ty;
            let all_same_receiver = all_candidates
                .iter()
                .all(|c| c.receiver_ty == first_receiver_ty);

            if all_same_receiver {
                // Simple case: all candidates use the same receiver type
                // Use the original approach with BindOverload (not BindMethodOverload)
                // and record adjustments immediately
                let first_adjustments = Self::build_adjustments(
                    all_candidates[0].deref_steps,
                    all_candidates[0].autoref_cost,
                );

                let mut branches = Vec::with_capacity(all_candidates.len());
                for candidate in &all_candidates {
                    let branch = DisjunctionBranch {
                        goal: Goal::BindOverload(BindOverloadGoalData {
                            node_id: *node_id,
                            var_ty: *method_ty,
                            candidate_ty: self.gcx().get_type(candidate.def_id),
                            source: candidate.def_id,
                            instantiation_args: None,
                        }),
                        source: Some(candidate.def_id),
                        autoref_cost: candidate.autoref_cost,
                        matches_expectation: candidate.matches_expectation,
                        deref_steps: candidate.deref_steps,
                    };
                    branches.push(branch);
                }

                let disjunction_goal = Obligation {
                    location: name.span,
                    goal: Goal::Disjunction(branches),
                };

                let args = Self::with_receiver_argument(
                    arguments,
                    ApplyArgument {
                        id: *reciever_node,
                        label: None,
                        ty: first_receiver_ty,
                        span: *reciever_span,
                    },
                );

                let apply_goal = Obligation {
                    location: *span,
                    goal: Goal::Apply(ApplyGoalData {
                        call_node_id: *node_id,
                        call_span: *span,
                        callee_ty: *method_ty,
                        callee_source: None,
                        is_unsafe_context: *is_unsafe_context,
                        result_ty: *result,
                        _expect_ty: *expect_ty,
                        arguments: args,
                        skip_labels: false,
                    }),
                };

                self.record_adjustments(*reciever_node, first_adjustments);
                return SolverResult::Solved(vec![disjunction_goal, apply_goal]);
            } else {
                // Complex case: candidates have different receiver types (different autoref modes)
                // Use BindMethodOverload which bundles adjustments with each candidate

                // Create a fresh type variable for the receiver that will be constrained
                // by the selected BindMethodOverload branch.
                let receiver_ty_var = self.icx.next_ty_var(*reciever_span);

                let mut branches = Vec::with_capacity(all_candidates.len());
                for candidate in &all_candidates {
                    let branch = DisjunctionBranch {
                        goal: Goal::BindMethodOverload(BindMethodOverloadGoalData {
                            node_id: *node_id,
                            receiver_node_id: *reciever_node,
                            var_ty: *method_ty,
                            candidate_ty: self.gcx().get_type(candidate.def_id),
                            receiver_ty: candidate.receiver_ty,
                            receiver_ty_var, // Pass the type variable to be constrained
                            source: candidate.def_id,
                            instantiation_args: None,
                            adjustments: Self::build_adjustments(
                                candidate.deref_steps,
                                candidate.autoref_cost,
                            ),
                        }),
                        source: Some(candidate.def_id),
                        autoref_cost: candidate.autoref_cost,
                        matches_expectation: candidate.matches_expectation,
                        deref_steps: candidate.deref_steps,
                    };
                    branches.push(branch);
                }

                let disjunction_goal = Obligation {
                    location: name.span,
                    goal: Goal::Disjunction(branches),
                };

                // Build the Apply goal using the receiver type variable
                let args = Self::with_receiver_argument(
                    arguments,
                    ApplyArgument {
                        id: *reciever_node,
                        label: None,
                        ty: receiver_ty_var,
                        span: *reciever_span,
                    },
                );

                let apply_goal = Obligation {
                    location: *span,
                    goal: Goal::Apply(ApplyGoalData {
                        call_node_id: *node_id,
                        call_span: *span,
                        callee_ty: *method_ty,
                        callee_source: None,
                        is_unsafe_context: *is_unsafe_context,
                        result_ty: *result,
                        _expect_ty: *expect_ty,
                        arguments: args,
                        skip_labels: false,
                    }),
                };

                // Note: We do NOT record adjustments here!
                // The BindMethodOverload goal will record the correct adjustments
                // when the disjunction selects a branch.
                return SolverResult::Solved(vec![disjunction_goal, apply_goal]);
            }
        }

        // ── Callable field fallback ──────────────────────────────────
        // If no method named `f` was found, check if `f` is a struct field
        // whose type is callable (e.g., `F: FnMut[T, T]`).
        // Resolve `self.f(args)` as `(self.f)(args)`.
        {
            let mut adjustments = Vec::new();
            let mut prev: Option<Ty<'ctx>> = None;
            for ty in self.autoderef(*receiver) {
                let ty = self.structurally_resolve(ty);
                if prev.is_some() {
                    adjustments.push(Adjustment::Dereference);
                }
                prev = Some(ty);

                if let Some((field, index)) = self.lookup_field(ty, name.symbol) {
                    if !self
                        .gcx()
                        .is_visibility_allowed(field.visibility, self.current_def)
                    {
                        // Field exists but is not visible; fall through to error.
                        break;
                    }

                    // Record field index and receiver adjustments.
                    self.record_adjustments(*reciever_node, adjustments);
                    self.record_field_index(*node_id, index);

                    // Create a Member goal: resolves `self.f` to the field type.
                    let field_ty = field.ty;

                    // Create an Apply goal: calls the field value with the arguments.
                    let apply_goal = Obligation {
                        location: *span,
                        goal: Goal::Apply(ApplyGoalData {
                            call_node_id: *node_id,
                            call_span: *span,
                            callee_ty: field_ty,
                            callee_source: None,
                            is_unsafe_context: *is_unsafe_context,
                            result_ty: *result,
                            _expect_ty: *expect_ty,
                            arguments: arguments.clone(),
                            skip_labels: false,
                        }),
                    };

                    // Equate method_ty with the field type so downstream sees the right type.
                    let eq_goal = Obligation {
                        location: name.span,
                        goal: Goal::Equal(*method_ty, field_ty),
                    };

                    return SolverResult::Solved(vec![eq_goal, apply_goal]);
                }
            }
        }

        let final_on = self.structurally_resolve(*receiver);
        if final_on.contains_inference() {
            return SolverResult::Deferred;
        }

        return SolverResult::Error(vec![Spanned::new(
            TypeError::NoSuchMember {
                name: name.symbol,
                on: final_on,
            },
            name.span,
        )]);
    }

    fn reciever_candidates(&self, base_ty: Ty<'ctx>) -> Vec<(Ty<'ctx>, usize)> {
        let mut base = Vec::with_capacity(4);
        let mut derefs = 0;

        let mut autoderef = self.autoderef(base_ty);
        while let Some(nx) = autoderef.next() {
            base.push((nx, derefs));
            derefs += 1;
        }

        base
    }

    pub fn lookup_instance_candidates_method(
        &self,
        candidate: Ty<'ctx>,
        reciever: Ty<'ctx>,
        name: Symbol,
        span: Span,
    ) -> Option<Vec<DefinitionID>> {
        let head = self.type_head_from_type(candidate)?;
        let all_candidates = self.lookup_instance_candidates_visible(head, name);
        if all_candidates.is_empty() {
            return None;
        }

        let mut matching = Vec::with_capacity(all_candidates.len());
        for candidate in all_candidates.into_iter() {
            let ty = self.gcx().get_type(candidate);
            let fn_reciever = match ty.kind() {
                TyKind::FnPointer { inputs, .. } => inputs.first().cloned(),
                _ => None,
            };

            let Some(fn_reciever) = fn_reciever else {
                continue;
            };

            let reciever_head = self.type_head_from_type(reciever);
            let fn_reciever_head = self.type_head_from_type(fn_reciever);

            let matches = match (reciever_head, fn_reciever_head) {
                (Some(a), Some(b)) => a == b,
                _ => reciever == fn_reciever,
            };

            if matches {
                matching.push(candidate);
            }
        }

        self.filter_extension_candidates_in_place(&mut matching, candidate, span);
        return Some(matching);
    }

    fn concrete_interface_roots(
        &self,
        self_ty: Ty<'ctx>,
        span: Span,
    ) -> Option<&'ctx [InterfaceReference<'ctx>]> {
        let head = self.type_head_from_type(self_ty)?;
        let records = self.gcx().collect_from_databases(|db| {
            db.conformance_by_head
                .get(&head)
                .map_or_else(Vec::new, |ids| {
                    ids.iter()
                        .filter_map(|id| db.conformance_records.get(id).copied())
                        .collect()
                })
        });
        if records.is_empty() {
            return None;
        }

        let mut interfaces = Vec::with_capacity(records.len());
        let mut seen: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();
        seen.reserve(records.len());

        for record in records {
            if !self.visible_traits.is_empty()
                && !self.visible_traits.contains(&record.interface.id)
            {
                continue;
            }

            if !self.extension_target_matches(record.extension, self_ty, span) {
                continue;
            }
            let iface = InterfaceReference {
                id: record.interface.id,
                arguments: self.interface_args_with_self(record.interface, self_ty),
                bindings: record.interface.bindings,
            };
            if seen.insert(iface) {
                interfaces.push(iface);
            }
        }

        if interfaces.is_empty() {
            return None;
        }

        Some(
            self.gcx()
                .store
                .arenas
                .global
                .alloc_slice_clone(&interfaces),
        )
    }

    fn solve_interface_method_call(
        &mut self,
        data: &MethodCallData<'ctx>,
        candidate_ty: Ty<'ctx>,
        reciever_ty: Ty<'ctx>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
        deref_steps: usize,
        autoref_cost: u8,
    ) -> Option<SolverResult<'ctx>> {
        let (candidates, object_safety_violation) = self.interface_method_candidates(
            candidate_ty,
            reciever_ty,
            interfaces,
            data.name.symbol,
            data.name.span,
        );
        if candidates.is_empty() {
            if object_safety_violation {
                let error = Spanned::new(
                    TypeError::NoSuchMember {
                        name: data.name.symbol,
                        on: candidate_ty,
                    },
                    data.name.span,
                );
                return Some(SolverResult::Error(vec![error]));
            }
            return None;
        }

        let mut branches = Vec::with_capacity(candidates.len());
        for candidate in candidates {
            branches.push(DisjunctionBranch {
                goal: Goal::BindInterfaceMethod(BindInterfaceMethodGoalData {
                    node_id: data.node_id,
                    var_ty: data.method_ty,
                    candidate_ty: candidate.candidate_ty,
                    call_info: candidate.call_info,
                    instantiation_args: candidate.instantiation_args,
                }),
                source: Some(candidate.source),
                autoref_cost: 0, // Interface method calls don't have autoref ambiguity
                matches_expectation: false,
                deref_steps: 0,
            });
        }

        let disjunction_goal = Obligation {
            location: data.name.span,
            goal: Goal::Disjunction(branches),
        };

        let args = Self::with_receiver_argument(
            &data.arguments,
            ApplyArgument {
                id: data.reciever_node,
                label: None,
                ty: reciever_ty,
                span: data.reciever_span,
            },
        );

        let apply_goal = Obligation {
            location: data.span,
            goal: Goal::Apply(ApplyGoalData {
                call_node_id: data.node_id,
                call_span: data.span,
                callee_ty: data.method_ty,
                callee_source: None,
                is_unsafe_context: data.is_unsafe_context,
                result_ty: data.result,
                _expect_ty: data.expect_ty,
                arguments: args,
                skip_labels: false,
            }),
        };

        self.record_adjustments(
            data.reciever_node,
            Self::build_adjustments(deref_steps, autoref_cost),
        );
        Some(SolverResult::Solved(vec![disjunction_goal, apply_goal]))
    }

    fn interface_method_candidates(
        &mut self,
        self_ty: Ty<'ctx>,
        reciever_ty: Ty<'ctx>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
        name: Symbol,
        name_span: Span,
    ) -> (Vec<InterfaceMethodCandidate<'ctx>>, bool) {
        let mut out = Vec::with_capacity(interfaces.len().saturating_mul(2));
        let mut object_safety_violation = false;
        let is_existential_dispatch = matches!(self_ty.kind(), TyKind::BoxedExistential { .. });

        for (table_index, iface) in interfaces.iter().enumerate() {
            let iface_args = self.interface_args_with_self(*iface, self_ty);
            let root = InterfaceReference {
                id: iface.id,
                arguments: iface_args,
                bindings: &[],
            };

            for iface_ref in self.collect_interface_with_supers(root) {
                let Some(requirements) = self.interface_requirements(iface_ref.id) else {
                    continue;
                };

                for method in &requirements.methods {
                    if method.name != name {
                        continue;
                    }
                    if !method.has_self {
                        continue;
                    }
                    if is_existential_dispatch
                        && self.gcx().generics_of(method.id).total_count() > 0
                    {
                        if !object_safety_violation {
                            self.gcx().dcx().emit_error(
                                format!(
                                    "cannot call generic interface method '{}' on an existential value",
                                    self.gcx().symbol_text(method.name)
                                ),
                                Some(name_span),
                            );
                            self.gcx().dcx().emit_info(
                                "methods with their own generic parameters are not object-safe"
                                    .into(),
                                Some(name_span),
                            );
                        }
                        object_safety_violation = true;
                        continue;
                    }

                    let Some(slot) = self.interface_method_slot(iface_ref.id, method.id) else {
                        continue;
                    };

                    // Only substitute interface-level args (e.g. `Self`) for receiver matching.
                    // Method-generic inference vars are created later, when a branch is selected.
                    let candidate_ty = self.labeled_signature_to_ty(method.signature);
                    let candidate_receiver_ty =
                        instantiate_ty_with_args(self.gcx(), candidate_ty, iface_ref.arguments);

                    if !self.receiver_matches_method(reciever_ty, candidate_receiver_ty) {
                        continue;
                    }

                    let call_info = InterfaceCallInfo {
                        root_interface: root.id,
                        method_interface: iface_ref.id,
                        method_id: method.id,
                        slot,
                        table_index,
                    };

                    out.push(InterfaceMethodCandidate {
                        call_info,
                        candidate_ty,
                        instantiation_args: Some(iface_ref.arguments),
                        source: method.id,
                    });
                }
            }
        }

        (out, object_safety_violation)
    }

    fn receiver_matches_method(&self, receiver: Ty<'ctx>, method_ty: Ty<'ctx>) -> bool {
        let TyKind::FnPointer { inputs, .. } = method_ty.kind() else {
            return false;
        };
        let Some(expected) = inputs.first().cloned() else {
            return false;
        };

        let receiver_head = self.type_head_from_type(receiver);
        let expected_head = self.type_head_from_type(expected);
        match (receiver_head, expected_head) {
            (Some(a), Some(b)) => a == b,
            _ => receiver == expected,
        }
    }

    fn interface_args_with_self(
        &self,
        iface: InterfaceReference<'ctx>,
        self_ty: Ty<'ctx>,
    ) -> GenericArguments<'ctx> {
        if iface.arguments.is_empty() {
            return iface.arguments;
        }

        let mut args: Vec<GenericArgument<'ctx>> = Vec::with_capacity(iface.arguments.len());
        args.push(GenericArgument::Type(self_ty));
        args.extend_from_slice(&iface.arguments[1..]);

        self.gcx().store.interners.intern_generic_args(args)
    }

    fn labeled_signature_to_ty(&self, sig: &LabeledFunctionSignature<'ctx>) -> Ty<'ctx> {
        let inputs: Vec<_> = sig.inputs.iter().map(|p| p.ty).collect();
        let inputs = self.gcx().store.interners.intern_ty_list(inputs);
        Ty::new(
            TyKind::FnPointer {
                inputs,
                output: sig.output,
            },
            self.gcx(),
        )
    }
}
