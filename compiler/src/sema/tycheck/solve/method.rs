use super::{
    BindInterfaceMethodGoalData, ConstraintSolver, Goal, InterfaceCallInfo, MethodCallData,
    Obligation, SolverResult,
};
use crate::{
    hir::Mutability,
    sema::{
        error::TypeError,
        models::{
            GenericArgument, GenericArguments, InterfaceReference, LabeledFunctionSignature, Ty,
            TyKind,
        },
        resolve::models::DefinitionID,
        tycheck::{
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, BindOverloadGoalData, DisjunctionBranch,
            },
            utils::{
                AutoReference, generics::GenericsBuilder, instantiate::instantiate_ty_with_args,
            },
        },
    },
    span::{Spanned, Symbol},
};

struct InterfaceMethodCandidate<'ctx> {
    call_info: InterfaceCallInfo,
    candidate_ty: Ty<'ctx>,
    instantiation_args: Option<GenericArguments<'ctx>>,
    source: DefinitionID,
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_method_call(&mut self, data: MethodCallData<'ctx>) -> SolverResult<'ctx> {
        let MethodCallData {
            node_id,
            receiver,
            reciever_node,
            reciever_span,
            name,
            arguments,
            result,
            span,
            method_ty,
            expect_ty,
            ..
        } = &data;

        let rec_candidates = self.reciever_candidates(*receiver);
        for (candidate_ty, deref_steps) in rec_candidates {
            let candidate_ty = self.structurally_resolve(candidate_ty);
            for r in [
                AutoReference::None,
                AutoReference::Immutable,
                AutoReference::Mutable,
            ] {
                let reciever_ty = match r {
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
                let mut adjustments = vec![];
                for _ in 0..deref_steps {
                    adjustments.push(Adjustment::Dereference);
                }
                match r {
                    AutoReference::None => {}
                    AutoReference::Immutable => adjustments.push(Adjustment::BorrowImmutable),
                    AutoReference::Mutable => adjustments.push(Adjustment::BorrowMutable),
                }

                if matches!(candidate_ty.kind(), TyKind::Parameter(_)) {
                    let bounds = self.bounds_for_type_in_scope(candidate_ty);
                    if !bounds.is_empty() {
                        let list = self.gcx().store.arenas.global.alloc_slice_copy(&bounds);
                        if let Some(result) = self.solve_interface_method_call(
                            &data,
                            candidate_ty,
                            reciever_ty,
                            list,
                            adjustments.clone(),
                        ) {
                            return result;
                        }
                    }
                }

                if let TyKind::BoxedExistential { interfaces } = candidate_ty.kind() {
                    if let Some(result) = self.solve_interface_method_call(
                        &data,
                        candidate_ty,
                        reciever_ty,
                        interfaces,
                        adjustments.clone(),
                    ) {
                        return result;
                    }
                }

                let candidates =
                    self.lookup_instance_candidates_method(candidate_ty, reciever_ty, name.symbol);
                let Some(candidates) = candidates else {
                    continue;
                };

                if candidates.is_empty() {
                    continue;
                }

                let mut branches = vec![];
                for candidate in candidates {
                    let branch = DisjunctionBranch {
                        goal: Goal::BindOverload(BindOverloadGoalData {
                            node_id: *node_id,
                            var_ty: *method_ty,
                            candidate_ty: self.gcx().get_type(candidate),
                            source: candidate,
                        }),
                        source: Some(candidate),
                    };
                    branches.push(branch);
                }

                let disjuction_goal = Obligation {
                    location: name.span,
                    goal: Goal::Disjunction(branches),
                };

                let mut args = arguments.clone();
                args.insert(
                    0,
                    ApplyArgument {
                        id: *reciever_node,
                        label: None,
                        ty: reciever_ty,
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
                        result_ty: *result,
                        _expect_ty: *expect_ty,
                        arguments: args,
                        skip_labels: false,
                    }),
                };

                self.record_adjustments(*reciever_node, adjustments);
                return SolverResult::Solved(vec![disjuction_goal, apply_goal]);
            }
        }
        return SolverResult::Error(vec![Spanned::new(
            TypeError::NoSuchMember {
                name: name.symbol,
                on: self.structurally_resolve(*receiver),
            },
            name.span,
        )]);
    }

    fn reciever_candidates(&self, base_ty: Ty<'ctx>) -> Vec<(Ty<'ctx>, usize)> {
        let mut base = vec![];
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
    ) -> Option<Vec<DefinitionID>> {
        let head = self.type_head_from_type(candidate)?;
        let all_candidates = self.lookup_instance_candidates_visible(head, name);
        if all_candidates.is_empty() {
            return None;
        }

        let mut matching = vec![];
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

        return Some(matching);
    }

    fn solve_interface_method_call(
        &mut self,
        data: &MethodCallData<'ctx>,
        candidate_ty: Ty<'ctx>,
        reciever_ty: Ty<'ctx>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
        adjustments: Vec<Adjustment<'ctx>>,
    ) -> Option<SolverResult<'ctx>> {
        let candidates = self.interface_method_candidates(
            candidate_ty,
            reciever_ty,
            interfaces,
            data.name.symbol,
            data.span,
        );
        if candidates.is_empty() {
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
            });
        }

        let disjunction_goal = Obligation {
            location: data.name.span,
            goal: Goal::Disjunction(branches),
        };

        let mut args = data.arguments.clone();
        args.insert(
            0,
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
                result_ty: data.result,
                _expect_ty: data.expect_ty,
                arguments: args,
                skip_labels: false,
            }),
        };

        self.record_adjustments(data.reciever_node, adjustments);
        Some(SolverResult::Solved(vec![disjunction_goal, apply_goal]))
    }

    fn interface_method_candidates(
        &self,
        self_ty: Ty<'ctx>,
        reciever_ty: Ty<'ctx>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
        name: Symbol,
        span: crate::span::Span,
    ) -> Vec<InterfaceMethodCandidate<'ctx>> {
        let mut out = Vec::new();

        for (table_index, iface) in interfaces.iter().enumerate() {
            let iface_args = self.interface_args_with_self(*iface, self_ty);
            let root = InterfaceReference {
                id: iface.id,
                arguments: iface_args,
            };

            for iface_ref in self.collect_interface_with_supers(root) {
                let Some(requirements) = self.interface_requirements(iface_ref.id) else {
                    continue;
                };

                for method in &requirements.methods {
                    if method.name != name {
                        continue;
                    }

                    let Some(slot) = self.interface_method_slot(iface_ref.id, method.id) else {
                        continue;
                    };

                    let (candidate_ty, instantiation_args) = self.instantiate_interface_method(
                        method.signature,
                        method.id,
                        iface_ref.arguments,
                        span,
                    );

                    if !self.receiver_matches_method(reciever_ty, candidate_ty) {
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
                        instantiation_args,
                        source: method.id,
                    });
                }
            }
        }

        out
    }

    fn receiver_matches_method(&self, receiver: Ty<'ctx>, method_ty: Ty<'ctx>) -> bool {
        let TyKind::FnPointer { inputs, .. } = method_ty.kind() else {
            return false;
        };
        let Some(expected) = inputs.first().copied() else {
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

        let mut args: Vec<GenericArgument<'ctx>> = iface.arguments.iter().copied().collect();
        if let Some(first) = args.get_mut(0) {
            *first = GenericArgument::Type(self_ty);
        }

        self.gcx().store.interners.intern_generic_args(args)
    }

    fn instantiate_interface_method(
        &self,
        signature: &LabeledFunctionSignature<'ctx>,
        method_id: DefinitionID,
        interface_args: GenericArguments<'ctx>,
        span: crate::span::Span,
    ) -> (Ty<'ctx>, Option<GenericArguments<'ctx>>) {
        let gcx = self.gcx();
        let args = GenericsBuilder::for_item(gcx, method_id, |param, _| {
            interface_args
                .get(param.index)
                .copied()
                .unwrap_or_else(|| self.icx.var_for_generic_param(param, span))
        });

        let signature_ty = self.labeled_signature_to_ty(signature);
        let instantiated = instantiate_ty_with_args(gcx, signature_ty, args);
        let instantiation_args = if gcx.generics_of(method_id).is_empty() {
            None
        } else {
            Some(args)
        };

        (instantiated, instantiation_args)
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
