//! Early binding of an interface requirement on a receiver whose outer type
//! is known but whose type arguments still hold numeric literal variables
//! (`Boxed { value: 0 }.size()`).
//!
//! Interface methods on a concrete receiver are found through conformance
//! records, and those records are matched against the receiver only once its
//! type is fully known. Such a call used to wait for numeric defaulting as a
//! whole, so its result type stayed unknown while the expressions around it
//! were typed (`Boxed { value: 0 }.size() + 1` failed).
//!
//! Here the records for the receiver's head (and blanket records), and the
//! bounds in scope that may match the receiver once it is typed, are only
//! evidence that a requirement may be callable. When they all support one
//! requirement, that requirement is bound now through the ordinary
//! `BindInterfaceMethod` path with `Self` = the receiver as it is. Its
//! signature is published, and its `Self: Interface` constraint stays an
//! ordinary `Goal::Conforms` that is proved once the receiver's literals have
//! types. No record is selected here, and finding a record never gives the
//! receiver's literals a type.
//!
//! The signature is published when it is known before the conformance is
//! proved. It may mention `Self`, the receiver with its open literals, and
//! an associated type of `Self` whose records all give one structural
//! result (`Range[{integer}]::Iterator` is `RangeIterator[{integer}]` from
//! the one generic record), which takes the projection's place. Publishing
//! gives the literals no type; whatever unifies with them later is a
//! declared type. See `publish_signature` and `structural_projection`.
//!
//! The rule is that the call means what it means with the receiver's type
//! written out (`Boxed[int32] { value: 0 }.size()`). A requirement with its
//! own `where` clause or generic parameters, one reached through an
//! interface with arguments besides `Self`, an associated type without a
//! structural result, and a call behind a custom dereference keep the
//! deferral. When solving finishes, ordinary lookup is repeated on the
//! resolved receiver and must select the same requirement at the same
//! adjustment, and each published associated type must normalize to its
//! published result.
use super::{
    Adjustment, ConstraintSolver, Goal, MethodCallData, Obligation,
    SolverResult, method::InterfaceMethodCandidate, numeric_vars_in,
};
use crate::{
    compile::context::Gcx,
    sema::{
        error::{SpannedErrorList, TypeError},
        models::{
            AliasKind, ConformanceRecord, Const, ConstKind, Constraint, GenericArgument,
            InterfaceReference, Ty, TyKind,
        },
        resolve::models::DefinitionID,
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            utils::{
                ParamEnv, instantiate::instantiate_ty_with_args, unresolved::inference_variables,
            },
            visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
        },
    },
    span::{Span, Spanned},
};

/// A receiver conformance that an early-bound call still has to prove. The
/// call's `Goal::Conforms` normally proves it; `SolverDriver::check_receiver_proofs`
/// checks it again when solving finishes, so a call whose result type is
/// known can never keep an unproved conformance.
#[derive(Debug, Clone)]
pub(super) struct ReceiverProof<'ctx> {
    pub ty: Ty<'ctx>,
    pub interface: InterfaceReference<'ctx>,
    pub location: Span,
    /// The early binding, which ordinary lookup on the resolved receiver
    /// must confirm. See `ConstraintSolver::confirm_early_lookup`.
    pub lookup: Option<Box<EarlyLookup<'ctx>>>,
    /// The associated types of the receiver that the binding published
    /// before its conformance was proved. Each must normalize to its
    /// published result once the receiver is resolved.
    pub projections: Vec<PublishedProjection<'ctx>>,
}

/// An associated type of an early-bound receiver (`Range[{integer}]::Iterator`)
/// and the structural result its call's signature was given in its place
/// (`RangeIterator[{integer}]`). See `ConstraintSolver::structural_projection`.
#[derive(Debug, Clone, Copy)]
pub(super) struct PublishedProjection<'ctx> {
    pub projection: Ty<'ctx>,
    pub result: Ty<'ctx>,
}

/// A requirement's signature as an early binding publishes it: the
/// associated types of `Self` in the instantiated signature, each with the
/// structural result that takes its place when the call is bound
/// (`substitute_published_projections`).
#[derive(Debug, Clone)]
struct PublishedSignature<'ctx> {
    projections: Vec<PublishedProjection<'ctx>>,
}

/// What an early-bound call selected, and what ordinary lookup needs to
/// repeat it once the receiver's literals have types.
#[derive(Debug, Clone)]
pub(super) struct EarlyLookup<'ctx> {
    call: MethodCallData<'ctx>,
    source: DefinitionID,
    deref_steps: usize,
    autoref_cost: u8,
    /// The bounds in scope when the call was bound, before its own
    /// requirement constraints joined them.
    param_env: ParamEnv<'ctx>,
}

/// One way to call the requirement: a receiver adjustment and the records
/// that may supply the requirement there.
struct EarlyCandidate<'ctx> {
    candidate: InterfaceMethodCandidate<'ctx>,
    receiver_ty: Ty<'ctx>,
    deref_steps: usize,
    autoref_cost: u8,
    /// Some supporting record applies whatever the literals become: it has
    /// no conditions and its target matches without giving them a type.
    unconditional: bool,
    /// Filled in once every candidate is known to be publishable.
    published: Option<PublishedSignature<'ctx>>,
}

impl<'ctx> ConstraintSolver<'ctx> {
    /// Publish a requirement whose signature is already known. When a callable
    /// field is available, only an unconditional method can supersede it now.
    /// A potential match returns Deferred; no match leaves the field available.
    pub(super) fn solve_early_interface_call(
        &mut self,
        data: &MethodCallData<'ctx>,
        prefix: &[Adjustment<'ctx>],
        has_field_fallback: bool,
    ) -> Option<SolverResult<'ctx>> {
        if data.selected.is_some() {
            return None;
        }
        let receiver = self.structurally_resolve(data.receiver);
        let can_publish = self.only_open_literals(receiver);
        if !can_publish
            && (!has_field_fallback || numeric_vars_in(&self.icx, receiver).is_empty())
        {
            return None;
        }

        let mut found: Vec<EarlyCandidate<'ctx>> = Vec::new();
        let mut used_interfaces = Vec::new();
        for (candidate_ty, deref_steps, referenceable) in
            self.reciever_candidates(receiver, data.receiver_addressable)
        {
            let candidate_ty = self.structurally_resolve(candidate_ty);
            for autoref_cost in 0..=u8::from(referenceable) {
                let receiver_ty = if autoref_cost == 0 {
                    candidate_ty
                } else {
                    Ty::new(TyKind::Reference(candidate_ty), self.gcx())
                };
                // Evidence that a requirement may be callable here: the
                // visible conformance records, and every bound in scope that
                // may apply once the literals have types. A declared bound
                // (`where Pair[T, int32]: B`) matches the typed receiver
                // exactly, and so does a bound another call left pending.
                let mut evidence = Vec::new();
                for (owner, record) in self.supporting_records(receiver_ty, data.span) {
                    // The ordinary lookup marks every record it matches as a
                    // use of its interface, whatever the method name.
                    used_interfaces.push(record.interface.id);
                    let unconditional = self.record_is_unconditional(&record, owner, receiver);
                    evidence.push((record.interface, unconditional));
                }
                for interface in
                    self.bounds_that_may_apply(receiver_ty, self.param_env.constraints())
                {
                    evidence.push((interface, false));
                }
                for (interface, unconditional) in evidence {
                    let root = InterfaceReference {
                        id: interface.id,
                        arguments: self.interface_args_with_self(interface, receiver_ty),
                        bindings: interface.bindings,
                    };
                    let roots = self.gcx().store.arenas.global.alloc_slice_clone(&[root]);
                    let (candidates, _) = self.interface_method_candidates(
                        receiver_ty,
                        Some(receiver_ty),
                        roots,
                        data.name.symbol,
                        data.name.span,
                    );
                    for candidate in candidates {
                        // Only interfaces whose arguments are just `Self`,
                        // from the root to the one declaring the requirement:
                        // the header is then the receiver itself, with
                        // nothing to recover in the extension's coordinates.
                        if !self.requirement_path_is_self_only(root, &candidate) {
                            return Some(SolverResult::Deferred);
                        }
                        // A requirement's own `where` clause can decide at
                        // which receiver adjustment it applies, or give the
                        // receiver's literals a type (`where Self == ...`).
                        if !self.gcx().constraints_of(candidate.source).is_empty() {
                            return Some(SolverResult::Deferred);
                        }
                        if autoref_cost > 0
                            && self.gcx().definition_is_clone_method(candidate.source)
                        {
                            continue;
                        }
                        if let Some(existing) = found.iter_mut().find(|existing| {
                            existing.candidate.source == candidate.source
                                && existing.receiver_ty == receiver_ty
                                && existing.deref_steps == deref_steps
                                && existing.candidate.instantiation_args
                                    == candidate.instantiation_args
                        }) {
                            existing.unconditional |= unconditional;
                            continue;
                        }
                        found.push(EarlyCandidate {
                            candidate,
                            receiver_ty,
                            deref_steps,
                            autoref_cost,
                            unconditional,
                            published: None,
                        });
                    }
                }
            }
        }

        if found.is_empty() {
            return None;
        }
        // The final proof repeats lookup on the original receiver. Behind
        // a custom dereference it cannot replay the outer lookup from here.
        if !can_publish
            || !prefix.is_empty()
            || self.may_custom_deref(receiver, data.receiver_addressable, data.span)
        {
            return Some(SolverResult::Deferred);
        }
        let Some(chosen) = self.choose_early_candidate(found, receiver, data.prefer_async, data.span)
        else {
            return Some(SolverResult::Deferred);
        };
        if has_field_fallback && !chosen.unconditional {
            return Some(SolverResult::Deferred);
        }
        let published = chosen
            .published
            .clone()
            .expect("a chosen candidate has a published signature");
        if !self.visible_traits.is_empty() {
            let mut uses = self.gcx().store.trait_visibility_uses.borrow_mut();
            uses.extend(used_interfaces);
        }

        let receiver_variable = self.icx.next_ty_var(data.reciever_span);
        let interface = InterfaceReference {
            id: chosen.candidate.call_info.method_interface,
            arguments: chosen
                .candidate
                .instantiation_args
                .expect("interface candidates carry their header"),
            bindings: &[],
        };
        self.receiver_proofs.push(ReceiverProof {
            ty: chosen.receiver_ty,
            interface,
            location: data.name.span,
            lookup: Some(Box::new(EarlyLookup {
                call: data.clone(),
                source: chosen.candidate.source,
                deref_steps: chosen.deref_steps,
                autoref_cost: chosen.autoref_cost,
                param_env: self.param_env.clone(),
            })),
            projections: published.projections.clone(),
        });
        let method_ty = data
            .method_ty
            .unwrap_or_else(|| self.icx.next_ty_var(data.span));
        let mut branch = self.method_call_branch(
            data,
            method_ty,
            receiver_variable,
            &super::method::MethodCandidate {
                source: chosen.candidate.source,
                receiver: chosen.receiver_ty,
                signature: chosen.candidate.candidate_ty,
                header: super::ExtensionHeaderMatch::Independent,
                interface: Some(chosen.candidate.call_info),
                arguments: chosen.candidate.instantiation_args,
                deref_steps: chosen.deref_steps,
                autoref_cost: chosen.autoref_cost,
            },
            prefix,
        );
        // The binding instantiates the requirement's template and then puts
        // each published result in its associated type's place.
        if let Goal::BindMethodOverload(method) = &mut branch.goal
            && let Goal::BindInterfaceMethod(bind) = method.binding.as_mut()
        {
            bind.published_projections = published
                .projections
                .iter()
                .map(|published| (published.projection, published.result))
                .collect();
        } else {
            unreachable!("an interface candidate binds through `BindInterfaceMethod`");
        }
        let apply = Self::method_application(data, method_ty, receiver_variable, false, false);
        Some(SolverResult::Solved(vec![
            Obligation {
                location: data.name.span,
                goal: Goal::Disjunction(vec![branch]),
            },
            Obligation {
                location: data.span,
                goal: Goal::Apply(apply),
            },
        ]))
    }

    /// The interfaces of bounds in scope whose subject may become the
    /// receiver once its literals have types. Matching is a rollback probe.
    fn bounds_that_may_apply(
        &self,
        receiver: Ty<'ctx>,
        constraints: impl IntoIterator<Item = Constraint<'ctx>>,
    ) -> Vec<InterfaceReference<'ctx>> {
        constraints
            .into_iter()
            .filter_map(|constraint| match constraint {
                Constraint::Bound { ty, interface } => Some((ty, interface)),
                Constraint::TypeEquality(..) => None,
            })
            .filter(|(subject, _)| {
                let subject = self.structurally_resolve(*subject);
                subject == receiver || self.icx.probe(|_| self.unify(subject, receiver).is_ok())
            })
            .map(|(_, interface)| interface)
            .collect()
    }

    /// Whether the discovery root reaches the interface declaring the
    /// requirement through interfaces that take no arguments besides
    /// `Self`, the root and the declaring one included. A root such as
    /// `Child: Base[int32]` reaches a requirement whose header is not the
    /// receiver alone.
    ///
    /// One such route suffices. The declaring interface's arguments are its
    /// header whatever route reaches it, and with `Self` alone they are the
    /// receiver on every route; a parameterised interface elsewhere in the
    /// hierarchy contributes nothing to the call. Only interfaces of that
    /// kind are walked, so the answer does not depend on the order in which
    /// superinterfaces are declared.
    fn requirement_path_is_self_only(
        &self,
        root: InterfaceReference<'ctx>,
        candidate: &InterfaceMethodCandidate<'ctx>,
    ) -> bool {
        let gcx = self.gcx();
        let self_only = |interface: &InterfaceReference<'ctx>| {
            gcx.generics_of(interface.id).total_count() == 1 && interface.arguments.len() == 1
        };
        let Some(arguments) = candidate.instantiation_args else {
            return false;
        };
        let target = (candidate.call_info.method_interface, arguments);
        if !self_only(&root) {
            return false;
        }
        let mut queue = std::collections::VecDeque::from([root]);
        let mut seen = rustc_hash::FxHashSet::default();
        seen.insert(root);
        while let Some(current) = queue.pop_front() {
            if (current.id, current.arguments) == target {
                return true;
            }
            for superface in crate::sema::impl_engine::ref_ops::direct_superfaces(gcx, current) {
                if self_only(&superface) && seen.insert(superface) {
                    queue.push_back(superface);
                }
            }
        }
        false
    }

    /// The single candidate the ordinary lookup would bind once the
    /// receiver's literals have types, if that is already certain.
    fn choose_early_candidate(
        &self,
        mut found: Vec<EarlyCandidate<'ctx>>,
        receiver: Ty<'ctx>,
        prefer_async: bool,
        span: Span,
    ) -> Option<EarlyCandidate<'ctx>> {
        // One requirement family: the same requirement with the same
        // interface arguments besides `Self`. Several records supporting it
        // are evidence, not a choice; two requirements stay deferred.
        let family = |candidate: &EarlyCandidate<'ctx>| {
            (
                candidate.candidate.source,
                candidate
                    .candidate
                    .instantiation_args
                    .map(|arguments| arguments.get(1..).unwrap_or_default().to_vec()),
            )
        };
        let first = family(found.first()?);
        if found.iter().any(|candidate| family(candidate) != first) {
            return None;
        }
        for candidate in &mut found {
            candidate.published = Some(self.publish_signature(&candidate.candidate, span)?);
        }
        // Rank as `rank_branches` does; every candidate is an interface one.
        let score = |candidate: &EarlyCandidate<'ctx>| {
            (
                self.gcx().definition_is_async(candidate.candidate.source) == prefer_async,
                std::cmp::Reverse(candidate.autoref_cost),
                std::cmp::Reverse(candidate.deref_steps),
            )
        };
        found.sort_by_key(|candidate| std::cmp::Reverse(score(candidate)));
        let mut found = found.into_iter();
        let best = found.next()?;
        if let Some(next) = found.next() {
            // A lower-ranked adjustment is selected only when the best one
            // fails. That cannot be known while the conformance is pending,
            // unless the best one holds whatever the literals become.
            if score(&next) == score(&best) || !best.unconditional {
                return None;
            }
        }
        // The receiver still holds its literals; nothing above bound them.
        debug_assert!(!numeric_vars_in(&self.icx, receiver).is_empty());
        Some(best)
    }

    /// Whether every inference variable in the receiver is an unresolved
    /// numeric literal variable, and it has at least one. Projections and
    /// other unknowns keep the call waiting.
    pub(super) fn only_open_literals(&self, receiver: Ty<'ctx>) -> bool {
        use crate::sema::tycheck::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
        struct Foreign<'a, 'ctx> {
            solver: &'a ConstraintSolver<'ctx>,
            literals: usize,
        }
        impl<'ctx> TypeVisitor<'ctx> for Foreign<'_, 'ctx> {
            fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
                match ty.kind() {
                    TyKind::Infer(_) => {
                        if self.solver.icx.unresolved_numeric_var(ty).is_some() {
                            self.literals += 1;
                            false
                        } else {
                            true
                        }
                    }
                    TyKind::Alias { .. } => true,
                    _ => ty.super_visit_with(self),
                }
            }
            fn visit_const(&mut self, value: crate::sema::models::Const<'ctx>) -> bool {
                matches!(value.kind, crate::sema::models::ConstKind::Infer(_))
                    || value.ty.visit_with(self)
            }
        }
        // The outer type must be a known nominal type or an array (or a
        // reference to one); a bare literal receiver is a later stage.
        let mut outer = receiver;
        while let TyKind::Reference(inner) | TyKind::Pointer(inner, _) = outer.kind() {
            outer = inner;
        }
        if !matches!(outer.kind(), TyKind::Adt(..) | TyKind::Array { .. }) {
            return false;
        }
        let mut visitor = Foreign {
            solver: self,
            literals: 0,
        };
        !receiver.visit_with(&mut visitor) && visitor.literals > 0
    }

    /// Whether a custom dereference may apply to the receiver. The ordinary
    /// path consults it when no record applies to the resolved receiver,
    /// and tries the reference form only where it could take the address,
    /// as `custom_deref_fallback` does.
    fn may_custom_deref(&self, receiver: Ty<'ctx>, addressable: bool, span: Span) -> bool {
        let Some(deref) = self.gcx().std_item_def(crate::hir::StdItem::Deref) else {
            return false;
        };
        let chain: Vec<_> = self
            .autoderef(receiver)
            .map(|ty| self.structurally_resolve(ty))
            .collect();
        let source = *chain.last().expect("autoderef yields the receiver");
        let addressable = chain.iter().rev().nth(1).map_or(addressable, |previous| {
            !matches!(
                previous.kind(),
                TyKind::Pointer(_, crate::hir::Mutability::Immutable)
            )
        });
        let forms = if addressable {
            vec![source, Ty::new(TyKind::Reference(source), self.gcx())]
        } else {
            vec![source]
        };
        forms.into_iter().any(|self_ty| {
            let head = self.type_head_from_type(self_ty);
            let owners = {
                let ancestry = self.gcx().class_ancestry(self_ty);
                if ancestry.is_empty() {
                    vec![self_ty]
                } else {
                    ancestry
                }
            };
            self.gcx()
                .collect_from_databases(|db| {
                    db.conformance_records
                        .values()
                        .filter(|record| record.interface.id == deref)
                        .copied()
                        .collect::<Vec<_>>()
                })
                .into_iter()
                .any(|record| {
                    owners.iter().any(|owner| {
                        (record.target.is_blanket()
                            || Some(record.target) == self.type_head_from_type(*owner)
                            || Some(record.target) == head)
                            && self.extension_target_matches(record.extension, *owner, span)
                    })
                })
        })
    }

    /// The visible conformance records whose target may match the receiver,
    /// with the owner (the receiver or a class ancestor) they matched. Each
    /// match is a rollback probe: no receiver literal is given a type.
    fn supporting_records(
        &self,
        receiver: Ty<'ctx>,
        span: Span,
    ) -> Vec<(Ty<'ctx>, ConformanceRecord<'ctx>)> {
        let ancestry = self.gcx().class_ancestry(receiver);
        let owners = if ancestry.is_empty() {
            vec![receiver]
        } else {
            ancestry
        };
        let mut records = Vec::new();
        for owner in owners {
            let head = self.type_head_from_type(owner);
            let mut matching = self.gcx().collect_from_databases(|db| {
                db.conformance_records
                    .iter()
                    .filter(|(_, record)| {
                        head.is_some_and(|head| record.target == head) || record.target.is_blanket()
                    })
                    .map(|(id, record)| (*id, *record))
                    .collect::<Vec<_>>()
            });
            matching.sort_by_key(|(id, _)| *id);
            for (_, record) in matching {
                if !self.visible_traits.is_empty()
                    && !self.visible_traits.contains(&record.interface.id)
                {
                    continue;
                }
                if !self.extension_target_matches(record.extension, owner, span) {
                    continue;
                }
                records.push((owner, record));
            }
        }
        records
    }

    /// A record with no conditions whose target matches the receiver without
    /// giving any of its literals a type (`conform[T] Boxed[T]`, or a
    /// blanket `conform[T] T`) applies whatever the literals become.
    fn record_is_unconditional(
        &self,
        record: &ConformanceRecord<'ctx>,
        owner: Ty<'ctx>,
        receiver: Ty<'ctx>,
    ) -> bool {
        !record.is_conditional
            && self.match_extension_header(record.extension, owner, receiver, record.location)
                == super::ExtensionHeaderMatch::Independent
    }

    /// The requirement's signature as the early binding publishes it, or
    /// `None` when it is not known before the receiver's conformance is
    /// proved. The requirement may have no generic parameters of its own,
    /// and its receiver input is `Self`. The other inputs and the output may
    /// mention `Self`, the receiver with its open literals: publishing it
    /// gives them no type, and whatever later unifies with it is a declared
    /// type. They may also mention an associated type of `Self` from the
    /// declaring interface or one of its superinterfaces that take only
    /// `Self`, when it has a structural result (`structural_projection`);
    /// that result takes its place. Any other alias keeps the call waiting.
    fn publish_signature(
        &self,
        candidate: &InterfaceMethodCandidate<'ctx>,
        span: Span,
    ) -> Option<PublishedSignature<'ctx>> {
        let gcx = self.gcx();
        if !gcx.generics_of(candidate.source).parameters.is_empty() {
            return None;
        }
        let arguments = candidate.instantiation_args?;
        let self_ty = arguments.first()?.ty()?;
        let TyKind::FnPointer { inputs, .. } = candidate.candidate_ty.kind() else {
            return None;
        };
        // The receiver input is `Self` itself (or a reference to it).
        let mut receiver = *inputs.first()?;
        while let TyKind::Reference(inner) = receiver.kind() {
            receiver = inner;
        }
        if !matches!(receiver.kind(), TyKind::Parameter(parameter) if parameter.index == 0) {
            return None;
        }

        // Nothing may wait on a parameter of the requirement's interface
        // that its arguments do not supply. A type parameter of the enclosing
        // declaration reaches the signature through `Self`
        // (`Pair[T, {integer}]` in `func run[T]`); it is an ordinary rigid
        // type here.
        if has_uncovered_parameters(candidate.candidate_ty, arguments) {
            return None;
        }
        let signature = instantiate_ty_with_args(gcx, candidate.candidate_ty, arguments);
        let TyKind::FnPointer { inputs, output, .. } = signature.kind() else {
            return None;
        };
        let (_, rest) = inputs.split_first()?;

        let declaring = InterfaceReference {
            id: candidate.call_info.method_interface,
            arguments,
            bindings: &[],
        };
        let interfaces = self
            .collect_interface_with_supers(declaring)
            .into_iter()
            .filter(|interface| {
                gcx.generics_of(interface.id).total_count() == 1
                    && interface.arguments.len() == 1
                    && interface.self_ty() == Some(self_ty)
            })
            .map(|interface| interface.id)
            .collect();
        let mut folder = ProjectionPublisher {
            solver: self,
            source: ProjectionSource::Method {
                receiver: self_ty,
                interfaces,
            },
            span,
            published: Vec::new(),
            failed: false,
        };
        // The published types are those of the instantiated signature, where
        // `Self` is the receiver: a result may mention a parameter of the
        // enclosing declaration, which the template's coordinates would
        // take for one of the interface's.
        let published: Vec<Ty<'ctx>> = rest
            .iter()
            .chain(std::iter::once(&output))
            .map(|ty| ty.fold_with(&mut folder))
            .collect();
        if folder.failed {
            return None;
        }
        // Nothing else may wait on an alias.
        if published
            .iter()
            .any(|ty| contains_alias(*ty) || has_unresolved_constants(*ty))
        {
            return None;
        }
        let projections = folder
            .published
            .into_iter()
            .map(|(projection, result)| PublishedProjection { projection, result })
            .collect();
        Some(PublishedSignature { projections })
    }

    /// Give a fresh local the declared structure of a qualified call's
    /// result. For example, the iterator of Range[N] is RangeIterator[N]
    /// for every eligible N. Keep the conformance and the exact associated
    /// type as proofs to check once the caller supplies N.
    pub(super) fn publish_projection_equality(
        &mut self,
        ty: Ty<'ctx>,
        span: Span,
    ) -> Option<Ty<'ctx>> {
        let mut folder = ProjectionPublisher {
            solver: self,
            source: ProjectionSource::Equality,
            span,
            published: Vec::new(),
            failed: false,
        };
        let published_ty = ty.fold_with(&mut folder);
        if folder.failed || folder.published.is_empty() {
            return None;
        }
        for (projection, result) in folder.published {
            let TyKind::Alias { def_id, args, .. } = projection.kind() else {
                unreachable!("published an associated type")
            };
            let interface = InterfaceReference {
                id: self
                    .gcx()
                    .definition_parent(def_id)
                    .expect("associated type owner"),
                arguments: args,
                bindings: &[],
            };
            self.receiver_proofs.push(ReceiverProof {
                ty: interface.self_ty().expect("projection has a receiver"),
                interface,
                location: span,
                lookup: None,
                projections: vec![PublishedProjection { projection, result }],
            });
        }
        Some(published_ty)
    }

    /// The structural result of `<receiver as interface>::assoc` while the
    /// receiver still holds open literals, or `None`.
    ///
    /// Every conformance record that may supply `receiver: interface` once
    /// the literals have types is consulted: records for the receiver's
    /// head, and blanket records. A record whose target cannot match the
    /// receiver at any width is not one of them. Each record's binding is
    /// computed in a rollback probe against the receiver as it is. Matching a
    /// generic record (`conform[Bound: Step] Range[Bound]`) gives no literal
    /// a type, and its binding may mention the receiver's literals
    /// (`RangeIterator[{integer}]`). Matching a specialised record would
    /// give them a type, so its binding must be a type without inference
    /// variables (`string`). The records must all give the same type.
    ///
    /// A bound in scope that may apply to the receiver could supply its own
    /// binding, so it keeps the call waiting, as does a binding that is
    /// itself an alias. A record's own conditions do not matter here; they
    /// are part of the conformance the call still has to prove.
    fn structural_projection(
        &self,
        receiver: Ty<'ctx>,
        interface: DefinitionID,
        assoc: DefinitionID,
        span: Span,
        constraints: impl IntoIterator<Item = Constraint<'ctx>>,
    ) -> Option<Ty<'ctx>> {
        let gcx = self.gcx();
        for bound in self.bounds_that_may_apply(receiver, constraints) {
            if self
                .collect_interface_with_supers(bound)
                .iter()
                .any(|bound| bound.id == interface)
            {
                return None;
            }
        }
        let receiver = self.structurally_resolve(receiver);
        let variables = inference_variables(receiver);
        let mut result = None;
        for (owner, record) in self.projection_records(receiver, interface, span) {
            let target = gcx.get_impl_target_ty(record.extension)?;
            let found = self.icx.probe(|_| {
                let arguments = self
                    .icx
                    .fresh_args_for_def(record.extension, record.location);
                let target = instantiate_ty_with_args(gcx, target, arguments);
                if self.unify(owner, target).is_err() {
                    // This record cannot supply the receiver at any width.
                    return Some(None);
                }
                let template = crate::sema::impl_engine::witness::record_type_witness_template(
                    gcx, &record, assoc,
                )?;
                // Only the record's own parameters are its template's; a
                // parameter of the enclosing declaration in the binding came
                // from the receiver and is a rigid type.
                if has_uncovered_parameters(template, arguments) {
                    return None;
                }
                let binding = self
                    .icx
                    .resolve_vars_if_possible(instantiate_ty_with_args(gcx, template, arguments));
                if contains_alias(binding) {
                    return None;
                }
                let literals_kept = self.icx.resolve_vars_if_possible(receiver) == receiver;
                let allowed: &[Ty<'ctx>] = if literals_kept { &variables } else { &[] };
                if has_foreign_variables(binding, allowed) {
                    return None;
                }
                // What matching gave a literal must not reach the result
                // (`Wrapped = Boxed[int64]` on `Boxed[int64]`): unified with
                // the receiver later, it would type the literal by which
                // records exist.
                let given: Vec<_> = variables
                    .iter()
                    .map(|variable| self.icx.resolve_vars_if_possible(*variable))
                    .filter(|ty| !matches!(ty.kind(), TyKind::Infer(_)))
                    .collect();
                if mentions_any(binding, &given) {
                    return None;
                }
                Some(Some(binding))
            })?;
            let Some(binding) = found else {
                continue;
            };
            match result {
                None => result = Some(binding),
                Some(previous) if previous == binding => {}
                Some(_) => return None,
            }
        }
        result
    }

    /// The conformance records for `interface` whose target may match the
    /// receiver or one of its class ancestors, visible or not: an invisible
    /// record still decides what the associated type is.
    fn projection_records(
        &self,
        receiver: Ty<'ctx>,
        interface: DefinitionID,
        span: Span,
    ) -> Vec<(Ty<'ctx>, ConformanceRecord<'ctx>)> {
        let ancestry = self.gcx().class_ancestry(receiver);
        let owners = if ancestry.is_empty() {
            vec![receiver]
        } else {
            ancestry
        };
        let mut records = Vec::new();
        for owner in owners {
            let head = self.type_head_from_type(owner);
            let mut matching = self.gcx().collect_from_databases(|db| {
                db.conformance_records
                    .iter()
                    .filter(|(_, record)| {
                        record.interface.id == interface
                            && (head.is_some_and(|head| record.target == head)
                                || record.target.is_blanket())
                    })
                    .map(|(id, record)| (*id, *record))
                    .collect::<Vec<_>>()
            });
            matching.sort_by_key(|(id, _)| *id);
            records.extend(
                matching
                    .into_iter()
                    .filter(|(_, record)| {
                        self.extension_target_matches(record.extension, owner, span)
                    })
                    .map(|(_, record)| (owner, record)),
            );
        }
        records
    }
}

/// Replaces each associated type of `Self` in an instantiated signature with
/// its structural result; see `ConstraintSolver::publish_signature`.
struct ProjectionPublisher<'a, 'ctx> {
    solver: &'a ConstraintSolver<'ctx>,
    source: ProjectionSource<'ctx>,
    span: Span,
    /// Each projection, as the instantiated signature has it, with its result.
    published: Vec<(Ty<'ctx>, Ty<'ctx>)>,
    failed: bool,
}

/// Early method lookup restricts projections to Self on the declaring
/// interface or its supers. An equality already names its interface.
enum ProjectionSource<'ctx> {
    Method {
        receiver: Ty<'ctx>,
        interfaces: Vec<DefinitionID>,
    },
    Equality,
}

/// The instantiated signature of an early-bound call with each published
/// associated type of its receiver replaced by its structural result.
pub(super) fn substitute_published_projections<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    published: &[(Ty<'ctx>, Ty<'ctx>)],
) -> Ty<'ctx> {
    struct Substitute<'a, 'ctx> {
        gcx: Gcx<'ctx>,
        published: &'a [(Ty<'ctx>, Ty<'ctx>)],
    }
    impl<'ctx> TypeFolder<'ctx> for Substitute<'_, 'ctx> {
        fn gcx(&self) -> Gcx<'ctx> {
            self.gcx
        }
        fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
            match self
                .published
                .iter()
                .find(|(projection, _)| *projection == ty)
            {
                Some((_, result)) => *result,
                None => ty.super_fold_with(self),
            }
        }
    }
    if published.is_empty() {
        return ty;
    }
    ty.fold_with(&mut Substitute { gcx, published })
}

impl<'ctx> TypeFolder<'ctx> for ProjectionPublisher<'_, 'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.solver.gcx()
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let TyKind::Alias { kind, def_id, args } = ty.kind() else {
            return ty.super_fold_with(self);
        };
        if let Some((_, result)) = self
            .published
            .iter()
            .find(|(published, _)| *published == ty)
        {
            return *result;
        }
        let result = (|| {
            if kind != AliasKind::Projection || args.len() != 1 {
                return None;
            }
            let receiver = args[0].ty()?;
            let interface = self.gcx().definition_parent(def_id)?;
            let constraints = match &self.source {
                ProjectionSource::Method {
                    receiver: method_receiver,
                    interfaces,
                } => {
                    if receiver != *method_receiver || !interfaces.contains(&interface) {
                        return None;
                    }
                    self.solver.param_env.constraints()
                }
                ProjectionSource::Equality => {
                    if self.gcx().generics_of(interface).total_count() != 1
                        || !self.solver.only_open_literals(receiver)
                    {
                        return None;
                    }
                    // A callee's pending Self: Interface is an obligation.
                    // Only bounds declared by the caller can supply its witness.
                    self.solver.assumption_constraints.to_vec()
                }
            };
            self.solver
                .structural_projection(receiver, interface, def_id, self.span, constraints)
        })();
        match result {
            Some(result) => {
                self.published.push((ty, result));
                result
            }
            None => {
                self.failed = true;
                ty
            }
        }
    }
}

/// Whether the type mentions an alias of any kind.
fn contains_alias(ty: Ty<'_>) -> bool {
    struct Aliases;
    impl<'ctx> TypeVisitor<'ctx> for Aliases {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            matches!(ty.kind(), TyKind::Alias { .. }) || ty.super_visit_with(self)
        }
    }
    ty.visit_with(&mut Aliases)
}

/// Whether a declaration's template mentions a generic parameter that
/// `arguments` does not supply, which instantiating it would leave in place.
/// The template is written in its declaration's parameters, so this is
/// decided before instantiation: afterwards, a parameter of the enclosing
/// declaration supplied through the arguments looks the same.
fn has_uncovered_parameters<'ctx>(
    template: Ty<'ctx>,
    arguments: crate::sema::models::GenericArguments<'ctx>,
) -> bool {
    struct Uncovered<'ctx>(crate::sema::models::GenericArguments<'ctx>);
    impl<'ctx> TypeVisitor<'ctx> for Uncovered<'ctx> {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            match ty.kind() {
                TyKind::Parameter(parameter) => {
                    !matches!(self.0.get(parameter.index), Some(GenericArgument::Type(_)))
                }
                _ => ty.super_visit_with(self),
            }
        }
        fn visit_const(&mut self, value: Const<'ctx>) -> bool {
            match value.kind {
                ConstKind::Param(parameter) => {
                    !matches!(self.0.get(parameter.index), Some(GenericArgument::Const(_)))
                }
                _ => value.ty.visit_with(self),
            }
        }
    }
    template.visit_with(&mut Uncovered(arguments))
}

/// Whether the type mentions an unresolved constant.
fn has_unresolved_constants(ty: Ty<'_>) -> bool {
    struct Constants;
    impl<'ctx> TypeVisitor<'ctx> for Constants {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            ty.super_visit_with(self)
        }
        fn visit_const(&mut self, value: Const<'ctx>) -> bool {
            matches!(value.kind, ConstKind::Infer(_)) || value.ty.visit_with(self)
        }
    }
    ty.visit_with(&mut Constants)
}

/// Whether the type is or contains one of `types`.
fn mentions_any<'ctx>(ty: Ty<'ctx>, types: &[Ty<'ctx>]) -> bool {
    struct Mentions<'a, 'ctx>(&'a [Ty<'ctx>]);
    impl<'ctx> TypeVisitor<'ctx> for Mentions<'_, 'ctx> {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            self.0.contains(&ty) || ty.super_visit_with(self)
        }
    }
    !types.is_empty() && ty.visit_with(&mut Mentions(types))
}

/// Whether a resolved type mentions an inference variable outside `allowed`,
/// or an unresolved constant.
fn has_foreign_variables<'ctx>(ty: Ty<'ctx>, allowed: &[Ty<'ctx>]) -> bool {
    struct Foreign<'a, 'ctx>(&'a [Ty<'ctx>]);
    impl<'ctx> TypeVisitor<'ctx> for Foreign<'_, 'ctx> {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            if matches!(ty.kind(), TyKind::Infer(_)) {
                return !self.0.contains(&ty);
            }
            ty.super_visit_with(self)
        }
        fn visit_const(&mut self, value: Const<'ctx>) -> bool {
            matches!(value.kind, ConstKind::Infer(_)) || value.ty.visit_with(self)
        }
    }
    ty.visit_with(&mut Foreign(allowed))
}

impl<'ctx> ConstraintSolver<'ctx> {
    /// Repeat the lookup of an early-bound call on its receiver as it is
    /// now, with its literals typed: the same name, arguments and result,
    /// the bounds that were in scope, visible interfaces, inherent methods,
    /// class ancestry and every receiver adjustment, ranked and probed as
    /// the ordinary path does. The early binding stands only when that
    /// lookup selects the same requirement at the same adjustment; this is
    /// what the call means when the receiver's type is written out.
    ///
    /// Everything runs in a rollback probe on a fork of this solver, so
    /// nothing it binds or records survives.
    fn confirm_early_lookup(
        &self,
        lookup: &EarlyLookup<'ctx>,
    ) -> Result<(), SpannedErrorList<'ctx>> {
        let mut call = lookup.call.clone();
        call.receiver = self.structurally_resolve(call.receiver);
        if call.receiver.has_inference_variables() || call.receiver.is_error() {
            return Ok(());
        }
        self.icx.probe(|_| {
            // The early binding already gave the callee its type; the
            // ordinary lookup must be free to bind another candidate.
            call.method_ty = Some(self.icx.next_ty_var(call.name.span));
            let mut fork = self.fork_for_lookup();
            fork.param_env = lookup.param_env.clone();
            let goals = match fork.solve_method_call(call.clone()) {
                SolverResult::Solved(goals) => goals,
                SolverResult::Error(errors) => return Err(errors),
                // Only an unresolved custom dereference waits here. The
                // typed spelling would end with its callee unresolved, so
                // the early binding is not confirmed.
                SolverResult::Deferred => {
                    return Err(vec![Spanned::new(
                        TypeError::AmbiguousOverload,
                        call.name.span,
                    )]);
                }
            };
            fork.obligations.extend(goals);
            let mut driver = super::SolverDriver::new(fork);
            driver.solve_to_fixpoint()?;
            let selected = driver.solver.overload_sources.get(&call.node_id).copied();
            let adjustment = driver
                .solver
                .adjustments
                .get(&call.reciever_node)
                .map_or(Some((0, false)), |adjustments| {
                    plain_adjustment(adjustments)
                });
            if selected == Some(lookup.source)
                && adjustment == Some((lookup.deref_steps, lookup.autoref_cost > 0))
            {
                Ok(())
            } else {
                Err(vec![Spanned::new(
                    TypeError::AmbiguousOverload,
                    call.name.span,
                )])
            }
        })
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    /// Check an associated type published by an early binding against the
    /// strict normalizer, once the receiver is resolved: the projection must
    /// normalize to exactly the resolved published result, in the bounds that
    /// were in scope at the call. Anything else, including a projection that
    /// does not normalize, is rejected.
    fn confirm_published_projection(
        &self,
        published: PublishedProjection<'ctx>,
        env: &ParamEnv<'ctx>,
    ) -> Result<(), TypeError<'ctx>> {
        let result = self.structurally_resolve(published.result);
        let projection = self.icx.resolve_vars_if_possible(published.projection);
        if result.has_inference_variables()
            || projection.has_inference_variables()
            || result.is_error()
        {
            // Unresolved variables are reported on their own.
            return Ok(());
        }
        let normalized =
            crate::sema::tycheck::utils::normalize_ty(self.icx.clone(), projection, env);
        if normalized == result && !contains_alias(normalized) {
            Ok(())
        } else {
            Err(TypeError::TyMismatch(crate::sema::error::ExpectedFound {
                expected: normalized,
                found: result,
            }))
        }
    }
}

/// The dereferences and auto-reference of a receiver adjustment made only
/// of those, as `(dereferences, referenced)`.
fn plain_adjustment(adjustments: &[Adjustment<'_>]) -> Option<(usize, bool)> {
    let mut dereferences = 0;
    let mut referenced = false;
    for adjustment in adjustments {
        match adjustment {
            Adjustment::Dereference if !referenced => dereferences += 1,
            Adjustment::Reference if !referenced => referenced = true,
            _ => return None,
        }
    }
    Some((dereferences, referenced))
}

impl<'ctx> super::SolverDriver<'ctx> {
    /// Check every early-bound call once its receiver is resolved. The
    /// receiver conformance is proved again: its `Goal::Conforms` normally
    /// did, but one that never finished must not let the call through with
    /// only its known result type. Where it holds, ordinary lookup on the
    /// resolved receiver must then select the same requirement at the same
    /// adjustment (see `ConstraintSolver::confirm_early_lookup`); where it
    /// does not, its own diagnostic is reported.
    pub(super) fn check_receiver_proofs(&mut self) -> SpannedErrorList<'ctx> {
        let mut errors = Vec::new();
        let assumptions = self.solver.assumption_constraints;
        let declared_env = std::cell::LazyCell::new(|| ParamEnv::new(assumptions.to_vec()));
        for proof in std::mem::take(&mut self.solver.receiver_proofs) {
            let ty = self.solver.structurally_resolve(proof.ty);
            let (interface, _) = self.solver.resolve_interface_ref(proof.interface);
            if ty.has_inference_variables() || ty.is_error() {
                // Unresolved variables are reported on their own.
                continue;
            }
            match self.solver.solve_conforms(proof.location, ty, interface) {
                SolverResult::Solved(_) => {}
                SolverResult::Error(found) => {
                    errors.extend(found);
                    continue;
                }
                SolverResult::Deferred => {
                    errors.push(Spanned::new(
                        TypeError::NonConformance { ty, interface },
                        proof.location,
                    ));
                    continue;
                }
            }
            if let Some(lookup) = &proof.lookup
                && let Err(found) = self.solver.confirm_early_lookup(lookup)
            {
                errors.extend(found);
                continue;
            }
            let env = proof
                .lookup
                .as_ref()
                .map_or_else(|| &*declared_env, |lookup| &lookup.param_env);
            for published in &proof.projections {
                if let Err(error) = self.solver.confirm_published_projection(*published, env) {
                    errors.push(Spanned::new(error, proof.location));
                }
            }
        }
        errors
    }
}

#[cfg(test)]
mod tests {
    use super::super::{ConstraintSolver, ConstraintSystem, MethodCallData, SolverResult};
    use crate::{
        compile::context::Gcx,
        hir::NodeID,
        sema::{
            error::TypeError,
            models::{GenericArgument, InterfaceReference, Ty},
            resolve::models::DefinitionID,
            tycheck::{
                infer::InferCtx, utils::ParamEnv, utils::instantiate::instantiate_ty_with_args,
            },
        },
        span::{FileID, Identifier, Span},
        test_support::{analyze_script, analyze_script_diagnostics},
    };
    use std::rc::Rc;

    const SIZE: &str = "struct Boxed[T] { value: T }\ninterface Size { func size() -> usize; }\n";

    fn find(gcx: Gcx<'_>, package: &crate::hir::Package, name: &str) -> DefinitionID {
        package
            .root
            .declarations
            .iter()
            .find(|declaration| gcx.symbol_text(declaration.identifier.symbol).as_str() == name)
            .unwrap()
            .id
    }

    fn solver<'ctx>(icx: Rc<InferCtx<'ctx>>, current_def: DefinitionID) -> ConstraintSolver<'ctx> {
        ConstraintSolver {
            icx,
            coercions: 0,
            boxings: 0,
            obligations: Default::default(),
            adjustments: Default::default(),
            interface_calls: Default::default(),
            integer_literals: Default::default(),
            field_indices: Default::default(),
            property_reads: Default::default(),
            overload_sources: Default::default(),
            lazy_argument_targets: Default::default(),
            deferred_return_scopes: Rc::new(Vec::new()),
            result_propagation_conversions: Default::default(),
            value_resolutions: Default::default(),
            instantiation_args: Default::default(),
            opening_calls: Default::default(),
            current_def,
            assumption_constraints: &[],
            param_env: ParamEnv::new(vec![]),
            visible_traits: Default::default(),
            held_literals: Default::default(),
            deferred: Default::default(),
            pending_member_values: Default::default(),
            lookups_have_waiters: false,
            receiver_proofs: Default::default(),
            default_scope: None,
        }
    }

    fn boxed<'ctx>(gcx: Gcx<'ctx>, package: &crate::hir::Package, element: Ty<'ctx>) -> Ty<'ctx> {
        let arguments = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(element)]);
        instantiate_ty_with_args(gcx, gcx.get_type(find(gcx, package, "Boxed")), arguments)
    }

    fn size_call<'ctx>(
        gcx: Gcx<'ctx>,
        icx: &InferCtx<'ctx>,
        receiver: Ty<'ctx>,
    ) -> MethodCallData<'ctx> {
        named_call(gcx, icx, receiver, "size")
    }

    fn named_call<'ctx>(
        gcx: Gcx<'ctx>,
        icx: &InferCtx<'ctx>,
        receiver: Ty<'ctx>,
        name: &str,
    ) -> MethodCallData<'ctx> {
        let span = Span::empty(FileID::from_raw(0));
        MethodCallData {
            interface: None,
            receiver_addressable: false,
            selected: None,
            pending_selection: None,
            node_id: NodeID::from_raw(1_000_000),
            receiver,
            reciever_span: span,
            reciever_node: NodeID::from_raw(1_000_001),
            is_unsafe_context: false,
            name: Identifier {
                symbol: gcx.intern_symbol(name),
                span,
            },
            arguments: vec![],
            result: icx.next_ty_var(span),
            method_ty: Some(icx.next_ty_var(span)),
            prefer_async: false,
            span,
        }
    }

    #[test]
    fn early_binding_leaves_the_receiver_literal_open() {
        // Matching `Boxed[{integer}]` against `Boxed[int64]` shows the record
        // may apply. It must not give the caller's literal that type: only
        // proving the pending conformance after defaulting may decide it.
        let source = format!(
            "{SIZE}conform Boxed[int64] to Size {{ func size() -> usize {{ 8 }}; }}\nfunc main() {{}}"
        );
        analyze_script(&source, |package, gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let literal = icx.next_int_var();
            let receiver = boxed(gcx, &package, literal);
            let mut solver = solver(icx.clone(), find(gcx, &package, "main"));
            let call = size_call(gcx, &icx, receiver);
            let result = solver.solve_method_call(call.clone());
            assert!(
                matches!(result, SolverResult::Solved(_)),
                "the one Size.size requirement binds early"
            );
            assert!(
                icx.unresolved_numeric_var(literal).is_some(),
                "the receiver literal was given a type: {}",
                icx.resolve_vars_if_possible(literal).format(gcx)
            );
            assert_eq!(solver.receiver_proofs.len(), 1);
            assert_eq!(solver.receiver_proofs[0].ty, receiver);
        });
    }

    #[test]
    fn competing_requirements_and_unrelated_receivers_stay_deferred() {
        // Two interfaces that both declare `size` are two requirement
        // families; which one applies depends on the literal's type.
        let source = format!(
            "{SIZE}interface Other {{ func size() -> usize; }}\nconform Boxed[int32] to Size {{ func size() -> usize {{ 4 }}; }}\nconform Boxed[int64] to Other {{ func size() -> usize {{ 8 }}; }}\nfunc main() {{}}"
        );
        analyze_script(&source, |package, gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let mut solver = solver(icx.clone(), find(gcx, &package, "main"));
            let literal = icx.next_int_var();
            let call = size_call(gcx, &icx, boxed(gcx, &package, literal));
            assert!(matches!(
                solver.solve_method_call(call),
                SolverResult::Deferred
            ));
            // A bare literal receiver is not handled in this stage.
            let call = size_call(gcx, &icx, icx.next_int_var());
            assert!(matches!(
                solver.solve_method_call(call),
                SolverResult::Deferred
            ));
            assert!(solver.receiver_proofs.is_empty());
            assert!(icx.unresolved_numeric_var(literal).is_some());
        });
    }

    #[test]
    fn finishing_rejects_an_unproved_receiver_conformance() {
        // The pending conformance is normally proved by its own goal. If that
        // goal were ever dropped, solving must still not accept the call on
        // the strength of its known result type.
        let source = format!(
            "{SIZE}conform Boxed[int64] to Size {{ func size() -> usize {{ 8 }}; }}\nfunc main() {{}}"
        );
        analyze_script(&source, |package, gcx| {
            let size = find(gcx, &package, "Size");
            let main = find(gcx, &package, "main");
            for (element, rejected) in [(gcx.types.int32, true), (gcx.types.int64, false)] {
                let ty = boxed(gcx, &package, element);
                let mut cs = ConstraintSystem::new(gcx, main);
                cs.receiver_proofs.push(super::ReceiverProof {
                    ty,
                    interface: InterfaceReference {
                        id: size,
                        arguments: gcx
                            .store
                            .interners
                            .intern_generic_args(vec![GenericArgument::Type(ty)]),
                        bindings: &[],
                    },
                    location: Span::empty(FileID::from_raw(0)),
                    lookup: None,
                    projections: Vec::new(),
                });
                let before = gcx.dcx().error_count();
                cs.solve_all();
                assert_eq!(
                    gcx.dcx().error_count() > before,
                    rejected,
                    "{}",
                    ty.format(gcx)
                );
            }
        });
    }

    #[test]
    fn literal_receivers_type_one_requirement_before_defaults() {
        for conformances in [
            "conform Boxed[int32] to Size { func size() -> usize { 4 }; }\nconform Boxed[int64] to Size { func size() -> usize { 8 }; }",
            "conform Boxed[int64] to Size { func size() -> usize { 8 }; }\nconform Boxed[int32] to Size { func size() -> usize { 4 }; }",
            "conform[T] Boxed[T] to Size { func size() -> usize { 4 }; }",
            "conform[T] T to Size { func size() -> usize { 4 }; }",
        ] {
            let source = format!(
                "{SIZE}{conformances}\nfunc take(_ size: usize) -> usize {{ size }}\nfunc main() {{ n := Boxed {{ value: 0 }}.size() + 1; same := Boxed {{ value: 0 }}.size() == 4; m := take(Boxed {{ value: 0 }}.size() * 2); }}"
            );
            let diagnostics = analyze_script_diagnostics(&source);
            assert!(diagnostics.is_empty(), "{conformances}\n{diagnostics:#?}");
        }
    }

    #[test]
    fn literal_receivers_still_prove_their_conformance() {
        let source = format!(
            "{SIZE}conform Boxed[int64] to Size {{ func size() -> usize {{ 8 }}; }}\nfunc main() {{ n := Boxed {{ value: 0 }}.size() + 1; }}"
        );
        let diagnostics = analyze_script_diagnostics(&source);
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("type 'Boxed[int32]' does not conform to interface 'Size'")),
            "{diagnostics:#?}"
        );
    }

    /// Whether the call on a fresh `Boxed[{integer}]` receiver is bound
    /// early, after `prepare` has set up the solver.
    fn binds_early(
        source: &str,
        name: &str,
        addressable: bool,
        prepare: impl for<'ctx> Fn(
            &mut ConstraintSolver<'ctx>,
            &crate::hir::Package,
            Gcx<'ctx>,
            Ty<'ctx>,
        ),
    ) -> bool {
        binds_early_on(source, name, addressable, boxed, prepare)
    }

    /// `binds_early` with the receiver built from the literal by `receiver`.
    fn binds_early_on(
        source: &str,
        name: &str,
        addressable: bool,
        receiver: for<'ctx> fn(Gcx<'ctx>, &crate::hir::Package, Ty<'ctx>) -> Ty<'ctx>,
        prepare: impl for<'ctx> Fn(
            &mut ConstraintSolver<'ctx>,
            &crate::hir::Package,
            Gcx<'ctx>,
            Ty<'ctx>,
        ),
    ) -> bool {
        let mut bound = false;
        analyze_script(source, |package, gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let literal = icx.next_int_var();
            let receiver = receiver(gcx, &package, literal);
            let mut solver = solver(icx.clone(), find(gcx, &package, "main"));
            prepare(&mut solver, &package, gcx, receiver);
            let mut call = named_call(gcx, &icx, receiver, name);
            call.receiver_addressable = addressable;
            let result = solver.solve_method_call(call);
            bound = matches!(result, SolverResult::Solved(_));
            assert_eq!(bound, !solver.receiver_proofs.is_empty());
            assert!(icx.unresolved_numeric_var(literal).is_some());
        });
        bound
    }

    fn interface<'ctx>(
        gcx: Gcx<'ctx>,
        id: DefinitionID,
        self_ty: Ty<'ctx>,
    ) -> InterfaceReference<'ctx> {
        InterfaceReference {
            id,
            arguments: gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(self_ty)]),
            bindings: &[],
        }
    }

    const PICK: &str = "struct Boxed[T] { value: T }\ninterface A {\n func prime() -> usize\n func pick() -> usize\n}\ninterface B { func pick() -> usize; }\nconform Boxed[int32] to A {\n func prime() -> usize { 1 }\n func pick() -> usize { 10 }\n}\nconform Boxed[int64] to A {\n func prime() -> usize { 1 }\n func pick() -> usize { 10 }\n}\n";

    #[test]
    fn a_pending_bound_does_not_complete_an_open_receivers_lookup() {
        // `b.prime()` bound early leaves `Boxed[{integer}]: A` among the
        // solver's bounds. A later `b.pick()` must still see that Boxed[int32]
        // also conforms to `B`, which declares `pick` as well.
        let source = format!(
            "{PICK}conform Boxed[int32] to B {{ func pick() -> usize {{ 20 }}; }}\nfunc main() {{}}"
        );
        fn pending<'ctx>(
            solver: &mut ConstraintSolver<'ctx>,
            package: &crate::hir::Package,
            gcx: Gcx<'ctx>,
            receiver: Ty<'ctx>,
        ) {
            let bound = interface(gcx, find(gcx, package, "A"), receiver);
            solver.param_env.add_pending_bound(receiver, bound);
        }
        assert!(!binds_early(&source, "pick", true, pending));
        // Without the competing conformance the pending bound agrees with
        // the records, and the call is bound early as before.
        let source = format!("{PICK}func main() {{}}");
        assert!(binds_early(&source, "pick", true, pending));
    }

    #[test]
    fn a_declared_bound_that_may_apply_after_defaulting_keeps_the_call_deferred() {
        // `where Boxed[int32]: B` matches the receiver once its literal is
        // typed; `B.pick` then competes with `A.pick`.
        let source = format!("{PICK}func main() {{}}");
        assert!(binds_early(&source, "pick", false, |_, _, _, _| {}));
        assert!(!binds_early(
            &source,
            "pick",
            false,
            |solver, package, gcx, _| {
                let int32 = boxed(gcx, package, gcx.types.int32);
                let bound = interface(gcx, find(gcx, package, "B"), int32);
                solver.param_env.add_pending_bound(int32, bound);
            }
        ));
    }

    #[test]
    fn requirements_reached_through_parameterised_interfaces_stay_deferred() {
        // `Heavy: Measured[int32]` reaches a requirement whose header holds
        // more than the receiver.
        let source = "struct Boxed[T] { value: T }\ninterface Measured[U] { func weight() -> usize; }\ninterface Heavy: Measured[int32] {}\nconform Boxed[int64] to Measured[int32] { func weight() -> usize { 8 }; }\nconform Boxed[int64] to Heavy {}\nfunc main() {}";
        assert!(!binds_early(source, "weight", false, |_, _, _, _| {}));
        let plain = "struct Boxed[T] { value: T }\ninterface Measured { func weight() -> usize; }\ninterface Heavy: Measured {}\nconform Boxed[int64] to Measured { func weight() -> usize { 8 }; }\nconform Boxed[int64] to Heavy {}\nfunc main() {}";
        assert!(binds_early(plain, "weight", false, |_, _, _, _| {}));
    }

    #[test]
    fn requirements_with_their_own_constraints_stay_deferred() {
        for clause in ["where Self: Allowed", "where Self == Boxed[int64]"] {
            let source = format!(
                "struct Boxed[T] {{ value: T }}\ninterface Allowed {{}}\ninterface Measure {{\n func measure() -> usize {clause} {{ 7 }}\n}}\nconform[T] T to Measure {{}}\nconform Boxed[int64] to Allowed {{}}\nfunc main() {{}}"
            );
            assert!(
                !binds_early(&source, "measure", false, |_, _, _, _| {}),
                "{clause}"
            );
        }
    }

    #[test]
    fn a_self_only_route_reaches_the_requirement_in_either_declaration_order() {
        // `Root` reaches `Leaf.size` through `Plain` and through
        // `Generic[bool]`. The plain route suffices whichever is declared
        // first; a root reached only through the parameterised one defers.
        fn declared_root<'ctx>(
            solver: &mut ConstraintSolver<'ctx>,
            package: &crate::hir::Package,
            gcx: Gcx<'ctx>,
            _: Ty<'ctx>,
        ) {
            let int32 = boxed(gcx, package, gcx.types.int32);
            let bound = interface(gcx, find(gcx, package, "Root"), int32);
            solver.param_env.add_pending_bound(int32, bound);
        }
        for (supers, binds) in [
            ("Plain, Generic[bool]", true),
            ("Generic[bool], Plain", true),
            ("Generic[bool]", false),
        ] {
            let source = format!(
                "struct Boxed[T] {{ value: T }}\ninterface Leaf {{ func size() -> usize; }}\ninterface Plain: Leaf {{}}\ninterface Generic[U]: Leaf {{}}\ninterface Root: {supers} {{}}\nfunc main() {{}}"
            );
            assert_eq!(
                binds_early(&source, "size", false, declared_root),
                binds,
                "{supers}"
            );
        }
    }

    const WRAP: &str = "struct Boxed[T] { value: T }\nstruct Cell[T] { value: T }\nstruct Pair[T, U] { first: T; second: U }\ninterface Wrap { type Wrapped; func wrap() -> Self::Wrapped; }\n";

    /// A type parameter of an enclosing declaration, `T`. Its index is the
    /// one `Self` has in an interface's signature template.
    fn rigid<'ctx>(gcx: Gcx<'ctx>) -> Ty<'ctx> {
        Ty::new(
            crate::sema::models::TyKind::Parameter(crate::sema::models::GenericParameter {
                index: 0,
                name: gcx.intern_symbol("T"),
            }),
            gcx,
        )
    }

    fn pair<'ctx>(
        gcx: Gcx<'ctx>,
        package: &crate::hir::Package,
        first: Ty<'ctx>,
        second: Ty<'ctx>,
    ) -> Ty<'ctx> {
        let arguments = gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(first),
            GenericArgument::Type(second),
        ]);
        instantiate_ty_with_args(gcx, gcx.get_type(find(gcx, package, "Pair")), arguments)
    }

    /// `Pair[T, {integer}]`, as in `func run[T](_ value: T)` calling
    /// `Pair { first: value, second: 0 }.wrap()`.
    fn rigid_pair<'ctx>(
        gcx: Gcx<'ctx>,
        package: &crate::hir::Package,
        literal: Ty<'ctx>,
    ) -> Ty<'ctx> {
        pair(gcx, package, rigid(gcx), literal)
    }

    #[test]
    fn associated_types_of_self_publish_only_a_structural_result() {
        fn no_bound<'ctx>(
            _: &mut ConstraintSolver<'ctx>,
            _: &crate::hir::Package,
            _: Gcx<'ctx>,
            _: Ty<'ctx>,
        ) {
        }
        fn pending_bound<'ctx>(
            solver: &mut ConstraintSolver<'ctx>,
            package: &crate::hir::Package,
            gcx: Gcx<'ctx>,
            _: Ty<'ctx>,
        ) {
            // A bound that may apply once the literal is int32 could supply
            // its own `Wrapped`.
            let int32 = boxed(gcx, package, gcx.types.int32);
            let bound = interface(gcx, find(gcx, package, "Wrap"), int32);
            solver.param_env.add_pending_bound(int32, bound);
        }
        let generic = "conform[T] Boxed[T] to Wrap { type Wrapped = Cell[T]; func wrap() -> Cell[T] { Cell { value: self.value } }; }";
        let agreeing = "conform Boxed[int32] to Wrap { type Wrapped = usize; func wrap() -> usize { 4 }; }\nconform Boxed[int64] to Wrap { type Wrapped = usize; func wrap() -> usize { 8 }; }";
        let disagreeing = "conform Boxed[int32] to Wrap { type Wrapped = usize; func wrap() -> usize { 4 }; }\nconform Boxed[int64] to Wrap { type Wrapped = uint32; func wrap() -> uint32 { 8 }; }";
        // A specialised record's binding may not use what matching gave the
        // literal (`Boxed[int32]` here): unified with the receiver later, it
        // would type the literal by which records exist.
        let specialised_self = "conform Boxed[int32] to Wrap { type Wrapped = Boxed[int32]; func wrap() -> Boxed[int32] { self }; }";
        // On `Pair[T, {integer}]`, the enclosing declaration's `T` is a rigid
        // type: a record binding that mentions it through the receiver has a
        // structural result like any other, and the same rules apply.
        let rigid_generic = "conform[X, Y] Pair[X, Y] to Wrap { type Wrapped = Pair[Y, X]; func wrap() -> Pair[Y, X] { Pair { first: self.second, second: self.first } }; }";
        let rigid_kept = "conform[X] Pair[X, int64] to Wrap { type Wrapped = X; func wrap() -> X { self.first }; }";
        let rigid_specialised = "conform[X] Pair[X, int64] to Wrap { type Wrapped = Pair[X, int64]; func wrap() -> Pair[X, int64] { self }; }";
        fn rigid_bound<'ctx>(
            solver: &mut ConstraintSolver<'ctx>,
            package: &crate::hir::Package,
            gcx: Gcx<'ctx>,
            _: Ty<'ctx>,
        ) {
            // `where Pair[T, int32]: Wrap` may apply once the literal is int32.
            let subject = pair(gcx, package, rigid(gcx), gcx.types.int32);
            let bound = interface(gcx, find(gcx, package, "Wrap"), subject);
            solver.param_env.add_pending_bound(subject, bound);
        }
        type Prepare =
            for<'ctx> fn(&mut ConstraintSolver<'ctx>, &crate::hir::Package, Gcx<'ctx>, Ty<'ctx>);
        type Receiver = for<'ctx> fn(Gcx<'ctx>, &crate::hir::Package, Ty<'ctx>) -> Ty<'ctx>;
        let cases: [(&str, Receiver, Prepare, bool); 9] = [
            (generic, boxed, no_bound, true),
            (agreeing, boxed, no_bound, true),
            (disagreeing, boxed, no_bound, false),
            (generic, boxed, pending_bound, false),
            (specialised_self, boxed, no_bound, false),
            (rigid_generic, rigid_pair, no_bound, true),
            (rigid_kept, rigid_pair, no_bound, true),
            (rigid_specialised, rigid_pair, no_bound, false),
            (rigid_generic, rigid_pair, rigid_bound, false),
        ];
        for (conformances, receiver, prepare, published) in cases {
            let source = format!("{WRAP}{conformances}\nfunc main() {{}}");
            assert_eq!(
                binds_early_on(&source, "wrap", false, receiver, prepare),
                published,
                "{conformances}"
            );
        }
    }

    #[test]
    fn a_rigid_parameter_of_the_receiver_stays_itself_in_the_published_signature() {
        // `Pair[T, {integer}]::Wrapped` is `Pair[{integer}, T]`. The result
        // is put in place after the requirement's template is instantiated:
        // in the template's coordinates `T` would read as `Self`.
        let conformance = "conform[X, Y] Pair[X, Y] to Wrap { type Wrapped = Pair[Y, X]; func wrap() -> Pair[Y, X] { Pair { first: self.second, second: self.first } }; }";
        let source = format!("{WRAP}{conformance}\nfunc main() {{}}");
        analyze_script(&source, |package, gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let literal = icx.next_int_var();
            let receiver = rigid_pair(gcx, &package, literal);
            let mut solver = solver(icx.clone(), find(gcx, &package, "main"));
            let call = named_call(gcx, &icx, receiver, "wrap");
            assert!(matches!(
                solver.solve_method_call(call),
                SolverResult::Solved(_)
            ));
            let proof = solver.receiver_proofs[0].clone();
            assert_eq!(proof.projections.len(), 1);
            let expected = pair(gcx, &package, literal, rigid(gcx));
            assert_eq!(proof.projections[0].result, expected);
        });
        let generic = format!(
            "{WRAP}{conformance}\nfunc flipped[T](_ value: T) -> Pair[int64, T] {{ Pair {{ first: value, second: 0 }}.wrap() }}\nfunc main() {{}}"
        );
        let diagnostics = analyze_script_diagnostics(&generic);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn an_associated_type_of_a_superinterface_is_published_too() {
        // `key` is declared on `Lookup`, but `Key` on its superinterface
        // `Keyed`, which takes only `Self`; its one generic record gives
        // `Cell[T]`.
        fn no_bound<'ctx>(
            _: &mut ConstraintSolver<'ctx>,
            _: &crate::hir::Package,
            _: Gcx<'ctx>,
            _: Ty<'ctx>,
        ) {
        }
        let source = "struct Boxed[T] { value: T }\nstruct Cell[T] { value: T }\ninterface Keyed { type Key; }\ninterface Lookup: Keyed { func key() -> Self::Key; }\nconform[T] Boxed[T] to Keyed { type Key = Cell[T]; }\nconform[T] Boxed[T] to Lookup { func key() -> Cell[T] { Cell { value: self.value } }; }\nfunc main() {}";
        assert!(binds_early(source, "key", false, no_bound));
    }

    #[test]
    fn a_published_projection_keeps_the_receivers_literal_and_is_checked_when_typed() {
        // `Boxed[{integer}]::Wrapped` is published as `Cell[{integer}]` with
        // the same literal. Once the literal is int32 the strict normalizer
        // must give exactly that type; a different published result is
        // rejected.
        let source = format!(
            "{WRAP}conform[T] Boxed[T] to Wrap {{ type Wrapped = Cell[T]; func wrap() -> Cell[T] {{ Cell {{ value: self.value }} }}; }}\nfunc main() {{}}"
        );
        analyze_script(&source, |package, gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let literal = icx.next_int_var();
            let receiver = boxed(gcx, &package, literal);
            let mut solver = solver(icx.clone(), find(gcx, &package, "main"));
            let call = named_call(gcx, &icx, receiver, "wrap");
            assert!(matches!(
                solver.solve_method_call(call),
                SolverResult::Solved(_)
            ));
            let proof = solver.receiver_proofs[0].clone();
            assert_eq!(proof.projections.len(), 1);
            let published = proof.projections[0];
            let cell = |element| {
                instantiate_ty_with_args(
                    gcx,
                    gcx.get_type(find(gcx, &package, "Cell")),
                    gcx.store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(element)]),
                )
            };
            assert_eq!(published.result, cell(literal));
            assert!(icx.unresolved_numeric_var(literal).is_some());

            solver.unify(literal, gcx.types.int32).unwrap();
            let env = proof.lookup.as_ref().unwrap().param_env.clone();
            assert!(solver.confirm_published_projection(published, &env).is_ok());
            for wrong in [cell(gcx.types.int64), boxed(gcx, &package, gcx.types.int32)] {
                let seeded = super::PublishedProjection {
                    result: wrong,
                    ..published
                };
                assert!(
                    matches!(
                        solver.confirm_published_projection(seeded, &env),
                        Err(TypeError::TyMismatch(_))
                    ),
                    "{}",
                    wrong.format(gcx)
                );
            }
        });
    }

    #[test]
    fn the_final_check_repeats_ordinary_lookup_on_the_typed_receiver() {
        // Only `Child` is visible. It reaches `Base.size` for Boxed[int64];
        // Boxed[int32] conforms to `Base` alone, so after defaulting ordinary
        // lookup finds no `size`, although `Boxed[int32]: Base` holds.
        let source = "struct Boxed[T] { value: T }\ninterface Base { func size() -> usize; }\ninterface Child: Base {}\nconform Boxed[int32] to Base { func size() -> usize { 4 }; }\nconform Boxed[int64] to Base { func size() -> usize { 8 }; }\nconform Boxed[int64] to Child {}\nfunc main() {}";
        analyze_script(source, |package, gcx| {
            for (element, rejected) in [(gcx.types.int32, true), (gcx.types.int64, false)] {
                let icx = Rc::new(InferCtx::new(gcx));
                let literal = icx.next_int_var();
                let receiver = boxed(gcx, &package, literal);
                let mut solver = solver(icx.clone(), find(gcx, &package, "main"));
                solver.visible_traits = Rc::new([find(gcx, &package, "Child")].into_iter().collect());
                let call = size_call(gcx, &icx, receiver);
                assert!(matches!(
                    solver.solve_method_call(call),
                    SolverResult::Solved(_)
                ));
                solver.unify(literal, element).unwrap();
                let lookup = solver.receiver_proofs[0].lookup.clone().unwrap();
                match solver.confirm_early_lookup(&lookup) {
                    Ok(()) => assert!(!rejected, "{}", element.format(gcx)),
                    Err(errors) => {
                        assert!(rejected, "{errors:#?}");
                        assert!(
                            matches!(errors[0].value, TypeError::NoSuchMember { .. }),
                            "{errors:#?}"
                        );
                    }
                }
            }
        });
    }
}
