use super::method::{MethodCandidate, ReceiverResolution};
use super::{
    Adjustment, ApplyArgument, ApplyGoalData, BindInterfaceMethodGoalData, BindMethodValueGoalData,
    BindOverloadGoalData, ConstraintSolver, DisjunctionBranch, Goal, InferredStaticMemberGoalData,
    InterfaceCallInfo, MemberGoalData, Obligation, ResolvedPropertyRead, SolverResult,
};
use crate::{
    hir::{NodeID, Resolution, StdItem},
    sema::{
        error::TypeError,
        models::{GenericArguments, InterfacePropertyRequirement, InterfaceReference, Ty, TyKind},
        resolve::models::{DefinitionID, DefinitionKind, PrimaryType, TypeHead, VariantCtorKind},
        tycheck::utils::{autoderef::Autoderef, instantiate::instantiate_ty_with_args},
    },
    span::{Spanned, Symbol},
};
use rustc_hash::FxHashSet;

#[cfg(test)]
mod tests;

#[derive(Clone)]
struct InterfacePropertyCandidate<'ctx> {
    property: InterfacePropertyRequirement<'ctx>,
    getter_ty: Ty<'ctx>,
    call_info: InterfaceCallInfo,
    interface_args: GenericArguments<'ctx>,
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_member(&mut self, data: MemberGoalData<'ctx>) -> SolverResult<'ctx> {
        self.solve_member_at(data, Vec::new(), Vec::new())
    }

    fn solve_member_at(
        &mut self,
        data: MemberGoalData<'ctx>,
        prefix: Vec<Adjustment<'ctx>>,
        mut visited: Vec<Ty<'ctx>>,
    ) -> SolverResult<'ctx> {
        let original = data.clone();
        let MemberGoalData {
            classify_only,
            receiver_addressable,
            node_id,
            receiver_node,
            receiver,
            name,
            result,
            span,
            ..
        } = data;

        let final_receiver = self.structurally_resolve(receiver);
        // Lookup needs a known pointee as well as a known reference header.
        // Otherwise an unrelated reference extension can constrain the pointee
        // before its producing expression (for example indexing) resolves.
        if self.autoderef(final_receiver).any(|ty| ty.is_infer()) {
            return SolverResult::Deferred;
        }
        if final_receiver.is_error() {
            let obligation = Obligation {
                location: span,
                goal: Goal::Equal(result, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }
        let mut hidden_field = None;
        let mut field_adjustments = prefix.clone();
        for (depth, ty) in self.autoderef(receiver).enumerate() {
            let ty = self.structurally_resolve(ty);
            if depth > 0 {
                field_adjustments.push(Adjustment::Dereference);
            }
            if let Some((index, field_ty, visibility)) = self.lookup_field(ty, name.symbol) {
                if self
                    .gcx()
                    .is_visibility_allowed(visibility, self.current_def)
                {
                    if classify_only {
                        return self.solve_equality(span, result, self.gcx().types.bool);
                    }
                    self.record_adjustments(receiver_node, field_adjustments);
                    self.record_field_index(node_id, index);
                    return self.solve_equality(span, result, field_ty);
                }
                hidden_field.get_or_insert((name.symbol, ty));
            }
        }
        let mut adjustments = prefix.clone();
        let mut prev: Option<Ty<'ctx>> = None;
        let mut referenceable = receiver_addressable;
        let mut methods = Vec::new();
        let mut method_seen = FxHashSet::default();
        for ty in self.autoderef(receiver) {
            let ty = self.structurally_resolve(ty);
            if let Some(previous) = prev {
                referenceable = !matches!(
                    previous.kind(),
                    TyKind::Pointer(_, crate::hir::Mutability::Immutable)
                );
                adjustments.push(Adjustment::Dereference);
            }
            prev = Some(ty);

            for autoref in [false, true] {
                if autoref && !referenceable {
                    continue;
                }
                let receiver_arg_ty = if autoref {
                    Ty::new(TyKind::Reference(ty), self.gcx())
                } else {
                    ty
                };
                let Some(property) = self.lookup_computed_property(receiver_arg_ty, name.symbol)
                else {
                    continue;
                };
                if let Some(owner) = self.gcx().definition_parent(property.property_id)
                    && self.gcx().definition_kind(owner) == DefinitionKind::Impl
                {
                    match self.match_extension_header(owner, receiver_arg_ty, ty, span) {
                        super::ExtensionHeaderMatch::Mismatch => continue,
                        super::ExtensionHeaderMatch::NeedsLiteralType => {
                            return SolverResult::Deferred;
                        }
                        super::ExtensionHeaderMatch::Independent => {}
                    }
                }
                if classify_only {
                    return self.solve_equality(span, result, self.gcx().types.bool);
                }
                let mut property_adjustments = adjustments.clone();
                if autoref {
                    property_adjustments.push(Adjustment::Reference);
                }
                self.record_adjustments(receiver_node, property_adjustments);
                self.record_property_read(
                    node_id,
                    ResolvedPropertyRead {
                        getter_id: property.getter_id,
                    },
                );

                let getter_ty = self.gcx().get_type(property.getter_id);
                let getter_var = self.icx.next_ty_var(span);

                let bind = Obligation {
                    location: span,
                    goal: Goal::BindOverload(BindOverloadGoalData {
                        static_owner: None,
                        node_id,
                        var_ty: getter_var,
                        candidate_ty: getter_ty,
                        source: property.getter_id,
                        instantiation_args: None,
                    }),
                };

                let apply = Obligation {
                    location: span,
                    goal: Goal::Apply(ApplyGoalData {
                        call_node_id: node_id,
                        callee_node_id: None,
                        call_span: span,
                        callee_ty: getter_var,
                        callee_source: Some(property.getter_id),
                        is_unsafe_context: false,
                        result_ty: result,
                        arguments: vec![ApplyArgument {
                            is_spread: false,
                            is_lazy_wrapped: false,
                            contains_await: false,
                            deferred_return_scope: None,
                            id: receiver_node,
                            label: None,
                            ty: receiver_arg_ty,
                            span,
                        }],
                        skip_labels: false,
                        input_only_selection: false,
                    }),
                };

                return SolverResult::Solved(vec![bind, apply]);
            }

            let interfaces = match ty.kind() {
                TyKind::Parameter(_)
                | TyKind::Alias {
                    kind:
                        crate::sema::models::AliasKind::Projection
                        | crate::sema::models::AliasKind::Opaque,
                    ..
                } => {
                    let bounds = self.bounds_for_member_lookup(ty);
                    (!bounds.is_empty()).then(|| {
                        self.gcx().store.arenas.global.alloc_slice_clone(&bounds) as &'ctx [_]
                    })
                }
                TyKind::BoxedExistential { interfaces } => Some(interfaces),
                _ => self.concrete_interface_roots(ty, span),
            };
            if let Some(interfaces) = interfaces
                && let Some(property_result) = self.solve_interface_property_member(
                    node_id,
                    receiver_node,
                    ty,
                    name,
                    result,
                    span,
                    &adjustments,
                    interfaces,
                )
            {
                if classify_only {
                    return self.solve_equality(span, result, self.gcx().types.bool);
                }
                return property_result;
            }

            for autoref_cost in 0..=u8::from(referenceable) {
                let method_receiver = if autoref_cost == 0 {
                    ty
                } else {
                    Ty::new(TyKind::Reference(ty), self.gcx())
                };
                let direct =
                    self.lookup_instance_candidates_method(ty, method_receiver, name.symbol, span);
                let interfaces = self.method_interfaces(method_receiver, span);
                let mut candidates: Vec<_> = direct
                    .into_iter()
                    .map(|(source, header)| {
                        (source, self.gcx().get_type(source), None, None, header)
                    })
                    .collect();
                if let Some(interfaces) = interfaces {
                    let (requirements, _) = self.interface_method_candidates(
                        method_receiver,
                        Some(method_receiver),
                        interfaces,
                        name.symbol,
                        name.span,
                    );
                    candidates.extend(requirements.into_iter().map(|candidate| {
                        (
                            candidate.source,
                            candidate.candidate_ty,
                            candidate.instantiation_args,
                            Some(candidate.call_info),
                            super::ExtensionHeaderMatch::Independent,
                        )
                    }));
                }
                for (source, signature, arguments, interface, header) in candidates {
                    let duplicate_builtin_operator = interface.as_ref().is_some_and(|info| {
                        method_seen.contains(&(source, method_receiver, None))
                            && arguments.is_some_and(|args| {
                                crate::mir::primitive_operators::ITEMS.iter().any(|&item| {
                                    self.gcx().std_item_def(item) == Some(info.method_interface)
                                        && crate::mir::primitive_operators::interface_for_type(
                                            self.gcx(),
                                            method_receiver,
                                            item,
                                        )
                                        .is_some_and(|builtin| builtin.arguments == args)
                                })
                            })
                    });
                    if autoref_cost > 0 && self.gcx().definition_is_clone_method(source)
                        || duplicate_builtin_operator
                        || !method_seen.insert((source, method_receiver, arguments))
                    {
                        continue;
                    }
                    if classify_only {
                        return self.solve_equality(span, result, self.gcx().types.void);
                    }
                    methods.push(MethodCandidate {
                        source,
                        receiver: method_receiver,
                        signature,
                        header,
                        arguments,
                        interface,
                        autoref_cost,
                        deref_steps: adjustments.len(),
                    });
                }
            }
        }
        if !methods.is_empty() && final_receiver.contains_inference() {
            let resolution = self.resolve_specialized_receivers(
                final_receiver,
                &mut methods,
                |method, literals| {
                    self.probe_receiver_widths(literals, |fork| {
                        fork.obligations.push_back(Obligation {
                            location: span,
                            goal: Self::bound_method_branch(&original, method, &prefix).goal,
                        });
                    })
                },
            );
            match resolution {
                ReceiverResolution::Ready => {}
                ReceiverResolution::Deferred => return SolverResult::Deferred,
                ReceiverResolution::Inferred => {
                    return self.solve_member_at(original, prefix, visited);
                }
            }
        }
        if !methods.is_empty() {
            let branches = methods
                .iter()
                .map(|method| Self::bound_method_branch(&original, method, &prefix))
                .collect();
            return SolverResult::Solved(vec![Obligation {
                location: span,
                goal: Goal::Disjunction(branches),
            }]);
        }

        let hidden_method = self.autoderef(receiver).any(|ty| {
            self.type_head_from_type(ty)
                .is_some_and(|head| self.has_invisible_instance_member(head, name.symbol))
        });
        if hidden_field.is_none() && !hidden_method {
            match self.custom_deref_fallback(
                receiver,
                receiver_addressable,
                span,
                &prefix,
                &mut visited,
            ) {
                Ok(Some((target, prefix, proof))) => {
                    let mut data = original;
                    data.receiver = target;
                    data.receiver_addressable = true;
                    let mut result = self.solve_member_at(data, prefix, visited);
                    if let SolverResult::Solved(obligations) = &mut result {
                        obligations.extend(proof);
                    }
                    return result;
                }
                Err(result) => return result,
                Ok(None) => {}
            }
        }

        // Exhaust all autodereference levels before classifying an unknown
        // member as a method. A field of &Box[T] lives on Box[T], not &Box[T].
        if classify_only {
            return self.solve_equality(span, result, self.gcx().types.void);
        }

        // Nothing matched; use last seen type for diagnostics.
        let final_ty = prev.unwrap_or_else(|| self.structurally_resolve(receiver));
        if final_ty.contains_inference() {
            return SolverResult::Deferred;
        }

        if let Some((name, struct_ty)) = hidden_field {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::FieldNotVisible { name, struct_ty },
                span,
            )]);
        }

        let error_kind = if let Some(head) = self.type_head_from_type(final_ty) {
            if self.has_invisible_instance_member(head, name.symbol) {
                TypeError::MethodNotVisible {
                    name: name.symbol,
                    on: final_ty,
                }
            } else {
                TypeError::NoSuchMember {
                    name: name.symbol,
                    on: final_ty,
                }
            }
        } else {
            TypeError::NoSuchMember {
                name: name.symbol,
                on: final_ty,
            }
        };

        let error = Spanned::new(error_kind, span);
        SolverResult::Error(vec![error])
    }

    fn bound_method_branch(
        data: &MemberGoalData<'ctx>,
        method: &MethodCandidate<'ctx>,
        prefix: &[Adjustment<'ctx>],
    ) -> DisjunctionBranch<'ctx> {
        // Bound capture construction takes the address only after selection.
        let mut adjustments = prefix.to_vec();
        adjustments.resize(method.deref_steps, Adjustment::Dereference);
        DisjunctionBranch {
            goal: Goal::BindMethodOverload(super::BindMethodOverloadGoalData {
                binding: Box::new(Goal::BindMethodValue(BindMethodValueGoalData {
                    explicit_arguments: data.explicit_arguments.clone(),
                    node_id: data.node_id,
                    var_ty: data.result,
                    candidate_ty: method.signature,
                    source: method.source,
                    instantiation_args: method.arguments,
                    call_info: method.interface,
                    receiver: method.receiver,
                    signature_hint: data.signature_hint,
                })),
                receiver_node_id: data.receiver_node,
                receiver_constraint: None,
                adjustments,
            }),
            source: Some(method.source),
            autoref_cost: method.autoref_cost,
            matches_async_preference: false,
            deref_steps: method.deref_steps,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn solve_interface_property_member(
        &mut self,
        node_id: NodeID,
        receiver_node: NodeID,
        receiver_ty: Ty<'ctx>,
        name: crate::span::Identifier,
        result: Ty<'ctx>,
        span: crate::span::Span,
        base_adjustments: &[Adjustment<'ctx>],
        interfaces: &'ctx [InterfaceReference<'ctx>],
    ) -> Option<SolverResult<'ctx>> {
        let mut candidates = Vec::new();
        let mut seen = FxHashSet::default();
        for (table_index, interface) in interfaces.iter().enumerate() {
            let root_args = self.interface_args_with_self(*interface, receiver_ty);
            let root = InterfaceReference {
                id: interface.id,
                arguments: root_args,
                bindings: interface.bindings,
            };
            for interface_ref in self.collect_interface_with_supers(root) {
                let Some(requirements) = self.interface_requirements(interface_ref.id) else {
                    continue;
                };
                for property in &requirements.properties {
                    if property.name != name.symbol || !seen.insert((property.id, interface_ref)) {
                        continue;
                    }
                    let getter_ty =
                        self.labeled_signature_to_ty(self.gcx().get_signature(property.getter_id));
                    let instantiated_getter =
                        instantiate_ty_with_args(self.gcx(), getter_ty, interface_ref.arguments);
                    let TyKind::FnPointer { inputs, .. } = instantiated_getter.kind() else {
                        continue;
                    };
                    let Some(expected_receiver) = inputs.first().copied() else {
                        continue;
                    };
                    if expected_receiver != receiver_ty {
                        continue;
                    }
                    candidates.push(InterfacePropertyCandidate {
                        property: *property,
                        getter_ty,
                        call_info: InterfaceCallInfo {
                            root_interface: root.id,
                            method_interface: interface_ref.id,
                            method_id: property.getter_id,
                            table_index,
                        },
                        interface_args: interface_ref.arguments,
                    });
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }
        if candidates.len() > 1 {
            let mut declaring = Vec::new();
            for candidate in &candidates {
                if !declaring.contains(&candidate.call_info.method_interface) {
                    declaring.push(candidate.call_info.method_interface);
                }
            }
            return Some(SolverResult::Error(vec![Spanned::new(
                TypeError::AmbiguousProperty {
                    name: name.symbol,
                    on: receiver_ty,
                    interfaces: declaring,
                },
                span,
            )]));
        }

        let candidate = candidates.pop().unwrap();
        self.record_adjustments(receiver_node, base_adjustments.to_vec());
        self.record_property_read(
            node_id,
            ResolvedPropertyRead {
                getter_id: candidate.property.getter_id,
            },
        );
        let getter_var = self.icx.next_ty_var(span);
        let bind = Obligation {
            location: span,
            goal: Goal::BindInterfaceMethod(BindInterfaceMethodGoalData {
                node_id,
                var_ty: getter_var,
                candidate_ty: candidate.getter_ty,
                call_info: candidate.call_info,
                instantiation_args: Some(candidate.interface_args),
                published_projections: Vec::new(),
            }),
        };
        let apply = Obligation {
            location: span,
            goal: Goal::Apply(ApplyGoalData {
                call_node_id: node_id,
                callee_node_id: None,
                call_span: span,
                callee_ty: getter_var,
                callee_source: None,
                is_unsafe_context: false,
                result_ty: result,
                arguments: vec![ApplyArgument {
                    is_spread: false,
                    is_lazy_wrapped: false,
                    contains_await: false,
                    deferred_return_scope: None,
                    id: receiver_node,
                    label: None,
                    ty: receiver_ty,
                    span,
                }],
                skip_labels: false,
                input_only_selection: false,
            }),
        };
        Some(SolverResult::Solved(vec![bind, apply]))
    }

    pub fn solve_inferred_static_member(
        &mut self,
        data: InferredStaticMemberGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let InferredStaticMemberGoalData {
            node_id,
            name,
            expr_ty,
            base_hint,
            allow_unsafe_callable_values,
            prefer_async,
            span,
        } = data;

        let base_ty = self
            .select_inferred_member_base(expr_ty, base_hint)
            .map(|ty| self.structurally_resolve(ty));

        if let Some(base) = base_ty {
            if base.is_error() {
                let obligation = Obligation {
                    location: span,
                    goal: Goal::Equal(expr_ty, Ty::error(self.gcx())),
                };
                return SolverResult::Solved(vec![obligation]);
            }
        }

        let Some(mut base_ty) = base_ty else {
            return SolverResult::Deferred;
        };

        let resolution = match self.resolve_static_member_resolution(base_ty, name, span) {
            Ok(resolution) => resolution,
            Err(errors) => {
                // Keep the Result's own members authoritative (notably ok/err).
                // A missing contextual member may instead belong to its success
                // type; bind only the callee here, and wrap its ready output at
                // the consuming expression's ordinary coercion site.
                if let Some((success, _)) = self.gcx().result_parts(base_ty) {
                    let success = self.structurally_resolve(success);
                    if success.is_infer() {
                        return SolverResult::Deferred;
                    }
                    match self.resolve_static_member_resolution(success, name, span) {
                        Ok(resolution) => {
                            base_ty = success;
                            resolution
                        }
                        Err(errors) => return SolverResult::Error(errors),
                    }
                } else if let Some(result) = self.try_inferred_member_optional_wrap_fallback(
                    node_id, base_ty, name, expr_ty, span,
                ) {
                    return result;
                } else {
                    return SolverResult::Error(errors);
                }
            }
        };
        let base_args = match base_ty.kind() {
            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
            _ => None,
        };

        self.record_value_resolution(node_id, resolution.clone());

        match resolution {
            Resolution::Definition(def_id, kind) => {
                if !allow_unsafe_callable_values
                    && matches!(
                        kind,
                        DefinitionKind::Function
                            | DefinitionKind::AssociatedFunction
                            | DefinitionKind::VariantConstructor(VariantCtorKind::Function)
                    )
                    && self.gcx().definition_is_unsafe(def_id)
                {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::UnsafeCallableValueNotAllowed {
                            name: self.gcx().definition_symbol_or_fallback(def_id),
                        },
                        span,
                    )]);
                }

                let ty = self.gcx().get_type(def_id);
                let generics = self.gcx().generics_of(def_id);
                let mut obligations = Vec::new();
                let final_ty = if kind == DefinitionKind::AssociatedConstant {
                    let args = match crate::sema::tycheck::utils::members::constant_arguments(
                        &self.icx,
                        def_id,
                        base_ty,
                        self.current_def,
                        span,
                    ) {
                        Ok(args) => args,
                        Err(e) => return SolverResult::Error(vec![Spanned::new(e, span)]),
                    };
                    self.record_instantiation(node_id, args);
                    obligations.extend(self.constraints_for_def(def_id, Some(args), span));
                    instantiate_ty_with_args(self.gcx(), ty, args)
                } else if !generics.is_empty() && ty.needs_instantiation() {
                    let args = self.instantiate_generic_args_with_defaults(def_id, base_args, span);
                    let instantiated = instantiate_ty_with_args(self.gcx(), ty, args);
                    self.record_instantiation(node_id, args);
                    obligations.extend(self.constraints_for_def(def_id, Some(args), span));
                    instantiated
                } else {
                    ty
                };

                match self.unify(expr_ty, final_ty) {
                    Ok(_) => {
                        if matches!(
                            kind,
                            DefinitionKind::Function
                                | DefinitionKind::AssociatedFunction
                                | DefinitionKind::VariantConstructor(VariantCtorKind::Function)
                        ) {
                            self.icx.bind_overload(expr_ty, def_id);
                        }
                        SolverResult::Solved(obligations)
                    }
                    Err(e) => SolverResult::Error(vec![Spanned::new(e, span)]),
                }
            }
            Resolution::FunctionSet(candidates) => {
                if !allow_unsafe_callable_values {
                    if let Some(def_id) = candidates
                        .iter()
                        .copied()
                        .find(|candidate| self.gcx().definition_is_unsafe(*candidate))
                    {
                        return SolverResult::Error(vec![Spanned::new(
                            TypeError::UnsafeCallableValueNotAllowed {
                                name: self.gcx().definition_symbol_or_fallback(def_id),
                            },
                            span,
                        )]);
                    }
                }

                let mut branches = Vec::with_capacity(candidates.len());
                for candidate in candidates {
                    let candidate_ty = self.gcx().get_type(candidate);
                    branches.push(DisjunctionBranch {
                        goal: Goal::BindOverload(BindOverloadGoalData {
                            static_owner: Some(base_ty),
                            node_id,
                            var_ty: expr_ty,
                            candidate_ty,
                            source: candidate,
                            instantiation_args: None,
                        }),
                        source: Some(candidate),
                        autoref_cost: 0,
                        matches_async_preference: self.gcx().definition_is_async(candidate)
                            == prefer_async,
                        deref_steps: 0,
                    });
                }
                SolverResult::Solved(vec![Obligation {
                    location: span,
                    goal: Goal::Disjunction(branches),
                }])
            }
            _ => {
                let error = Spanned::new(
                    TypeError::NoSuchMember {
                        name: name.symbol,
                        on: base_ty,
                    },
                    span,
                );
                SolverResult::Error(vec![error])
            }
        }
    }

    /// Fallback for `.variant` shorthand when the expected type is `Optional[Inner]`
    /// but `variant` is not a member of `Optional` itself. Peels the optional,
    /// re-attempts resolution on `Inner`, and if it resolves to a unit variant
    /// constructor, binds the node's type to `Inner` so the outer coerce goal
    /// can insert the `OptionalWrap` adjustment.
    fn try_inferred_member_optional_wrap_fallback(
        &mut self,
        node_id: NodeID,
        base_ty: Ty<'ctx>,
        name: crate::span::Identifier,
        expr_ty: Ty<'ctx>,
        span: crate::span::Span,
    ) -> Option<SolverResult<'ctx>> {
        if self.gcx().symbol_eq(name.symbol, "some") || self.gcx().symbol_eq(name.symbol, "none") {
            return None;
        }

        let (_, inner_ty) = self.unwrap_optional_type(base_ty)?;
        let inner_ty = self.structurally_resolve(inner_ty);
        if inner_ty.is_infer() || inner_ty.is_error() {
            return None;
        }

        let inner_resolution = self
            .resolve_static_member_resolution(inner_ty, name, span)
            .ok()?;

        // Only accept unit (constant) variant constructors for the wrap fallback.
        // Other resolutions (function variants, associated functions) return
        // callable types that would need the wrap to apply at the call site,
        // which is a separate concern.
        let (def_id, kind) = match inner_resolution {
            Resolution::Definition(
                def_id,
                kind @ DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
            ) => (def_id, kind),
            _ => return None,
        };

        self.record_value_resolution(node_id, Resolution::Definition(def_id, kind));

        let def_ty = self.gcx().get_type(def_id);
        let generics = self.gcx().generics_of(def_id);
        let inner_base_args = match inner_ty.kind() {
            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
            _ => None,
        };
        let mut obligations = Vec::new();
        let inner_final_ty = if !generics.is_empty() && def_ty.needs_instantiation() {
            let args = self.instantiate_generic_args_with_defaults(def_id, inner_base_args, span);
            let instantiated = instantiate_ty_with_args(self.gcx(), def_ty, args);
            self.record_instantiation(node_id, args);
            obligations.extend(self.constraints_for_def(def_id, Some(args), span));
            instantiated
        } else {
            def_ty
        };

        if let Err(e) = self.unify(inner_ty, inner_final_ty) {
            return Some(SolverResult::Error(vec![Spanned::new(e, span)]));
        }
        match self.unify(expr_ty, inner_final_ty) {
            Ok(_) => Some(SolverResult::Solved(obligations)),
            Err(e) => Some(SolverResult::Error(vec![Spanned::new(e, span)])),
        }
    }

    pub fn autoderef(&self, base: Ty<'ctx>) -> Autoderef<'ctx> {
        Autoderef::new(&self.icx, base)
    }

    pub fn record_adjustments(&mut self, node_id: NodeID, adjustments: Vec<Adjustment<'ctx>>) {
        if adjustments.is_empty() {
            return;
        }
        if let Some(existing) = self.adjustments.get_mut(&node_id) {
            let mut combined = adjustments;
            combined.extend(std::mem::take(existing));
            *existing = combined;
        } else {
            self.adjustments.insert(node_id, adjustments);
        }
    }

    /// Coercions of an already-adjusted source run after its inner operations.
    /// Keep this ordering in speculative solver branches as well as the outer
    /// ConstraintSystem's corresponding append operation.
    pub(super) fn append_adjustments(
        &mut self,
        node_id: NodeID,
        adjustments: Vec<Adjustment<'ctx>>,
    ) {
        self.adjustments
            .entry(node_id)
            .or_default()
            .extend(adjustments);
    }

    pub(crate) fn lookup_field(
        &self,
        ty: Ty<'ctx>,
        name: Symbol,
    ) -> Option<(usize, Ty<'ctx>, crate::sema::resolve::models::Visibility)> {
        if let Some((index, ty)) = ty.labeled_tuple_field(name) {
            return Some((index, ty, crate::sema::resolve::models::Visibility::Public));
        }
        let TyKind::Adt(def, _) = ty.kind() else {
            return None;
        };

        if self.gcx().definition_kind(def.id) != DefinitionKind::Struct {
            return None;
        }

        let struct_def = self.gcx().source_struct_definition(ty)?;
        for (idx, field) in struct_def.fields.iter().enumerate() {
            if field.name == name {
                return Some((idx, field.ty, field.visibility));
            }
        }
        None
    }

    pub(crate) fn lookup_computed_property(
        &self,
        ty: Ty<'ctx>,
        name: Symbol,
    ) -> Option<crate::compile::context::ComputedPropertyEntry<'ctx>> {
        let head = self.type_head_from_type(ty)?;
        let property = self.gcx().lookup_computed_property(head, name)?;
        if !self
            .gcx()
            .is_visibility_allowed(property.visibility, self.current_def)
        {
            return None;
        }

        Some(property)
    }

    pub(super) fn lookup_instance_candidates(
        &self,
        ty: Ty<'ctx>,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let mut candidates = match self.type_head_from_type(ty) {
            Some(head) => self.lookup_instance_candidates_visible(head, name),
            None => Vec::new(),
        };
        if self.gcx().is_class_type(ty) {
            for method in self.gcx().class_methods(ty) {
                if self.gcx().definition_ident(method.implementation).symbol == name
                    && self
                        .gcx()
                        .is_definition_visible(method.implementation, self.current_def)
                    && !candidates.contains(&method.implementation)
                {
                    candidates.push(method.implementation);
                }
            }
        }
        candidates.retain(|source| super::inherent_method(self.gcx(), *source));
        // Builtin conformances have no source extension to seed member lookup.
        // Discover the requirement independently of an earlier generic call
        // warming the synthetic-method cache. Normal interface-call solving
        // must still prove Clone for this actual receiver and its components.
        let gcx = self.gcx();
        let ty = crate::sema::tycheck::utils::normalize_aliases(gcx, ty);
        if gcx.symbol_eq(&name, "clone")
            && (crate::sema::impl_engine::builtin_copy_clone(gcx, ty)
                || matches!(
                    ty.kind(),
                    TyKind::Tuple(_) | TyKind::Array { .. } | TyKind::Closure { .. }
                ))
            && let Some(clone_id) = gcx.std_item_def(StdItem::Clone)
            && let Some(requirements) = gcx.get_interface_requirements(clone_id)
            && let Some(method) = requirements
                .methods
                .iter()
                .find(|method| method.name == name)
            && gcx.is_definition_visible(method.id, self.current_def)
            && !candidates.contains(&method.id)
        {
            candidates.push(method.id);
        }
        // Primitive operator conformances also have no source extension.
        // Lookup cannot depend on an earlier generic call warming witnesses.
        for &item in crate::mir::primitive_operators::ITEMS {
            if crate::mir::primitive_operators::supports(gcx, ty, item)
                && let Some(interface) = gcx.std_item_def(item)
                && let Some(requirements) = gcx.get_interface_requirements(interface)
                && let Some(method) = requirements
                    .methods
                    .iter()
                    .find(|method| method.name == name)
                && gcx.is_definition_visible(method.id, self.current_def)
                && !candidates.contains(&method.id)
            {
                candidates.push(method.id);
            }
        }
        if candidates.is_empty()
            && let Some(method) = gcx.erased_take_as(self.current_def, ty, name)
        {
            candidates.push(method);
        }
        candidates
    }

    pub(crate) fn lookup_instance_candidates_visible(
        &self,
        head: TypeHead,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let mut members = Vec::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();
        members.reserve(8);
        seen.reserve(8);

        // First: Look up inherent instance methods (always available)
        let mut collect_inherent = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(idx) = db.type_head_to_members.get(&head) {
                if let Some(set) = idx.inherent_instance.get(&name) {
                    let extra = set.members.len();
                    members.reserve(extra);
                    seen.reserve(extra);
                    for &id in &set.members {
                        if seen.insert(id) {
                            members.push(id);
                        }
                    }
                }
            }
        };

        gcx.with_session_type_database(|db| collect_inherent(db));
        for index in gcx.visible_packages() {
            gcx.with_type_database(index, |db| collect_inherent(db));
        }

        members.retain(|id| gcx.is_definition_visible(*id, self.current_def));
        members
    }

    fn collect_blanket_trait_methods_for_name(
        &self,
        db: &crate::compile::context::TypeDatabase<'ctx>,
        name: Symbol,
        members: &mut Vec<DefinitionID>,
        seen: &mut FxHashSet<DefinitionID>,
    ) {
        for (head, index) in &db.type_head_to_members {
            if head.is_blanket() {
                self.collect_visible_trait_methods_for_name(index, name, members, seen);
            }
        }
    }

    /// Check whether a type has any instance member with the given name that
    /// exists but is not visible from the current definition. Used to produce
    /// a "method is private" error instead of "no such member".
    pub(crate) fn has_invisible_instance_member(&self, head: TypeHead, name: Symbol) -> bool {
        let gcx = self.gcx();
        let current_def = self.current_def;

        let check = |db: &crate::compile::context::TypeDatabase<'ctx>| -> bool {
            if let Some(idx) = db.type_head_to_members.get(&head) {
                if let Some(set) = idx.inherent_instance.get(&name) {
                    for &id in &set.members {
                        if !gcx.is_definition_visible(id, current_def) {
                            return true;
                        }
                    }
                }
            }
            false
        };

        if gcx.with_session_type_database(|db| check(db)) {
            return true;
        }
        for index in gcx.visible_packages() {
            if gcx.with_type_database(index, |db| check(db)) {
                return true;
            }
        }

        false
    }

    fn collect_visible_trait_methods_for_name(
        &self,
        index: &crate::compile::context::TypeMemberIndex,
        name: Symbol,
        members: &mut Vec<DefinitionID>,
        seen: &mut FxHashSet<DefinitionID>,
    ) {
        // Some dependency/package contexts do not currently populate visible trait scope.
        // Preserve previous behavior there so we don't regress trait lookup.
        if self.visible_traits.is_empty() {
            if let Some(methods) = index.trait_methods_by_name.get(&name) {
                let extra = methods.len();
                members.reserve(extra);
                seen.reserve(extra);
                for &id in methods {
                    if seen.insert(id) {
                        members.push(id);
                    }
                }
            }
            return;
        }

        for &interface_id in self.visible_traits.iter() {
            let key = (interface_id, name);
            let Some(set) = index.trait_methods.get(&key) else {
                continue;
            };
            if !set.members.is_empty() {
                self.gcx()
                    .store
                    .trait_visibility_uses
                    .borrow_mut()
                    .insert(interface_id);
            }

            let extra = set.members.len();
            members.reserve(extra);
            seen.reserve(extra);
            for &id in &set.members {
                if seen.insert(id) {
                    members.push(id);
                }
            }
        }
    }

    pub fn type_head_from_type(&self, ty: Ty<'ctx>) -> Option<TypeHead> {
        match ty.kind() {
            TyKind::Bool => Some(TypeHead::Primary(PrimaryType::Bool)),
            TyKind::Rune => Some(TypeHead::Primary(PrimaryType::Rune)),
            TyKind::String => Some(TypeHead::Primary(PrimaryType::String)),
            TyKind::Int(k) => Some(TypeHead::Primary(PrimaryType::Int(k))),
            TyKind::UInt(k) => Some(TypeHead::Primary(PrimaryType::UInt(k))),
            TyKind::Float(k) => Some(TypeHead::Primary(PrimaryType::Float(k))),
            TyKind::Adt(def, _) => Some(TypeHead::Nominal(def.id)),
            TyKind::Reference(_) => Some(TypeHead::Reference),
            TyKind::Pointer(_, mutbl) => Some(TypeHead::Pointer(mutbl)),
            TyKind::Tuple(items) => Some(TypeHead::Tuple(items.len() as u16)),
            TyKind::Array { .. } => Some(TypeHead::Array),
            TyKind::Closure { closure_def_id, .. } => Some(TypeHead::Closure(closure_def_id)),
            TyKind::Parameter(_) | TyKind::ExistentialSelf(_) => None,
            TyKind::Alias { .. } => None, // Alias should be normalized before lookup
            TyKind::Infer(_)
            | TyKind::FnPointer { .. }
            | TyKind::BoxedExistential { .. }
            | TyKind::Opaque(_) // Opaque types have no members
            | TyKind::Error
            | TyKind::Never => None,
        }
    }

    fn select_inferred_member_base(
        &self,
        expr_ty: Ty<'ctx>,
        base_hint: Option<Ty<'ctx>>,
    ) -> Option<Ty<'ctx>> {
        let base_hint = base_hint.map(|ty| self.structurally_resolve(ty));
        if let Some(base_hint) = base_hint {
            if !base_hint.is_infer() {
                return match base_hint.kind() {
                    TyKind::FnPointer { output, .. } => {
                        let output = self.structurally_resolve(output);
                        if output.is_infer() {
                            None
                        } else {
                            Some(output)
                        }
                    }
                    _ => Some(base_hint),
                };
            }
        }

        let expr_ty = self.structurally_resolve(expr_ty);
        if expr_ty.is_infer() {
            return None;
        }

        match expr_ty.kind() {
            TyKind::FnPointer { output, .. } => {
                let output = self.structurally_resolve(output);
                if output.is_infer() {
                    None
                } else {
                    Some(output)
                }
            }
            _ => Some(expr_ty),
        }
    }

    pub(super) fn resolve_static_member_resolution(
        &self,
        base_ty: Ty<'ctx>,
        name: crate::span::Identifier,
        span: crate::span::Span,
    ) -> Result<Resolution, Vec<Spanned<TypeError<'ctx>>>> {
        let gcx = self.gcx();
        let head = self.type_head_from_type(base_ty);
        if let Some(TypeHead::Nominal(def_id)) = head {
            if gcx.definition_kind(def_id) == DefinitionKind::Enum {
                let enum_def = gcx.get_enum_definition(def_id);

                if let Some(variant) = enum_def.variants.iter().find(|v| v.name == name.symbol) {
                    if !gcx.is_definition_visible(variant.ctor_def_id, self.current_def) {
                        let error = Spanned::new(
                            TypeError::NoSuchMember {
                                name: name.symbol,
                                on: base_ty,
                            },
                            span,
                        );
                        return Err(vec![error]);
                    }

                    let kind = gcx.definition_kind(variant.ctor_def_id);
                    return Ok(Resolution::Definition(variant.ctor_def_id, kind));
                }
            }
        }

        if let Some(id) = crate::sema::tycheck::utils::members::associated_constant(
            gcx,
            base_ty,
            name.symbol,
            self.current_def,
            Some(&self.icx),
            span,
        )
        .map_err(|e| vec![Spanned::new(e, span)])?
        {
            return Ok(Resolution::Definition(
                id,
                DefinitionKind::AssociatedConstant,
            ));
        }

        let mut candidates = crate::sema::tycheck::utils::members::static_candidates(
            self.gcx(),
            base_ty,
            name.symbol,
            self.current_def,
        );

        // UFCS: If no static members found, look for instance methods.
        // This allows calling `Interface.method(value)` where `method` is an instance method.
        if candidates.is_empty()
            && let Some(head) = head
        {
            candidates = self.collect_instance_member_candidates(head, name.symbol);
        }

        if candidates.is_empty()
            && let Some(TypeHead::Nominal(interface_id)) = head
            && gcx.definition_kind(interface_id) == DefinitionKind::Interface
            && let Some(requirements) = gcx.get_interface_requirements(interface_id)
            && let Some(property) = requirements
                .properties
                .iter()
                .find(|property| property.name == name.symbol)
        {
            candidates.push(property.getter_id);
        }

        if candidates.is_empty() {
            let error = Spanned::new(
                TypeError::NoSuchMember {
                    name: name.symbol,
                    on: base_ty,
                },
                span,
            );
            return Err(vec![error]);
        }

        let visible: Vec<_> = candidates
            .into_iter()
            .filter(|id| gcx.is_definition_visible(*id, self.current_def))
            .collect();

        if visible.is_empty() {
            let error = Spanned::new(
                TypeError::NoSuchMember {
                    name: name.symbol,
                    on: base_ty,
                },
                span,
            );
            return Err(vec![error]);
        }

        if visible.len() == 1 {
            let id = visible[0];
            let kind = gcx.definition_kind(id);
            return Ok(Resolution::Definition(id, kind));
        }

        Ok(Resolution::FunctionSet(visible))
    }

    /// Collect instance method candidates for UFCS resolution.
    /// This is used when static member lookup fails to allow `Interface.method(value)` syntax.
    fn collect_instance_member_candidates(
        &self,
        head: TypeHead,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let mut members = Vec::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();

        // Collect from inherent instance methods
        let mut collect = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(index) = db.type_head_to_members.get(&head) {
                if let Some(set) = index.inherent_instance.get(&name) {
                    for &id in &set.members {
                        if seen.insert(id) {
                            members.push(id);
                        }
                    }
                }
            }
        };

        gcx.with_session_type_database(|db| collect(db));
        for index in gcx.visible_packages() {
            gcx.with_type_database(index, |db| collect(db));
        }

        // Second: Look up trait methods
        let mut collect_trait_methods = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(idx) = db.type_head_to_members.get(&head) {
                self.collect_visible_trait_methods_for_name(idx, name, &mut members, &mut seen);
            }
            self.collect_blanket_trait_methods_for_name(db, name, &mut members, &mut seen);
        };

        gcx.with_session_type_database(|db| collect_trait_methods(db));
        for index in gcx.visible_packages() {
            gcx.with_type_database(index, |db| collect_trait_methods(db));
        }

        members
    }
}
