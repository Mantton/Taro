use super::{
    Adjustment, BindOverloadGoalData, ConstraintSolver, DisjunctionBranch, Goal,
    InferredStaticMemberGoalData, MemberGoalData, Obligation, SolverResult,
};
use crate::{
    hir::{NodeID, OperatorKind, Resolution, StdInterface},
    sema::{
        error::TypeError,
        models::{InterfaceReference, StructField, Ty, TyKind},
        resolve::models::{DefinitionID, DefinitionKind, PrimaryType, TypeHead, VariantCtorKind},
        tycheck::{
            resolve_conformance_witness,
            utils::{
                autoderef::Autoderef,
                generics::GenericsBuilder,
                instantiate::{instantiate_struct_definition_with_args, instantiate_ty_with_args},
            },
        },
    },
    span::{Spanned, Symbol},
};
use rustc_hash::FxHashSet;

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_member(&mut self, data: MemberGoalData<'ctx>) -> SolverResult<'ctx> {
        let MemberGoalData {
            node_id,
            receiver_node,
            receiver,
            name,
            result,
            span,
        } = data;

        let final_receiver = self.structurally_resolve(receiver);
        if final_receiver.is_error() {
            let obligation = Obligation {
                location: span,
                goal: Goal::Equal(result, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

        let mut adjustments = Vec::new();
        let mut prev: Option<Ty<'ctx>> = None;
        for ty in self.autoderef(receiver) {
            let ty = self.structurally_resolve(ty);
            if let Some(_) = prev {
                adjustments.push(Adjustment::Dereference);
            }
            prev = Some(ty);

            // Field lookup (structs only for now).
            if let Some((field, index)) = self.lookup_field(ty, name.symbol.clone()) {
                if !self
                    .gcx()
                    .is_visibility_allowed(field.visibility, self.current_def)
                {
                    let error = Spanned::new(
                        TypeError::FieldNotVisible {
                            name: field.name,
                            struct_ty: ty,
                        },
                        span,
                    );
                    return SolverResult::Error(vec![error]);
                }

                self.record_adjustments(receiver_node, adjustments);
                self.record_field_index(node_id, index);
                return self.solve_equality(span, result, field.ty);
            }

            // Instance methods.
            let candidates = self.lookup_instance_candidates(ty, name.symbol.clone());
            let candidates = self.filter_extension_candidates(candidates, ty, span);
            if !candidates.is_empty() {
                self.record_adjustments(receiver_node, adjustments);
                let mut branches = Vec::with_capacity(candidates.len());
                for candidate in candidates {
                    let candidate_ty = self.gcx().get_type(candidate);
                    branches.push(DisjunctionBranch {
                        goal: Goal::BindOverload(BindOverloadGoalData {
                            node_id,
                            var_ty: result,
                            candidate_ty,
                            source: candidate,
                            instantiation_args: None,
                        }),
                        source: Some(candidate),
                        autoref_cost: 0,
                        matches_expectation: false,
                        deref_steps: 0,
                    });
                }
                return SolverResult::Solved(vec![Obligation {
                    location: span,
                    goal: Goal::Disjunction(branches),
                }]);
            }
        }

        // Nothing matched; use last seen type for diagnostics.
        let final_ty = prev.unwrap_or_else(|| self.structurally_resolve(receiver));
        if final_ty.contains_inference() {
            return SolverResult::Deferred;
        }

        let error = Spanned::new(
            TypeError::NoSuchMember {
                name: name.symbol.clone(),
                on: final_ty,
            },
            span,
        );
        SolverResult::Error(vec![error])
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

        let Some(base_ty) = base_ty else {
            return SolverResult::Deferred;
        };

        let base_args = match base_ty.kind() {
            TyKind::Adt(_, args) if !args.is_empty() => Some(args),
            _ => None,
        };

        let Some(head) = self.type_head_from_type(base_ty) else {
            let error = Spanned::new(
                TypeError::NoSuchMember {
                    name: name.symbol.clone(),
                    on: base_ty,
                },
                span,
            );
            return SolverResult::Error(vec![error]);
        };

        let resolution = match self.resolve_static_member_resolution(head, base_ty, name.clone(), span)
        {
            Ok(resolution) => resolution,
            Err(errors) => return SolverResult::Error(errors),
        };

        self.record_value_resolution(node_id, resolution.clone());

        match resolution {
            Resolution::Definition(def_id, kind) => {
                let ty = self.gcx().get_type(def_id);
                let generics = self.gcx().generics_of(def_id);
                let mut obligations = Vec::new();
                let final_ty = if !generics.is_empty() && ty.needs_instantiation() {
                    let args = if let Some(base_args) = base_args {
                        GenericsBuilder::for_item(self.gcx(), def_id, |param, _| {
                            base_args
                                .get(param.index)
                                .cloned()
                                .unwrap_or_else(|| self.icx.var_for_generic_param(param, span))
                        })
                    } else {
                        self.icx.fresh_args_for_def(def_id, span)
                    };
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
                let mut branches = Vec::with_capacity(candidates.len());
                for candidate in candidates {
                    let candidate_ty = self.gcx().get_type(candidate);
                    branches.push(DisjunctionBranch {
                        goal: Goal::BindOverload(BindOverloadGoalData {
                            node_id,
                            var_ty: expr_ty,
                            candidate_ty,
                            source: candidate,
                            instantiation_args: None,
                        }),
                        source: Some(candidate),
                        autoref_cost: 0,
                        matches_expectation: false,
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
                        name: name.symbol.clone(),
                        on: base_ty,
                    },
                    span,
                );
                SolverResult::Error(vec![error])
            }
        }
    }

    pub fn autoderef(&self, base: Ty<'ctx>) -> Autoderef<'ctx> {
        Autoderef::new(&self.icx, base)
    }

    pub fn record_adjustments(&mut self, node_id: NodeID, adjustments: Vec<Adjustment<'ctx>>) {
        if adjustments.is_empty() {
            return;
        }
        self.adjustments.insert(node_id, adjustments);
    }

    fn lookup_field(&self, ty: Ty<'ctx>, name: Symbol) -> Option<(StructField<'ctx>, usize)> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };

        if self.gcx().definition_kind(def.id) != DefinitionKind::Struct {
            return None;
        }

        let struct_def = self.gcx().get_struct_definition(def.id);
        let struct_def = instantiate_struct_definition_with_args(self.gcx(), struct_def, args);
        for (idx, field) in struct_def.fields.iter().enumerate() {
            if field.name == name {
                return Some((field.clone(), idx));
            }
        }
        None
    }

    fn lookup_instance_candidates(&self, ty: Ty<'ctx>, name: Symbol) -> Vec<DefinitionID> {
        let Some(head) = self.type_head_from_type(ty) else {
            return vec![];
        };

        self.lookup_instance_candidates_visible(head, name)
    }

    pub(crate) fn lookup_instance_candidates_visible(
        &self,
        head: TypeHead,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let mut members = Vec::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();

        // First: Look up inherent instance methods (always available)
        let mut collect_inherent = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(idx) = db.type_head_to_members.get(&head) {
                if let Some(set) = idx.inherent_instance.get(&name) {
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

        // Second: Look up trait methods
        // TODO: Implement proper trait scoping - for now, make all trait methods available
        let mut collect_trait_methods = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(idx) = db.type_head_to_members.get(&head) {
                // For now, collect from ALL traits (not just visible ones)
                // This matches the previous behavior and keeps tests passing
                for ((_, method_name), set) in idx.trait_methods.iter() {
                    if *method_name == name {
                        for &id in &set.members {
                            if seen.insert(id) {
                                members.push(id);
                            }
                        }
                    }
                }
            }
        };

        gcx.with_session_type_database(|db| collect_trait_methods(db));
        for index in gcx.visible_packages() {
            gcx.with_type_database(index, |db| collect_trait_methods(db));
        }

        members
            .into_iter()
            .filter(|id| self.gcx().is_definition_visible(*id, self.current_def))
            .collect()
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
            TyKind::Reference(_, mutbl) => Some(TypeHead::Reference(mutbl)),
            TyKind::Pointer(_, mutbl) => Some(TypeHead::Pointer(mutbl)),
            TyKind::Tuple(items) => Some(TypeHead::Tuple(items.len() as u16)),
            TyKind::Array { .. } => Some(TypeHead::Array),
            TyKind::Closure { closure_def_id, .. } => Some(TypeHead::Closure(closure_def_id)),
            TyKind::Parameter(_) => None,
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

    fn resolve_static_member_resolution(
        &self,
        head: TypeHead,
        base_ty: Ty<'ctx>,
        name: crate::span::Identifier,
        span: crate::span::Span,
    ) -> Result<Resolution, Vec<Spanned<TypeError<'ctx>>>> {
        let gcx = self.gcx();
        if let TypeHead::Nominal(def_id) = head {
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

        let mut candidates = self.collect_static_member_candidates(head, name.symbol.clone());

        // UFCS: If no static members found, look for instance methods.
        // This allows calling `Interface.method(value)` where `method` is an instance method.
        if candidates.is_empty() {
            candidates = self.collect_instance_member_candidates(head, name.symbol.clone());
        }

        if candidates.is_empty() {
            let error = Spanned::new(
                TypeError::NoSuchMember {
                    name: name.symbol.clone(),
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
                    name: name.symbol.clone(),
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

    fn collect_static_member_candidates(&self, head: TypeHead, name: Symbol) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let mut members = Vec::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();

        let mut collect = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(index) = db.type_head_to_members.get(&head) {
                if let Some(set) = index.inherent_static.get(&name) {
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

        members
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
        // TODO: Implement proper trait scoping - for now, make all trait methods available
        let mut collect_trait_methods = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(idx) = db.type_head_to_members.get(&head) {
                // For now, collect from ALL traits (not just visible ones)
                // This matches the previous behavior and keeps tests passing
                for ((_, method_name), set) in idx.trait_methods.iter() {
                    if *method_name == name {
                        for &id in &set.members {
                            if seen.insert(id) {
                                members.push(id);
                            }
                        }
                    }
                }
            }
        };

        gcx.with_session_type_database(|db| collect_trait_methods(db));
        for index in gcx.visible_packages() {
            gcx.with_type_database(index, |db| collect_trait_methods(db));
        }

        members
    }

    /// Look up operator candidates for the given type and operator kind.
    pub fn lookup_operator_candidates(
        &self,
        ty: Ty<'ctx>,
        kind: OperatorKind,
    ) -> Vec<DefinitionID> {
        if let Some(head) = self.type_head_from_type(ty) {
            return self.lookup_operator_candidates_visible(head, kind);
        }

        // If no primary type head (e.g. generic parameter), resolve operators from
        // in-scope bounds (`T: Ord`, `T: PartialEq`, etc.) and existential interfaces.
        match ty.kind() {
            TyKind::Parameter(_) | TyKind::BoxedExistential { .. } => {
                self.lookup_operator_candidates_from_bounds(ty, kind)
            }
            _ => Vec::new(),
        }
    }

    fn lookup_operator_candidates_from_bounds(
        &self,
        ty: Ty<'ctx>,
        kind: OperatorKind,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let Some(std_interface) = StdInterface::from_operator_kind(kind) else {
            return Vec::new();
        };
        let Some(interface_id) = gcx.std_interface_def(std_interface) else {
            return Vec::new();
        };
        let Some(method_name) = std_interface.operator_method_name() else {
            return Vec::new();
        };
        let method_symbol = gcx.intern_symbol(method_name);

        // Collect all explicit bounds from the current parameter environment.
        let mut bounds = self.bounds_for_type_in_scope(ty);

        // Existentials carry their own interface list on the type itself.
        if let TyKind::BoxedExistential { interfaces } = ty.kind() {
            bounds.extend_from_slice(interfaces);
        }

        let mut out = Vec::new();
        let mut seen_defs: FxHashSet<DefinitionID> = FxHashSet::default();
        let mut seen_ifaces: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();

        for bound in bounds {
            // Resolve inference where possible; skip unresolved bounds for now.
            let (bound, has_infer) = self.resolve_interface_ref(bound);
            if has_infer {
                continue;
            }

            // Include superinterfaces so `T: Ord` can satisfy PartialOrd/PartialEq operators.
            for iface in self.collect_interface_with_supers(bound) {
                if !seen_ifaces.insert(iface) || iface.id != interface_id {
                    continue;
                }

                let Some(requirements) = self.interface_requirements(iface.id) else {
                    continue;
                };

                for method_req in &requirements.methods {
                    if method_req.name != method_symbol {
                        continue;
                    }

                    if seen_defs.insert(method_req.id)
                        && gcx.is_definition_visible(method_req.id, self.current_def)
                    {
                        out.push(method_req.id);
                    }
                }
            }
        }

        out
    }

    fn lookup_operator_candidates_visible(
        &self,
        head: TypeHead,
        kind: OperatorKind,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let mut members = Vec::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();

        // First, look up in the old-style TypeMemberIndex.operators (deprecated path)
        let mut collect = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(idx) = db.type_head_to_members.get(&head) {
                if let Some(set) = idx.operators.get(&kind) {
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

        // Then, look up through interface conformance (new path)
        if let Some(candidates) = self.lookup_operator_via_interface(head, kind) {
            for id in candidates {
                if seen.insert(id) {
                    members.push(id);
                }
            }
        }

        members
            .into_iter()
            .filter(|id| self.gcx().is_definition_visible(*id, self.current_def))
            .collect()
    }

    /// Look up operator candidates through interface conformance.
    /// This is the new interface-based operator resolution path.
    fn lookup_operator_via_interface(
        &self,
        head: TypeHead,
        kind: OperatorKind,
    ) -> Option<Vec<DefinitionID>> {
        let gcx = self.gcx();

        // Convert OperatorKind to StdInterface
        let std_interface = StdInterface::from_operator_kind(kind)?;

        // Get the interface definition ID
        let interface_id = gcx.std_interface_def(std_interface)?;

        // Create an interface reference with empty arguments (we'll match later)
        let interface_ref = InterfaceReference {
            id: interface_id,
            arguments: &[],
            bindings: &[],
        };

        // Check if the type conforms to this interface
        let witness = resolve_conformance_witness(gcx, head, interface_ref)?;

        // Get the method name for this operator
        let method_name = std_interface.operator_method_name()?;
        let method_symbol = gcx.intern_symbol(method_name);

        // Look up the method witness
        // We need to find the method requirement ID first
        let requirements = gcx.get_interface_requirements(interface_id)?;
        for method_req in &requirements.methods {
            if method_req.name == method_symbol {
                if let Some(method_witness) = witness.method_witnesses.get(&method_req.id) {
                    if let Some(impl_id) = method_witness.implementation.impl_id() {
                        return Some(vec![impl_id]);
                    }
                }
            }
        }

        None
    }
}
