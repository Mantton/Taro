use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID},
    sema::{
        models::{
            AliasKind, AssociatedTypeDefinition, ClosureKind, ConformanceWitness, GenericArgument,
            GenericArguments, InterfaceConstantRequirement, InterfaceDefinition,
            InterfaceMethodRequirement, InterfaceReference, InterfaceRequirements,
            LabeledFunctionSignature, MethodImplementation, MethodWitness, SyntheticMethodKind, Ty,
            TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            infer::InferCtx,
            utils::{generics::GenericsBuilder, unify::TypeUnifier},
        },
    },
    span::Symbol,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

use crate::sema::tycheck::utils::instantiate::{
    instantiate_const_with_args, instantiate_ty_with_args,
};

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(_: &hir::Package, context: Gcx<'ctx>) -> CompileResult<()> {
        let actor = Actor::new(context);
        actor.check_all_conformances();
        context.dcx().ok()
    }
}

#[derive(Debug)]
enum ConformanceError<'ctx> {
    MissingMethod {
        name: Symbol,
        signature: &'ctx LabeledFunctionSignature<'ctx>,
    },
    MissingConstant {
        name: Symbol,
        ty: Ty<'ctx>,
    },
    MissingAssociatedType {
        name: Symbol,
    },
}

impl<'ctx> Actor<'ctx> {
    fn check_all_conformances(&self) {
        // Get all conformances from the session type database
        let conformances = self
            .context
            .with_session_type_database(|db| db.conformances.clone());

        // PHASE 1: Build all conformance witnesses first
        for (type_head, records) in &conformances {
            for record in records {
                self.check_conformance(*type_head, record);
            }
        }

        // PHASE 2: Validate superinterface requirements
        // Now all witnesses exist, so we can validate that required interfaces are implemented
        let mut seen: FxHashSet<(TypeHead, InterfaceReference<'ctx>)> = FxHashSet::default();

        for (type_head, records) in conformances {
            for record in &records {
                // Also validate superface requirements
                for iface in self
                    .collect_interface_with_supers(record.interface)
                    .into_iter()
                    .skip(1)
                {
                    if !seen.insert((type_head, iface)) {
                        continue;
                    }

                    let mut derived = *record;
                    derived.interface = iface;
                    // Pass the original interface to indicate this is a superinterface requirement
                    self.validate_conformance_with_context(
                        type_head,
                        &derived,
                        Some(record.interface),
                    );
                }
            }
        }
    }

    fn check_conformance(
        &self,
        type_head: TypeHead,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) {
        match self.build_witness(type_head, record) {
            Ok(witness) => {
                // Store witness for later use (codegen, method dispatch, etc.)
                self.store_witness(type_head, record.interface, witness);
            }
            Err(errors) => {
                self.emit_conformance_errors(type_head, record, errors, None);
            }
        }
    }

    fn validate_conformance_with_context(
        &self,
        type_head: TypeHead,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
        required_by: Option<InterfaceReference<'ctx>>,
    ) {
        // For superinterface requirements, check if a witness already exists
        // (from the user's separate impl block for that interface)
        if required_by.is_some() {
            // Check if there's already a conformance witness for this interface
            let has_witness = self.context.with_session_type_database(|db| {
                let key = (type_head, record.interface);
                db.conformance_witnesses.contains_key(&key)
            });

            if !has_witness {
                // No impl block exists for this superinterface
                self.emit_conformance_errors(type_head, record, vec![], required_by);
            }
        } else {
            // For direct conformance, build and validate the witness
            if let Err(errors) = self.build_witness(type_head, record) {
                self.emit_conformance_errors(type_head, record, errors, required_by);
            }
        }
    }

    fn build_witness(
        &self,
        type_head: TypeHead,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) -> Result<ConformanceWitness<'ctx>, Vec<ConformanceError<'ctx>>> {
        let interface_id = record.interface.id;

        // Get requirements for this interface
        let Some(requirements) = self.get_requirements(interface_id) else {
            // No requirements found - likely an error elsewhere
            return Ok(ConformanceWitness::default());
        };

        let mut witness = ConformanceWitness::default();
        witness.extension_id = Some(record.extension);
        let mut errors = Vec::new();

        // 1. Check associated types
        for assoc in &requirements.types {
            match self.find_type_witness(type_head, assoc, record) {
                Ok(ty) => {
                    witness.type_witnesses.insert(assoc.id, ty);
                }
                Err(e) => errors.push(e),
            }
        }

        // 2. Check methods
        for method in &requirements.methods {
            match self.find_method_witness(type_head, method, record, &witness.type_witnesses) {
                Ok(witness_entry) => {
                    witness.method_witnesses.insert(method.id, witness_entry);
                }
                Err(e) => errors.push(e),
            }
        }

        // 4. Check constants
        for constant in &requirements.constants {
            match self.find_constant_witness(type_head, constant, record) {
                Ok(id) => {
                    witness.constant_witnesses.insert(constant.id, id);
                }
                Err(e) => errors.push(e),
            }
        }

        if errors.is_empty() {
            Ok(witness)
        } else {
            Err(errors)
        }
    }

    fn store_witness(
        &self,
        type_head: TypeHead,
        interface: InterfaceReference<'ctx>,
        witness: ConformanceWitness<'ctx>,
    ) {
        self.context.with_session_type_database(|db| {
            db.conformance_witnesses
                .insert((type_head, interface), witness);
        });
    }

    fn get_requirements(
        &self,
        interface_id: DefinitionID,
    ) -> Option<&'ctx InterfaceRequirements<'ctx>> {
        self.context
            .with_type_database(interface_id.package(), |db| {
                db.interface_requirements.get(&interface_id).cloned()
            })
    }

    fn interface_definition(
        &self,
        interface_id: DefinitionID,
    ) -> Option<&'ctx InterfaceDefinition<'ctx>> {
        self.context
            .with_type_database(interface_id.package(), |db| {
                db.def_to_iface_def.get(&interface_id).cloned()
            })
    }

    fn collect_interface_with_supers(
        &self,
        root: InterfaceReference<'ctx>,
    ) -> Vec<InterfaceReference<'ctx>> {
        let mut out = Vec::new();
        let mut queue = std::collections::VecDeque::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();

        seen.insert(root.id);
        out.push(root);
        queue.push_back(root);

        while let Some(current) = queue.pop_front() {
            let Some(def) = self.interface_definition(current.id) else {
                continue;
            };

            for superface in &def.superfaces {
                let iface = self.substitute_interface_ref(superface.value, current.arguments);
                if seen.insert(iface.id) {
                    out.push(iface);
                    queue.push_back(iface);
                }
            }
        }

        out
    }

    fn substitute_interface_ref(
        &self,
        template: InterfaceReference<'ctx>,
        args: GenericArguments<'ctx>,
    ) -> InterfaceReference<'ctx> {
        if args.is_empty() {
            return template;
        }

        let mut new_args = Vec::with_capacity(template.arguments.len());
        for arg in template.arguments.iter() {
            match arg {
                GenericArgument::Type(ty) => {
                    let substituted = instantiate_ty_with_args(self.context, *ty, args);
                    new_args.push(GenericArgument::Type(substituted));
                }
                GenericArgument::Const(c) => {
                    let substituted = instantiate_const_with_args(self.context, *c, args);
                    new_args.push(GenericArgument::Const(substituted));
                }
            }
        }

        let mut new_bindings = Vec::with_capacity(template.bindings.len());
        for binding in template.bindings {
            let substituted = instantiate_ty_with_args(self.context, binding.ty, args);
            new_bindings.push(crate::sema::models::AssociatedTypeBinding {
                name: binding.name,
                ty: substituted,
            });
        }

        let interned = self.context.store.interners.intern_generic_args(new_args);
        InterfaceReference {
            id: template.id,
            arguments: interned,
            bindings: self
                .context
                .store
                .arenas
                .global
                .alloc_slice_clone(&new_bindings),
        }
    }

    fn resolve_conformance_witness(
        &self,
        type_head: TypeHead,
        interface: InterfaceReference<'ctx>,
    ) -> Option<ConformanceWitness<'ctx>> {
        let gcx = self.context;

        // Check cached witnesses across all packages
        if let Some(mut witness) = gcx.find_in_databases(|db| {
            db.conformance_witnesses
                .get(&(type_head, interface))
                .cloned()
        }) {
            // Check if we need to patch a stale synthetic ID
            for (method_id, method_witness) in &mut witness.method_witnesses {
                if let MethodImplementation::Synthetic(kind, None) = method_witness.implementation {
                    // Try to look up the ID in synthetic_methods
                    if let Some(info) = self.context.get_synthetic_method(type_head, *method_id) {
                        if let Some(syn_id) = info.syn_id {
                            method_witness.implementation =
                                MethodImplementation::Synthetic(kind, Some(syn_id));
                        }
                    }
                }
            }
            return Some(witness);
        }

        // Collect conformance records from all packages
        let records = gcx.collect_from_databases(|db| {
            db.conformances.get(&type_head).cloned().unwrap_or_default()
        });

        // Auto-implement Tuple for tuple types
        if let Some(witness) = self.build_tuple_witness(type_head, interface) {
            self.store_witness(type_head, interface, witness.clone());
            return Some(witness);
        }

        if let Some(witness) = self.build_closure_witness(type_head, interface) {
            self.store_witness(type_head, interface, witness.clone());
            return Some(witness);
        }

        for record in records {
            if record.interface.id == interface.id {
                if let Ok(witness) = self.build_witness(type_head, &record) {
                    self.store_witness(type_head, interface, witness.clone());
                    return Some(witness);
                }
                return None;
            }

            for iface in self
                .collect_interface_with_supers(record.interface)
                .into_iter()
                .skip(1)
            {
                if iface.id != interface.id {
                    continue;
                }

                let mut derived = record;
                derived.interface = iface;
                if let Ok(witness) = self.build_witness(type_head, &derived) {
                    self.store_witness(type_head, interface, witness.clone());
                    return Some(witness);
                }
                // Don't return None here - continue checking other records
                // The superinterface impl might not be in this specific impl block
            }
        }

        None
    }

    /// Auto-implement Tuple for tuple types.
    fn build_tuple_witness(
        &self,
        type_head: TypeHead,
        interface: InterfaceReference<'ctx>,
    ) -> Option<ConformanceWitness<'ctx>> {
        // Only handle Tuple type heads
        let TypeHead::Tuple(_) = type_head else {
            return None;
        };

        // Check if this is the Tuple interface
        let tuple_def = self
            .context
            .std_interface_def(crate::hir::StdInterface::Tuple)?;
        if interface.id != tuple_def {
            return None;
        }

        // Return an empty witness - Tuple is a marker interface with no requirements
        Some(ConformanceWitness::default())
    }

    fn build_closure_witness(
        &self,
        type_head: TypeHead,
        interface: InterfaceReference<'ctx>,
    ) -> Option<ConformanceWitness<'ctx>> {
        let TypeHead::Closure(closure_def_id) = type_head else {
            return None;
        };

        let gcx = self.context;
        let captures = gcx.get_closure_captures(closure_def_id)?;
        let closure_kind = captures.kind;

        let (required_kind, synth_kind) = self.closure_interface_kind(interface.id)?;
        if !self.closure_kind_allows(closure_kind, required_kind) {
            return None;
        }

        let sig = gcx.get_signature(closure_def_id);
        if sig.inputs.is_empty() {
            return None;
        }

        let inputs: Vec<Ty<'ctx>> = sig.inputs.iter().skip(1).map(|p| p.ty).collect();
        let inputs_list = gcx.store.interners.intern_ty_list(inputs.clone());
        let output = sig.output;
        let closure_ty = Ty::new(
            TyKind::Closure {
                closure_def_id,
                captured_generics: &[],
                inputs: inputs_list,
                output,
                kind: closure_kind,
            },
            gcx,
        );

        let args_ty = match inputs_list.len() {
            0 => gcx.types.void,
            1 => inputs_list[0],
            _ => Ty::new(TyKind::Tuple(inputs_list), gcx),
        };

        let mut args_iter = interface.arguments.iter();
        let self_arg = match args_iter.next() {
            Some(GenericArgument::Type(ty)) => *ty,
            _ => return None,
        };
        if self_arg != closure_ty {
            return None;
        }
        let args_arg = match args_iter.next() {
            Some(GenericArgument::Type(ty)) => *ty,
            _ => return None,
        };
        let output_arg = match args_iter.next() {
            Some(GenericArgument::Type(ty)) => *ty,
            _ => return None,
        };
        if args_iter.next().is_some() {
            return None;
        }
        if args_arg != args_ty || output_arg != output {
            return None;
        }

        let requirements = gcx.get_interface_requirements(interface.id)?;
        let mut witness = ConformanceWitness::default();

        for method in &requirements.methods {
            let args_template = GenericsBuilder::identity_for_item(gcx, method.id);
            let info = crate::sema::tycheck::derive::SyntheticMethodInfo {
                kind: synth_kind,
                self_ty: closure_ty,
                interface_id: interface.id,
                interface_args: interface.arguments,
                interface_bindings: interface.bindings,
                method_id: method.id,
                method_name: method.name,
                syn_id: None,
            };
            gcx.register_synthetic_method(type_head, method.id, method.name, info);
            witness.method_witnesses.insert(
                method.id,
                MethodWitness {
                    implementation: MethodImplementation::Synthetic(synth_kind, None),
                    args_template,
                },
            );
        }

        witness.extension_id = None;
        Some(witness)
    }

    fn closure_interface_kind(
        &self,
        interface_id: DefinitionID,
    ) -> Option<(ClosureKind, SyntheticMethodKind)> {
        let gcx = self.context;
        let fn_id = gcx.std_interface_def(hir::StdInterface::Fn)?;
        let fn_mut_id = gcx.std_interface_def(hir::StdInterface::FnMut)?;
        let fn_once_id = gcx.std_interface_def(hir::StdInterface::FnOnce)?;

        if interface_id == fn_id {
            Some((ClosureKind::Fn, SyntheticMethodKind::ClosureCall))
        } else if interface_id == fn_mut_id {
            Some((ClosureKind::FnMut, SyntheticMethodKind::ClosureCallMut))
        } else if interface_id == fn_once_id {
            Some((ClosureKind::FnOnce, SyntheticMethodKind::ClosureCallOnce))
        } else {
            None
        }
    }

    fn closure_kind_allows(&self, actual: ClosureKind, required: ClosureKind) -> bool {
        match required {
            ClosureKind::Fn => matches!(actual, ClosureKind::Fn),
            ClosureKind::FnMut => matches!(actual, ClosureKind::Fn | ClosureKind::FnMut),
            ClosureKind::FnOnce => true,
        }
    }
}

pub fn resolve_conformance_witness<'ctx>(
    context: Gcx<'ctx>,
    type_head: TypeHead,
    interface: InterfaceReference<'ctx>,
) -> Option<ConformanceWitness<'ctx>> {
    let actor = Actor::new(context);
    actor.resolve_conformance_witness(type_head, interface)
}

// Type witness lookup (stub - full implementation needs associated types)
impl<'ctx> Actor<'ctx> {
    fn find_type_witness(
        &self,
        type_head: TypeHead,
        assoc: &AssociatedTypeDefinition<'ctx>,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) -> Result<Ty<'ctx>, ConformanceError<'ctx>> {
        let gcx = self.context;
        // Look in the extension's package (where the implementation lives)
        let extension_pkg = record.extension.package();
        let alias_id = gcx.with_type_database(extension_pkg, |db| {
            db.alias_table
                .by_type
                .get(&type_head)
                .and_then(|bucket| bucket.aliases.get(&assoc.name))
                .map(|(id, _)| *id)
        });

        if let Some(alias_id) = alias_id {
            return Ok(gcx.get_alias_type(alias_id));
        }

        if let Some(default_ty) = assoc.default_type {
            return Ok(default_ty);
        }

        Err(ConformanceError::MissingAssociatedType {
            name: assoc.name,
        })
    }
}

// Method witness lookup
impl<'ctx> Actor<'ctx> {
    fn find_method_witness(
        &self,
        type_head: TypeHead,
        requirement: &InterfaceMethodRequirement<'ctx>,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
        type_witnesses: &FxHashMap<DefinitionID, Ty<'ctx>>,
    ) -> Result<MethodWitness<'ctx>, ConformanceError<'ctx>> {
        // RUST-STYLE CONFORMANCE:
        // Look up candidates ONLY from the specific impl block (record.extension)
        // NOT from all impls (inherent or other traits)

        let impl_id = record.extension;
        let extension_pkg = impl_id.package();

        // The interface ID is the one we're checking conformance for
        let interface_id = record.interface.id;

        // Look up in trait_methods with (interface_id, name) key
        let candidates: Vec<DefinitionID> = self
            .context
            .with_type_database(extension_pkg, |db| {
                db.type_head_to_members
                    .get(&type_head)
                    .and_then(|idx| {
                        let key = (interface_id, requirement.name);
                        idx.trait_methods.get(&key)
                    })
                    .map(|set| {
                        // Filter to only methods from THIS specific impl block
                        set.members
                            .iter()
                            .filter(|&&id| self.context.definition_parent(id) == Some(impl_id))
                            .cloned()
                            .collect()
                    })
            })
            .unwrap_or_default();

        // Find matching signature
        for candidate in candidates {
            if self.signatures_match(requirement.id, candidate, record, type_witnesses) {
                let args_template = self.build_method_args_template(
                    requirement.id,
                    candidate,
                    record,
                    type_witnesses,
                );

                // Check if this candidate is actually a registered synthetic method
                if let Some(info) = self.context.get_synthetic_method(type_head, candidate) {
                    return Ok(MethodWitness {
                        implementation: MethodImplementation::Synthetic(info.kind, info.syn_id),
                        args_template,
                    });
                }

                return Ok(MethodWitness {
                    implementation: MethodImplementation::Concrete(candidate),
                    args_template,
                });
            }
        }

        // Check for default implementation
        if !requirement.is_required {
            let args_template = GenericsBuilder::identity_for_item(self.context, requirement.id);
            return Ok(MethodWitness {
                implementation: MethodImplementation::Default(requirement.id),
                args_template,
            });
        }

        // Try to synthesize if this is a derivable interface via inline conformance
        if record.is_inline {
            // Get the self type for synthesis
            let self_ty = match type_head {
                TypeHead::Nominal(id) => self.context.get_type(id),
                _ => {
                    return Err(ConformanceError::MissingMethod {
                        name: requirement.name,
                        signature: requirement.signature,
                    });
                }
            };

            let args_template = GenericsBuilder::identity_for_item(self.context, requirement.id);

            if let Some(synthesized) = crate::sema::tycheck::derive::try_synthesize_method(
                self.context,
                type_head,
                self_ty,
                record.interface.id,
                record.interface.arguments,
                requirement.name,
                requirement.id,
                args_template,
            ) {
                return Ok(synthesized.witness);
            }
        }

        Err(ConformanceError::MissingMethod {
            name: requirement.name,
            signature: requirement.signature,
        })
    }
}

// Constant witness lookup (stub)
impl<'ctx> Actor<'ctx> {
    fn find_constant_witness(
        &self,
        _type_head: TypeHead,
        requirement: &InterfaceConstantRequirement<'ctx>,
        _record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) -> Result<DefinitionID, ConformanceError<'ctx>> {
        // TODO: Implement constant lookup
        // For now, check if there's a default
        if requirement.default.is_some() {
            return Ok(requirement.id);
        }

        Err(ConformanceError::MissingConstant {
            name: requirement.name,
            ty: requirement.ty,
        })
    }
}

// Signature matching
impl<'ctx> Actor<'ctx> {
    fn signatures_match(
        &self,
        interface_fn_id: DefinitionID,
        impl_fn_id: DefinitionID,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
        type_witnesses: &FxHashMap<DefinitionID, Ty<'ctx>>,
    ) -> bool {
        let gcx = self.context;

        let interface_sig = gcx.get_signature(interface_fn_id);
        let impl_sig = gcx.get_signature(impl_fn_id);

        // 1. Quick shape check (arity, labels, variadic)
        if !interface_sig.same_shape(impl_sig) {
            return false;
        }

        // 2. Generics arity check
        let interface_generics = gcx.generics_of(interface_fn_id);
        let impl_generics = gcx.generics_of(impl_fn_id);
        if interface_generics.parameters.len() != impl_generics.parameters.len() {
            return false;
        }

        // 3. Substitute Self and interface args into requirement signature
        let interface_fn_ty = self.labeled_signature_to_ty(interface_sig);
        let substituted_ty = self.substitute_with_args(interface_fn_ty, record.interface.arguments);
        let substituted_ty = self.substitute_projection_witnesses(substituted_ty, type_witnesses);

        let impl_fn_ty = self.labeled_signature_to_ty(impl_sig);

        // 4. Freshen each signature separately so method-local generics are
        //    compared positionally (first generic matches first generic)
        let mut interface_freshener = crate::sema::tycheck::freshen::TypeFreshener::new(gcx);
        let fresh_interface_ty = interface_freshener.freshen(substituted_ty);

        let mut impl_freshener = crate::sema::tycheck::freshen::TypeFreshener::new(gcx);
        let fresh_impl_ty = impl_freshener.freshen(impl_fn_ty);

        fresh_interface_ty == fresh_impl_ty
    }

    fn build_method_args_template(
        &self,
        interface_method_id: DefinitionID,
        impl_method_id: DefinitionID,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
        type_witnesses: &FxHashMap<DefinitionID, Ty<'ctx>>,
    ) -> GenericArguments<'ctx> {
        let gcx = self.context;
        let impl_generics = gcx.generics_of(impl_method_id);
        if impl_generics.is_empty() {
            return gcx.store.interners.intern_generic_args(Vec::new());
        }

        let interface_sig = gcx.get_signature(interface_method_id);
        let interface_fn_ty = self.labeled_signature_to_ty(interface_sig);
        let substituted_interface_ty =
            self.substitute_with_args(interface_fn_ty, record.interface.arguments);
        let substituted_interface_ty =
            self.substitute_projection_witnesses(substituted_interface_ty, type_witnesses);

        let impl_sig = gcx.get_signature(impl_method_id);
        let impl_fn_ty = self.labeled_signature_to_ty(impl_sig);

        let icx = Rc::new(InferCtx::new(gcx));
        let span = record.location;
        let fresh_impl_args = icx.fresh_args_for_def(impl_method_id, span);
        let impl_fn_ty = instantiate_ty_with_args(gcx, impl_fn_ty, fresh_impl_args);

        let unifier = TypeUnifier::new(icx.clone());
        if unifier.unify(impl_fn_ty, substituted_interface_ty).is_err() {
            return GenericsBuilder::identity_for_item(gcx, impl_method_id);
        }

        let resolved: Vec<_> = fresh_impl_args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => {
                    GenericArgument::Type(icx.resolve_vars_if_possible(*ty))
                }
                GenericArgument::Const(c) => {
                    GenericArgument::Const(icx.resolve_const_if_possible(*c))
                }
            })
            .collect();

        gcx.store.interners.intern_generic_args(resolved)
    }

    fn labeled_signature_to_ty(&self, sig: &LabeledFunctionSignature<'ctx>) -> Ty<'ctx> {
        let gcx = self.context;
        let inputs: Vec<_> = sig.inputs.iter().map(|p| p.ty).collect();
        let inputs = gcx.store.interners.intern_ty_list(inputs);
        Ty::new(
            crate::sema::models::TyKind::FnPointer {
                inputs,
                output: sig.output,
            },
            gcx,
        )
    }

    fn substitute_with_args(
        &self,
        ty: Ty<'ctx>,
        args: crate::sema::models::GenericArguments<'ctx>,
    ) -> Ty<'ctx> {
        if args.is_empty() {
            return ty;
        }

        let mut substitutor = ArgSubstitutor {
            gcx: self.context,
            args,
        };
        ty.fold_with(&mut substitutor)
    }

    fn substitute_projection_witnesses(
        &self,
        ty: Ty<'ctx>,
        type_witnesses: &FxHashMap<DefinitionID, Ty<'ctx>>,
    ) -> Ty<'ctx> {
        if type_witnesses.is_empty() {
            return ty;
        }

        let mut substitutor = ProjectionSubstitutor {
            gcx: self.context,
            type_witnesses,
        };
        ty.fold_with(&mut substitutor)
    }
}

// Error emission
impl<'ctx> Actor<'ctx> {
    fn emit_conformance_errors(
        &self,
        type_head: TypeHead,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
        errors: Vec<ConformanceError<'ctx>>,
        required_by: Option<InterfaceReference<'ctx>>,
    ) {
        let gcx = self.context;
        let type_name = type_head.format(gcx);
        let interface_name = record.interface.format(gcx);

        // Emit different error message for superinterface requirements
        let error_msg = if let Some(requiring_interface) = required_by {
            let requiring_name = requiring_interface.format(gcx);
            format!(
                "interface '{}' requires type '{}' to conform to '{}'",
                requiring_name, type_name, interface_name
            )
        } else {
            format!(
                "type '{}' does not satisfy requirements for interface '{}'",
                type_name, interface_name
            )
        };

        gcx.dcx().emit_error(error_msg, Some(record.location));

        // Only emit detailed errors if this is a direct conformance (not a superinterface requirement)
        // For superinterface requirements, the user needs to add a separate impl block,
        // and the detailed errors will be shown when they implement that interface.
        if required_by.is_none() {
            for error in errors {
                let msg = match error {
                    ConformanceError::MissingMethod { name, signature } => {
                        let sig_ty = self.labeled_signature_to_ty(signature);
                        format!(
                            "missing required method '{}' with signature '{}'",
                            name,
                            sig_ty.format(gcx)
                        )
                    }
                    ConformanceError::MissingConstant { name, ty } => {
                        format!(
                            "missing required constant '{}' of type '{}'",
                            name,
                            ty.format(gcx)
                        )
                    }
                    ConformanceError::MissingAssociatedType { name } => {
                        format!("missing required associated type '{}'", name)
                    }
                };
                gcx.dcx().emit_info(msg, Some(record.location));
            }
        }
    }
}

// Substitutor for generic arguments
struct ArgSubstitutor<'ctx> {
    gcx: Gcx<'ctx>,
    args: crate::sema::models::GenericArguments<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for ArgSubstitutor<'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        use crate::sema::models::TyKind;
        use crate::sema::tycheck::fold::TypeSuperFoldable;

        match ty.kind() {
            TyKind::Parameter(param) => {
                // Substitute if we have an arg for this index
                if let Some(arg) = self.args.get(param.index as usize) {
                    if let crate::sema::models::GenericArgument::Type(sub_ty) = arg {
                        return *sub_ty;
                    }
                }
                ty
            }
            _ => ty.super_fold_with(self),
        }
    }
}

struct ProjectionSubstitutor<'ctx, 'w> {
    gcx: Gcx<'ctx>,
    type_witnesses: &'w FxHashMap<DefinitionID, Ty<'ctx>>,
}

impl<'ctx> TypeFolder<'ctx> for ProjectionSubstitutor<'ctx, '_> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Alias {
                kind: AliasKind::Projection,
                def_id,
                ..
            } => {
                if let Some(witness_ty) = self.type_witnesses.get(&def_id) {
                    // Return the witness type directly - it's already the concrete type
                    // assigned in the extension (e.g., `type Element = T`).
                    // We don't instantiate with projection args because those represent
                    // the Self type, not arguments to the witness.
                    // Continue folding to resolve any nested projections within the witness type.
                    return witness_ty.fold_with(self);
                }
                ty.super_fold_with(self)
            }
            _ => ty.super_fold_with(self),
        }
    }
}
