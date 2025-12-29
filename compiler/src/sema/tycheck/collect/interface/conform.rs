use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, OperatorKind},
    sema::{
        models::{
            AssociatedTypeDefinition, ConformanceWitness, GenericArgument, GenericArguments,
            InterfaceConstantRequirement, InterfaceDefinition, InterfaceMethodRequirement,
            InterfaceOperatorRequirement, InterfaceReference, InterfaceRequirements,
            LabeledFunctionSignature, Ty,
        },
        resolve::models::TypeHead,
        tycheck::fold::{TypeFoldable, TypeFolder},
    },
    span::Symbol,
};
use rustc_hash::FxHashSet;

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
    MissingOperator {
        kind: OperatorKind,
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

        let mut seen: FxHashSet<(TypeHead, InterfaceReference<'ctx>)> = FxHashSet::default();

        for (type_head, records) in conformances {
            for record in &records {
                self.check_conformance(type_head, record);

                // Also validate superface requirements, but defer witness creation until needed.
                for iface in self.collect_interface_with_supers(record.interface).into_iter().skip(1) {
                    if !seen.insert((type_head, iface)) {
                        continue;
                    }

                    let mut derived = *record;
                    derived.interface = iface;
                    self.validate_conformance(type_head, &derived);
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
                self.emit_conformance_errors(type_head, record, errors);
            }
        }
    }

    fn validate_conformance(
        &self,
        type_head: TypeHead,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) {
        if let Err(errors) = self.build_witness(type_head, record) {
            self.emit_conformance_errors(type_head, record, errors);
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
        let mut errors = Vec::new();

        // 1. Check associated types (stub for now)
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
            match self.find_method_witness(type_head, method, record) {
                Ok(id) => {
                    witness.method_witnesses.insert(method.id, id);
                }
                Err(e) => errors.push(e),
            }
        }

        // 3. Check operators
        for op in &requirements.operators {
            match self.find_operator_witness(type_head, op, record) {
                Ok(id) => {
                    witness.operator_witnesses.insert(op.kind, id);
                }
                Err(e) => errors.push(e),
            }
        }

        // 4. Check constants (stub for now)
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
                db.interface_requirements.get(&interface_id).copied()
            })
    }

    fn interface_definition(
        &self,
        interface_id: DefinitionID,
    ) -> Option<&'ctx InterfaceDefinition<'ctx>> {
        self.context.with_type_database(interface_id.package(), |db| {
            db.def_to_iface_def.get(&interface_id).copied()
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

        let interned = self.context.store.interners.intern_generic_args(new_args);
        InterfaceReference {
            id: template.id,
            arguments: interned,
        }
    }

    fn resolve_conformance_witness(
        &self,
        type_head: TypeHead,
        interface: InterfaceReference<'ctx>,
    ) -> Option<ConformanceWitness<'ctx>> {
        if let Some(witness) = self.context.with_session_type_database(|db| {
            db.conformance_witnesses
                .get(&(type_head, interface))
                .cloned()
        }) {
            return Some(witness);
        }

        let records = self.context.with_session_type_database(|db| {
            db.conformances
                .get(&type_head)
                .cloned()
                .unwrap_or_default()
        });

        for record in records {
            if record.interface == interface {
                if let Ok(witness) = self.build_witness(type_head, &record) {
                    self.store_witness(type_head, interface, witness.clone());
                    return Some(witness);
                }
                return None;
            }

            for iface in self.collect_interface_with_supers(record.interface).into_iter().skip(1) {
                if iface != interface {
                    continue;
                }

                let mut derived = record;
                derived.interface = iface;
                if let Ok(witness) = self.build_witness(type_head, &derived) {
                    self.store_witness(type_head, interface, witness.clone());
                    return Some(witness);
                }
                return None;
            }
        }

        None
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
        _record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) -> Result<Ty<'ctx>, ConformanceError<'ctx>> {
        let gcx = self.context;
        let alias_id = gcx.with_session_type_database(|db| {
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

        Err(ConformanceError::MissingAssociatedType { name: assoc.name })
    }
}

// Method witness lookup
impl<'ctx> Actor<'ctx> {
    fn find_method_witness(
        &self,
        type_head: TypeHead,
        requirement: &InterfaceMethodRequirement<'ctx>,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) -> Result<DefinitionID, ConformanceError<'ctx>> {
        // Look up candidates in type's member index
        let candidates = self
            .context
            .with_session_type_database(|db| {
                db.type_head_to_members
                    .get(&type_head)
                    .and_then(|idx| idx.instance_functions.get(&requirement.name))
                    .map(|set| set.members.clone())
            })
            .unwrap_or_default();

        // Find matching signature
        for candidate in candidates {
            if self.signatures_match(requirement.id, candidate, record) {
                return Ok(candidate);
            }
        }

        // Check for default implementation
        if !requirement.is_required {
            return Ok(requirement.id);
        }

        Err(ConformanceError::MissingMethod {
            name: requirement.name,
            signature: requirement.signature,
        })
    }
}

// Operator witness lookup
impl<'ctx> Actor<'ctx> {
    fn find_operator_witness(
        &self,
        type_head: TypeHead,
        requirement: &InterfaceOperatorRequirement<'ctx>,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) -> Result<DefinitionID, ConformanceError<'ctx>> {
        // Look up candidates in type's operator index
        let candidates = self
            .context
            .with_session_type_database(|db| {
                db.type_head_to_members
                    .get(&type_head)
                    .and_then(|idx| idx.operators.get(&requirement.kind))
                    .map(|set| set.members.clone())
            })
            .unwrap_or_default();

        // Find matching signature
        for candidate in candidates {
            if self.operator_signatures_match(requirement, candidate, record) {
                return Ok(candidate);
            }
        }

        // Operators always need explicit implementation
        Err(ConformanceError::MissingOperator {
            kind: requirement.kind,
            signature: requirement.signature,
        })
    }

    fn operator_signatures_match(
        &self,
        requirement: &InterfaceOperatorRequirement<'ctx>,
        candidate_id: DefinitionID,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
    ) -> bool {
        let gcx = self.context;
        let interface_sig = requirement.signature;
        let impl_sig = gcx.get_signature(candidate_id);

        // Operators are label-agnostic, only check arity and variadic
        if interface_sig.is_variadic != impl_sig.is_variadic
            || interface_sig.inputs.len() != impl_sig.inputs.len()
        {
            return false;
        }

        // Substitute Self and interface args into requirement signature
        let interface_fn_ty = self.labeled_signature_to_ty(interface_sig);
        let substituted_ty = self.substitute_with_args(interface_fn_ty, record.interface.arguments);
        let impl_fn_ty = self.labeled_signature_to_ty(impl_sig);

        // Freshen and compare
        let mut freshener = crate::sema::tycheck::freshen::TypeFreshener::new(gcx);
        let fresh_interface_ty = freshener.freshen(substituted_ty);
        let fresh_impl_ty = freshener.freshen(impl_fn_ty);

        fresh_interface_ty == fresh_impl_ty
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

        let impl_fn_ty = self.labeled_signature_to_ty(impl_sig);

        // 4. Freshen and compare
        let mut freshener = crate::sema::tycheck::freshen::TypeFreshener::new(gcx);
        let fresh_interface_ty = freshener.freshen(substituted_ty);
        let fresh_impl_ty = freshener.freshen(impl_fn_ty);

        fresh_interface_ty == fresh_impl_ty
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
}

// Error emission
impl<'ctx> Actor<'ctx> {
    fn emit_conformance_errors(
        &self,
        type_head: TypeHead,
        record: &crate::sema::models::ConformanceRecord<'ctx>,
        errors: Vec<ConformanceError<'ctx>>,
    ) {
        let gcx = self.context;
        let type_name = type_head.format(gcx);
        let interface_name = record.interface.format(gcx);

        gcx.dcx().emit_error(
            format!(
                "type '{}' does not satisfy requirements for interface '{}'",
                type_name, interface_name
            ),
            Some(record.location),
        );

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
                ConformanceError::MissingOperator { kind, signature } => {
                    let sig_ty = self.labeled_signature_to_ty(signature);
                    format!(
                        "missing required operator '{:?}' with signature '{}'",
                        kind,
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
