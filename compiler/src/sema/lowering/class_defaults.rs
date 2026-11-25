//! Give an adopted default an exact body identity. Calling its requirement
//! normally would select the class witness again, recursively entering its
//! forwarding method instead of executing the interface's default body.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, DefinitionKind},
    sema::models::{SyntheticDefinition, SyntheticDefinitionKind, Ty},
};

#[path = "class_default_adapters.rs"]
mod adapters;

/// Receiver-only class upcasts do not authorize reinterpreting arbitrary
/// invariant Self slots or nested values. Shared/owned direct Self inputs are
/// safe; a direct owned Self result additionally needs a dynamic-class proof.
pub(crate) fn class_interface_signature_supported<'ctx>(
    gcx: Gcx<'ctx>,
    signature: &crate::sema::models::LabeledFunctionSignature<'ctx>,
) -> bool {
    use crate::sema::tycheck::{
        utils::normalize_aliases,
        visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
    };
    struct HasSelf<'ctx>(Gcx<'ctx>);
    impl<'ctx> TypeVisitor<'ctx> for HasSelf<'ctx> {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            let ty = normalize_aliases(self.0, ty);
            // Associated outputs are fixed by the declaring conformance.
            // Their receiver argument is not a dynamic Self storage position;
            // the checked witness supplies the concrete associated binding.
            if matches!(
                ty.kind(),
                crate::sema::models::TyKind::Alias {
                    kind: crate::sema::models::AliasKind::Projection,
                    ..
                }
            ) {
                return false;
            }
            ty == self.0.types.self_type_parameter || ty.super_visit_with(self)
        }
    }
    let contains_self = |ty: Ty<'ctx>| ty.visit_with(&mut HasSelf(gcx));
    let instance = signature
        .inputs
        .first()
        .is_some_and(|input| gcx.symbol_text(input.name).as_str() == "self");
    signature
        .inputs
        .iter()
        .skip(usize::from(instance))
        .all(|input| {
            let ty = normalize_aliases(gcx, input.ty);
            ty == gcx.types.self_type_parameter || !contains_self(ty)
        })
        && ((instance && normalize_aliases(gcx, signature.output) == gcx.types.self_type_parameter)
            || !contains_self(signature.output))
}

impl<'ctx> Gcx<'ctx> {
    /// Exact-body aliases resolve once to the original item instance. No MIR
    /// cloning, certificate copying or generic-coordinate rebasing is needed:
    /// the selected instance is the already checked original body itself.
    pub(crate) fn class_default_source(self, id: DefinitionID) -> Option<DefinitionID> {
        match self.store.synthetic_definitions.borrow().get(&id)?.kind {
            SyntheticDefinitionKind::ClassDefaultBody { source } => Some(source),
            _ => None,
        }
    }

    pub(crate) fn class_default_body(self, source: DefinitionID) -> Option<DefinitionID> {
        let interface = self.definition_parent(source)?;
        if self.try_definition_kind(interface) != Some(DefinitionKind::Interface) {
            return None;
        }
        let requirements = self.get_interface_requirements(interface)?;
        if !requirements
            .methods
            .iter()
            .any(|method| method.id == source && !method.is_required)
            && !requirements
                .properties
                .iter()
                .any(|property| property.getter_id == source && !property.getter_is_required)
        {
            return None;
        }
        if let Some(id) =
            self.store
                .synthetic_definitions
                .borrow()
                .iter()
                .find_map(|(id, definition)| {
                    (id.package() == self.package_index()
                        && definition.kind == SyntheticDefinitionKind::ClassDefaultBody { source })
                    .then_some(*id)
                })
        {
            return Some(id);
        }
        let signature = self.get_signature(source);
        let id = self.allocate_synthetic_id(self.package_index());
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::ClassDefaultBody { source },
                name: self.intern_symbol(&format!(
                    "$class_default_body${}${}",
                    source.package().index(),
                    source.index().raw()
                )),
                generics: self.generics_of(source),
                signature,
                span: self.definition_ident(source).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.update_constraints(id, self.constraints_of(source));
        if self.definition_is_async(source) {
            self.cache_async_body_output(id, self.function_body_output(source));
        }
        if self.definition_is_unsafe(source) {
            self.with_session_type_database(|database| {
                database.def_to_unsafe.insert(id);
            });
        }
        Some(id)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn exact_default_identity_bypasses_witness_selection_without_changing_the_signature() {
        crate::test_support::analyze_script(
            r#"
interface Readable {
    func read() -> int32 { 7 }
    func delayed() async -> int32 { 7 }
    func required() -> int32
}
struct Counter {}
conform Counter to Readable {
    func read() -> int32 { 9 }
    func required() -> int32 { 11 }
}
func main() {}
"#,
            |package, gcx| {
                let interface = package.root.declarations[0].id;
                let counter = gcx.get_type(package.root.declarations[1].id);
                let requirements = gcx.get_interface_requirements(interface).unwrap();
                let method = requirements
                    .methods
                    .iter()
                    .find(|method| gcx.symbol_text(method.name).as_str() == "read")
                    .unwrap()
                    .id;
                let alias = gcx.class_default_body(method).unwrap();
                assert_eq!(gcx.class_default_body(method), Some(alias));
                assert_eq!(gcx.get_type(alias), gcx.get_type(method));
                assert!(
                    gcx.get_signature(alias)
                        .same_shape(gcx.get_signature(method))
                );
                assert!(std::ptr::eq(
                    gcx.generics_of(alias),
                    gcx.generics_of(method)
                ));
                let arguments = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(counter)]);
                let normal = crate::specialize::resolve_instance(gcx, method, arguments);
                assert_ne!(
                    normal.def_id(),
                    method,
                    "normal calls select Counter's conformance"
                );
                let exact = crate::specialize::resolve_instance(gcx, alias, arguments);
                assert_eq!(
                    exact.def_id(),
                    method,
                    "the alias names the body rather than reentering its class witness"
                );
                let asynchronous = requirements
                    .methods
                    .iter()
                    .find(|method| gcx.symbol_text(method.name).as_str() == "delayed")
                    .unwrap()
                    .id;
                let async_alias = gcx.class_default_body(asynchronous).unwrap();
                assert!(gcx.definition_is_async(async_alias));
                assert_eq!(
                    gcx.function_body_output(async_alias),
                    gcx.function_body_output(asynchronous)
                );
                let required = requirements
                    .methods
                    .iter()
                    .find(|method| gcx.symbol_text(method.name).as_str() == "required")
                    .unwrap()
                    .id;
                assert_eq!(gcx.class_default_body(required), None);
            },
        );
    }
}

/// Default expressions have synthetic signatures but no HIR function declaration.
/// Persist their signatures so imported callers can instantiate the provider.
pub(crate) fn cache_provider_signatures(gcx: crate::compile::context::Gcx<'_>) {
    let providers: Vec<_> = gcx
        .store
        .default_value_exprs
        .borrow()
        .keys()
        .copied()
        .filter(|id| id.package() == gcx.package_index())
        .collect();
    for id in providers {
        gcx.cache_signature(id, gcx.get_signature(id).clone());
    }
}
