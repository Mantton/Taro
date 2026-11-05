//! Compiler-owned lazy static declarations and checked access capabilities.
//! Initializers are ordinary Native functions; access producers alone may
//! publish a reference to process-long storage after synchronized initialization.
use crate::{
    compile::context::Gcx,
    hir::DefinitionID,
    sema::models::{
        LabeledFunctionSignature, SyntheticDefinition, SyntheticDefinitionKind, Ty, TyKind,
    },
};

impl<'ctx> Gcx<'ctx> {
    pub(crate) fn static_initializer_function(self, storage: DefinitionID) -> DefinitionID {
        self.static_function(storage, false)
    }
    pub(crate) fn static_reference_function(self, storage: DefinitionID) -> DefinitionID {
        self.static_function(storage, true)
    }
    fn static_function(self, storage: DefinitionID, reference: bool) -> DefinitionID {
        let kind = if reference {
            SyntheticDefinitionKind::StaticReference { storage }
        } else {
            SyntheticDefinitionKind::StaticInitializer { storage }
        };
        if let Some(id) = self
            .store
            .synthetic_definitions
            .borrow()
            .iter()
            .find_map(|(id, definition)| (definition.kind == kind).then_some(*id))
        {
            return id;
        }
        // Imported initializers are always exported with their static. No
        // client may invent a replacement for a dependency's initializer body.
        assert!(
            reference || storage.package() == self.package_index(),
            "missing imported static initializer"
        );
        let id = self.allocate_synthetic_id(self.package_index());
        let output = if reference {
            Ty::new(TyKind::Reference(self.get_type(storage)), self)
        } else {
            self.get_type(storage)
        };
        let signature = self
            .store
            .arenas
            .function_signatures
            .alloc(LabeledFunctionSignature {
                inputs: vec![],
                output,
                is_variadic: false,
                abi: reference.then_some(crate::hir::Abi::Intrinsic),
            });
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind,
                name: self.intern_symbol(if reference {
                    "__staticReference"
                } else {
                    "__staticInitializer"
                }),
                generics: self.empty_generics_for_package(self.package_index()),
                signature,
                span: self.definition_ident(storage).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        id
    }
}

pub(crate) fn referenced_storage(gcx: Gcx<'_>, id: DefinitionID) -> Option<DefinitionID> {
    let definitions = gcx.store.synthetic_definitions.borrow();
    let definition = definitions.get(&id)?;
    let SyntheticDefinitionKind::StaticReference { storage } = definition.kind else {
        return None;
    };
    let signature = definition.signature;
    (signature.inputs.is_empty()
        && signature.abi == Some(crate::hir::Abi::Intrinsic)
        && !signature.is_variadic
        && definition.generics.total_count() == 0
        && matches!(signature.output.kind(), TyKind::Reference(inner)
            if inner == gcx.get_type(storage)))
    .then_some(storage)
}

#[cfg(test)]
mod tests {
    #[test]
    fn runtime_initializers_accept_initialized_storage_but_not_views_or_suspension() {
        for source in [
            "static var value: int32 = makeValue()\nfunc makeValue() -> int32 { 7 }\nfunc main() {}",
            "class Document { value: int32 }\nextend Document { init() { self.value = 7 }; }\nstatic var document: Document = Document()\nfunc main() {}",
        ] {
            let errors = crate::test_support::analyze_language_item_script(source, false, &[]);
            assert!(errors.is_empty(), "{errors:#?}");
        }
        let errors = crate::test_support::analyze_language_item_script(
            "func value() async -> int32 { 7 }\nstatic var saved: int32 = await value()\nfunc main() {}",
            false,
            &[],
        );
        assert!(!errors.is_empty(), "static initialization cannot suspend");
    }
}
