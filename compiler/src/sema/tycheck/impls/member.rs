use crate::{
    compile::context::{GlobalContext, MemberSet, TypeMemberIndex},
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
};
use rustc_hash::{FxHashMap, FxHasher};
use std::hash::{Hash, Hasher};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor {
        context,
        impl_interfaces: FxHashMap::default(),
    };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    /// Maps impl_id -> Option<interface_id> for quick lookup during member collection
    impl_interfaces: FxHashMap<DefinitionID, Option<DefinitionID>>,
}

impl<'ctx> Actor<'ctx> {
    fn collect_impl_member(&mut self, impl_id: DefinitionID, decl: &hir::AssociatedDeclaration) {
        let Some(head) = self.context.get_impl_type_head(impl_id) else {
            return;
        };

        // Check if this impl has an interface (trait impl vs inherent impl)
        let interface_id = self.impl_interfaces.get(&impl_id).copied().flatten();
        let _ = interface_id.is_some();

        match &decl.kind {
            hir::AssociatedDeclarationKind::Function(function) => {
                let has_self = function
                    .signature
                    .prototype
                    .inputs
                    .first()
                    .is_some_and(|param| param.name.symbol.as_str() == "self");
                self.collect_function(
                    head,
                    impl_id,
                    decl.id,
                    decl.identifier,
                    has_self,
                    interface_id,
                );
            }
            _ => {}
        }
    }

    fn collect_function(
        &mut self,
        head: crate::sema::resolve::models::TypeHead,
        _: DefinitionID,
        def_id: DefinitionID,
        ident: crate::span::Identifier,
        has_self: bool,
        interface_id: Option<DefinitionID>,
    ) {
        let fingerprint = self.fingerprint_for(def_id);
        self.context.with_session_type_database(|db| {
            let index: &mut TypeMemberIndex = db.type_head_to_members.entry(head).or_default();

            let set: &mut MemberSet = if let Some(interface_id) = interface_id {
                // Trait impl: store in trait_methods with (interface_id, name) key
                let key = (interface_id, ident.symbol);
                index.trait_methods.entry(key).or_default()
            } else {
                // Inherent impl: store in inherent_static or inherent_instance
                if has_self {
                    index.inherent_instance.entry(ident.symbol).or_default()
                } else {
                    index.inherent_static.entry(ident.symbol).or_default()
                }
            };

            if let Some(previous) = set.fingerprints.insert(fingerprint, def_id) {
                let msg = format!("invalid redeclaration of '{}'", ident.symbol.as_str());
                self.context.dcx().emit_error(msg, Some(ident.span));

                let prev_ident = self.context.definition_ident(previous);
                let msg = format!("'{}' is initially defined here", ident.symbol.as_str());
                self.context.dcx().emit_info(msg, Some(prev_ident.span));
                return;
            }

            set.members.push(def_id);
        });
    }

    fn fingerprint_for(&self, id: DefinitionID) -> u64 {
        let sig = self.context.get_signature(id);

        let mut hasher = FxHasher::default();
        sig.abi.hash(&mut hasher);
        sig.is_variadic.hash(&mut hasher);
        sig.inputs.len().hash(&mut hasher);
        for param in &sig.inputs {
            param.label.hash(&mut hasher);
            param.ty.hash(&mut hasher);
        }
        sig.output.hash(&mut hasher);
        hasher.finish()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        // Cache interface information for impl blocks
        if let hir::DeclarationKind::Impl(impl_node) = &declaration.kind {
            let interface_id = impl_node.interface.as_ref().and_then(|interface_ty| {
                // Extract interface ID from the type
                if let hir::TypeKind::Nominal(path) = &interface_ty.kind {
                    if let hir::ResolvedPath::Resolved(resolved) = path {
                        if let hir::Resolution::Definition(id, _) = resolved.resolution {
                            return Some(id);
                        }
                    }
                }
                None
            });
            self.impl_interfaces.insert(declaration.id, interface_id);
        }

        // Continue walking to visit children (especially associated declarations in impl blocks)
        hir::walk_declaration(self, declaration)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        match context {
            hir::AssocContext::Interface(..) => return,
            hir::AssocContext::Impl(impl_id) => {
                self.collect_impl_member(impl_id, node);
            }
        }
    }
}
