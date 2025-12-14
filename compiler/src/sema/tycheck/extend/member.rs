use crate::{
    compile::context::{GlobalContext, MemberSet, TypeMemberIndex},
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
};
use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn collect_extension_member(
        &mut self,
        extension_id: DefinitionID,
        decl: &hir::AssociatedDeclaration,
    ) {
        let Some(head) = self.context.get_extension_type_head(extension_id) else {
            return;
        };

        match &decl.kind {
            hir::AssociatedDeclarationKind::Function(function) => {
                let has_self = function
                    .signature
                    .prototype
                    .inputs
                    .first()
                    .is_some_and(|param| param.name.symbol.as_str() == "self");
                self.collect_function(head, decl.id, decl.identifier, has_self);
            }
            hir::AssociatedDeclarationKind::Operator(op) => {
                self.collect_operator(head, decl.id, decl.identifier, op.kind);
            }
            _ => todo!("associated declaration kind in extension member collection"),
        }
    }

    fn collect_function(
        &mut self,
        head: crate::sema::resolve::models::TypeHead,
        def_id: DefinitionID,
        ident: crate::span::Identifier,
        has_self: bool,
    ) {
        let fingerprint = self.fingerprint_for(def_id);
        self.context.with_session_type_database(|db| {
            let index: &mut TypeMemberIndex = db.type_head_to_members.entry(head).or_default();
            let set: &mut MemberSet = if has_self {
                index.instance_functions.entry(ident.symbol).or_default()
            } else {
                index.static_functions.entry(ident.symbol).or_default()
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

    fn collect_operator(
        &mut self,
        head: crate::sema::resolve::models::TypeHead,
        def_id: DefinitionID,
        ident: crate::span::Identifier,
        kind: hir::OperatorKind,
    ) {
        let fingerprint = self.fingerprint_for(def_id);
        self.context.with_session_type_database(|db| {
            let index: &mut TypeMemberIndex = db.type_head_to_members.entry(head).or_default();
            let set: &mut MemberSet = index.operators.entry(kind).or_default();

            if let Some(previous) = set.fingerprints.insert(fingerprint, def_id) {
                let msg = format!("invalid redeclaration of operator '{:?}'", kind);
                self.context.dcx().emit_error(msg, Some(ident.span));

                let prev_ident = self.context.definition_ident(previous);
                let msg = format!("'{:?}' operator signature is initially defined here", kind);
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
    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        match context {
            hir::AssocContext::Interface(..) => return,
            hir::AssocContext::Extension(extension_id) => {
                self.collect_extension_member(extension_id, node);
            }
        }
    }
}
