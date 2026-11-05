//! Preserve native capabilities separately from the generated method names.
use crate::{
    compile::context::{Gcx, NativeSubscriptEntry},
    hir::{self, HirVisitor},
};

pub fn run(package: &hir::Package, gcx: Gcx<'_>) {
    struct Collector<'ctx>(Gcx<'ctx>);
    impl HirVisitor for Collector<'_> {
        fn visit_assoc_declaration(
            &mut self,
            declaration: &hir::AssociatedDeclaration,
            context: hir::AssocContext,
        ) {
            if let hir::AssociatedDeclarationKind::Subscript(subscript) = &declaration.kind {
                self.0.with_session_type_database(|db| {
                    db.native_subscripts.insert(
                        declaration.id,
                        NativeSubscriptEntry {
                            getter: subscript.getter_id,
                            setter: subscript.setter_id,
                            address: subscript.address_id,
                            getter_is_default: subscript.getter_is_default,
                            setter_is_default: subscript.setter_is_default,
                            is_override: subscript.is_override,
                            is_final: subscript.is_final,
                        },
                    );
                });
            }
            hir::walk_assoc_declaration(self, declaration, context);
        }
    }
    hir::walk_package(&mut Collector(gcx), package);
}
