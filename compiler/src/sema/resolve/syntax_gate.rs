//! Stop parsed future syntax before it can acquire incomplete runtime semantics.
//!
//! This pass runs after configuration filtering and before symbol collection.
//! Remove each check only in the story that supplies its complete semantics.
use crate::{
    ast::{self, AstVisitor},
    diagnostics::DiagCtx,
    error::CompileResult,
};

pub(super) fn check_package(package: &ast::Package, dcx: &DiagCtx) -> CompileResult<()> {
    let mut checker = Checker { dcx };
    checker.visit_package(package);
    dcx.ok()
}

struct Checker<'a> {
    dcx: &'a DiagCtx,
}

impl AstVisitor for Checker<'_> {
    fn visit_assoc_declaration(
        &mut self,
        node: &ast::AssociatedDeclaration,
        context: ast::AssocContext,
    ) {
        let feature = match &node.kind {
            ast::AssociatedDeclarationKind::Initializer(_)
                if matches!(context, ast::AssocContext::Interface(_)) =>
            {
                Some("init declarations belong in the owning type's extension, not an interface")
            }
            _ => None,
        };
        if let Some(feature) = feature {
            self.dcx
                .emit_error(feature.into(), Some(node.identifier.span));
            return;
        }
        ast::walk_assoc_declaration(self, node, context);
    }

    fn visit_enum_variant(&mut self, node: &ast::Variant) {
        let fields = match &node.kind {
            ast::VariantKind::Unit => &[][..],
            ast::VariantKind::Tuple(fields) | ast::VariantKind::Struct(fields) => fields.as_slice(),
        };
        for field in fields {
            if field.default_value.is_some() {
                self.dcx.emit_error(
                    "enum payload fields do not support defaults".into(),
                    Some(field.identifier.span),
                );
            }
        }
        ast::walk_enum_variant(self, node);
    }

    fn visit_function(
        &mut self,
        id: ast::NodeID,
        node: &ast::Function,
        context: ast::FunctionContext,
    ) {
        if matches!(
            context,
            ast::FunctionContext::Assoc(ast::AssocContext::Interface(_))
        ) && (node.is_final || node.is_override)
        {
            self.dcx.emit_error(
                "final/override requires a class instance method".into(),
                Some(node.signature.span),
            );
        }
        ast::walk_function(self, id, node, context);
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn enum_payload_defaults_are_rejected_instead_of_silently_ignored() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "enum State { case value { count: int32 = 7 } }\nfunc main() { var state: State = .value(count: 9) }",
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("enum payload fields do not support defaults")),
            "{diagnostics:#?}"
        );
    }
}
