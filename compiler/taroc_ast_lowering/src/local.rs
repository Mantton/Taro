use super::package::Actor;

impl Actor<'_> {
    pub fn lower_local(&mut self, local: taroc_ast::Local) -> taroc_hir::Local {
        taroc_hir::Local {
            id: self.next(),
            mutability: self.lower_mutability(local.mutability),
            pattern: self.lower_binding_pattern(local.pattern),
            ty: self.lower_optional(local.ty, |a, t| a.lower_type(t)),
            initializer: self.lower_optional(local.initializer, |a, e| a.lower_expression(e)),
            source: local.source,
        }
    }
}
