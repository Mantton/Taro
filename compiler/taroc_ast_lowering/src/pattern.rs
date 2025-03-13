use super::package::Actor;

impl Actor<'_> {
    pub fn lower_binding_pattern(
        &mut self,
        pat: taroc_ast::BindingPattern,
    ) -> taroc_hir::BindingPattern {
        taroc_hir::BindingPattern {
            id: self.next(),
            span: pat.span,
            kind: self.lower_binding_pattern_kind(pat.kind),
        }
    }

    fn lower_binding_pattern_kind(
        &mut self,
        kind: taroc_ast::BindingPatternKind,
    ) -> taroc_hir::BindingPatternKind {
        match kind {
            taroc_ast::BindingPatternKind::Wildcard => taroc_hir::BindingPatternKind::Wildcard,
            taroc_ast::BindingPatternKind::Identifier(identifier) => {
                taroc_hir::BindingPatternKind::Identifier(identifier.clone())
            }
            taroc_ast::BindingPatternKind::Tuple(vec) => taroc_hir::BindingPatternKind::Tuple(
                self.lower_sequence(vec, |a, v| a.lower_binding_pattern(v)),
            ),
        }
    }
}

impl Actor<'_> {
    pub fn _lower_matching_pattern(
        &mut self,
        pat: taroc_ast::MatchingPattern,
    ) -> taroc_hir::MatchingPattern {
        taroc_hir::MatchingPattern {
            id: self.next(),
            span: pat.span,
            kind: self._lower_matching_pattern_kind(pat.kind),
        }
    }

    fn _lower_matching_pattern_kind(
        &mut self,
        _kind: taroc_ast::MatchingPatternKind,
    ) -> taroc_hir::MatchingPatternKind {
        todo!()
    }
}
