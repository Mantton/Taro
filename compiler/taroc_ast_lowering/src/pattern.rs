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
    pub fn lower_matching_pattern(
        &mut self,
        pattern: taroc_ast::MatchingPattern,
    ) -> taroc_hir::MatchingPattern {
        taroc_hir::MatchingPattern {
            id: self.next(),
            span: pattern.span,
            kind: self.lower_matching_pattern_kind(pattern.kind),
        }
    }

    fn lower_matching_pattern_kind(
        &mut self,
        kind: taroc_ast::MatchingPatternKind,
    ) -> taroc_hir::MatchingPatternKind {
        use taroc_ast::MatchingPatternKind as Src;
        use taroc_hir::MatchingPatternKind as Dest;

        match kind {
            // `_`
            Src::Wildcard => Dest::Wildcard,

            // `..`
            Src::Rest => todo!(),

            // `foo` | `var foo`
            Src::Binding(mode, ident) => Dest::Binding(mode, ident),

            // `(a, b, …)`
            Src::Tuple(items, span) => {
                let lowered = items
                    .into_iter()
                    .map(|p| self.lower_matching_pattern(p))
                    .collect();
                Dest::Tuple(lowered, span)
            }

            // `Foo::Bar`
            Src::Path(path) => Dest::Path(self.lower_path(path)),

            // `Foo::Bar(a, b)`
            Src::PathTuple(path, items, span) => {
                let lowered = items
                    .into_iter()
                    .map(|p| self.lower_matching_pattern(p))
                    .collect();
                Dest::PathTuple(self.lower_path(path), lowered, span)
            }

            // `Foo::Bar { a, b, .. }`
            Src::PathStruct(path, fields, span, has_rest) => {
                let lowered_fields = fields
                    .into_iter()
                    .map(|f| taroc_hir::PatternField {
                        id: self.next(),
                        span: f.span,
                        identifier: f.identifier,
                        pattern: self.lower_matching_pattern(f.pattern),
                    })
                    .collect();
                Dest::PathStruct(self.lower_path(path), lowered_fields, span, has_rest)
            }

            // `Foo | Bar`
            Src::Or(arms, span) => {
                let lowered = arms
                    .into_iter()
                    .map(|p| self.lower_matching_pattern(p))
                    .collect();
                Dest::Or(lowered, span)
            }

            // literal pattern (anon consts)
            Src::Literal(c) => Dest::Literal(self.lower_anon_const(c)),
        }
    }
}
