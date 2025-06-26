use super::package::Actor;

impl Actor<'_> {
    pub fn lower_pattern(&mut self, pattern: taroc_ast::Pattern) -> taroc_hir::Pattern {
        taroc_hir::Pattern {
            id: self.next(),
            span: pattern.span,
            kind: self.lower_pattern_kind(pattern.kind),
        }
    }

    fn lower_pattern_kind(&mut self, kind: taroc_ast::PatternKind) -> taroc_hir::PatternKind {
        use taroc_ast::PatternKind as Src;
        use taroc_hir::PatternKind as Dest;

        match kind {
            // `_`
            Src::Wildcard => Dest::Wildcard,

            // `..`
            Src::Rest => todo!(),

            // `foo`
            Src::Identifier(ident) => Dest::Identifier(ident),

            // `(a, b, …)`
            Src::Tuple(items, span) => {
                let lowered = items.into_iter().map(|p| self.lower_pattern(p)).collect();
                Dest::Tuple(lowered, span)
            }

            // `Foo::Bar`
            Src::Path(path) => Dest::Path(self.lower_path(path)),

            // `Foo::Bar(a, b)`
            Src::PathTuple(path, items, span) => {
                let lowered = items.into_iter().map(|p| self.lower_pattern(p)).collect();
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
                        pattern: self.lower_pattern(f.pattern),
                    })
                    .collect();
                Dest::PathStruct(self.lower_path(path), lowered_fields, span, has_rest)
            }

            // `Foo | Bar`
            Src::Or(arms, span) => {
                let lowered = arms.into_iter().map(|p| self.lower_pattern(p)).collect();
                Dest::Or(lowered, span)
            }

            // literal pattern (anon consts)
            Src::Literal(c) => Dest::Literal(self.lower_anon_const(c)),
        }
    }
}
