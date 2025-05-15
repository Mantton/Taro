use super::package::Actor;

impl Actor<'_> {
    pub fn lower_path(&mut self, path: taroc_ast::Path) -> taroc_hir::Path {
        taroc_hir::Path {
            span: path.span,
            segments: self.lower_sequence(path.segments, |a, sg| a.lower_path_segment(sg)),
        }
    }

    pub fn lower_tagged_path(&mut self, path: taroc_ast::Path) -> taroc_hir::TaggedPath {
        taroc_hir::TaggedPath {
            path: self.lower_path(path),
            id: self.next(),
        }
    }

    pub fn lower_path_segment(
        &mut self,
        segment: taroc_ast::PathSegment,
    ) -> taroc_hir::PathSegment {
        taroc_hir::PathSegment {
            id: self.next(),
            identifier: segment.identifier,
            arguments: self.lower_optional(segment.arguments, |a, tys| a.lower_type_arguments(tys)),
            span: segment.span,
        }
    }
}
