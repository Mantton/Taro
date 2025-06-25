use taroc_hir::{
    MatchingPatternKind, NodeID,
    visitor::{HirVisitor, walk_matching_pattern},
};
use taroc_span::Span;

use crate::{check::context::func::FnCtx, ty::Ty};

pub(super) struct GatherLocalsVisitor<'rcx, 'gcx> {
    fcx: &'rcx FnCtx<'rcx, 'gcx>,
}

impl<'rcx, 'gcx> GatherLocalsVisitor<'rcx, 'gcx> {
    pub fn gather_from_when_arm(fcx: &'rcx FnCtx<'rcx, 'gcx>, pat: &taroc_hir::MatchingPattern) {
        let mut v = GatherLocalsVisitor { fcx };
        v.visit_matching_pattern(pat)
    }

    fn assign(&mut self, span: Span, id: NodeID) -> Ty<'gcx> {
        let var_ty = self.fcx.next_ty_var(span);
        self.fcx.locals.borrow_mut().insert(id, var_ty);
        var_ty
    }
}

impl HirVisitor for GatherLocalsVisitor<'_, '_> {
    fn visit_matching_pattern(&mut self, p: &taroc_hir::MatchingPattern) -> Self::Result {
        let MatchingPatternKind::Binding(..) = &p.kind else {
            return walk_matching_pattern(self, p);
        };
        let _ = self.assign(p.span, p.id);
        return walk_matching_pattern(self, p);
    }
}
