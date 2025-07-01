use crate::{check::context::func::FnCtx, ty::Ty};
use taroc_hir::{
    NodeID, PatternKind,
    visitor::{HirVisitor, walk_pattern},
};
use taroc_span::Span;

pub(super) struct GatherLocalsVisitor<'rcx, 'gcx> {
    fcx: &'rcx FnCtx<'rcx, 'gcx>,
}

impl<'rcx, 'gcx> GatherLocalsVisitor<'rcx, 'gcx> {
    pub fn from_match_arm(fcx: &'rcx FnCtx<'rcx, 'gcx>, pat: &taroc_hir::Pattern) {
        let mut v = GatherLocalsVisitor { fcx };
        v.visit_pattern(pat)
    }

    pub fn from_local(fcx: &'rcx FnCtx<'rcx, 'gcx>, local: &taroc_hir::Local) {
        let mut v = GatherLocalsVisitor { fcx };
        v.declare(local.id, local.ty.as_deref(), local.pattern.span);
        v.visit_pattern(&local.pattern)
    }

    pub fn _from_pattern_binding(
        fcx: &'rcx FnCtx<'rcx, 'gcx>,
        binding: &taroc_hir::PatternBinding,
        expr: &taroc_hir::Expression,
    ) {
        let mut v = GatherLocalsVisitor { fcx };
        v.declare(expr.id, None, expr.span);
        v.visit_pattern(&binding.pattern)
    }

    fn assign(&mut self, span: Span, id: NodeID, ty: Option<Ty<'gcx>>) -> Ty<'gcx> {
        let mut locals = self.fcx.locals.borrow_mut();
        if locals.get(&id).is_some() {
            unreachable!("evaluated local more than once")
        };

        let ty = match ty {
            Some(ty) => {
                locals.insert(id, ty);
                ty
            }
            None => {
                let var_ty = self.fcx.next_ty_var(span);
                locals.insert(id, var_ty);
                var_ty
            }
        };

        ty
    }

    fn declare(&mut self, id: NodeID, ty: Option<&taroc_hir::Type>, span: Span) {
        let annotation = ty.map(|f| self.fcx.lower_ty(f));
        self.assign(span, id, annotation);
    }
}

impl HirVisitor for GatherLocalsVisitor<'_, '_> {
    fn visit_pattern(&mut self, p: &taroc_hir::Pattern) -> Self::Result {
        let PatternKind::Identifier(..) = &p.kind else {
            return walk_pattern(self, p);
        };
        let _ = self.assign(p.span, p.id, None);
        return walk_pattern(self, p);
    }
}
