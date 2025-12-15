use crate::{
    hir::{self, HirVisitor, Mutability, NodeID},
    sema::{
        models::Ty,
        tycheck::{
            check::checker::{Checker, LocalBinding},
            solve::ConstraintSystem,
        },
    },
    span::Span,
};

pub(super) struct GatherLocalsVisitor<'cs, 'arena> {
    cs: &'cs ConstraintSystem<'arena>,
    checker: &'cs Checker<'arena>,
    pattern_mutable: bool,
}

impl<'cs, 'arena> GatherLocalsVisitor<'cs, 'arena> {
    pub fn from_match_arm(
        cs: &'cs ConstraintSystem<'arena>,
        checker: &'cs Checker<'arena>,
        pat: &hir::Pattern,
    ) {
        let mut v = GatherLocalsVisitor {
            cs,
            checker,
            pattern_mutable: false,
        };
        v.visit_pattern(pat)
    }

    pub fn from_local(
        cs: &'cs ConstraintSystem<'arena>,
        checker: &'cs Checker<'arena>,
        local: &hir::Local,
    ) {
        let mut v = GatherLocalsVisitor {
            cs,
            checker,
            pattern_mutable: local.mutability == Mutability::Mutable,
        };
        v.declare(
            local.id,
            local.ty.as_deref(),
            local.pattern.span,
            local.mutability == Mutability::Mutable,
        );
        v.visit_pattern(&local.pattern)
    }

    fn assign(
        &mut self,
        span: Span,
        id: NodeID,
        ty: Option<Ty<'arena>>,
        mutable: bool,
    ) -> Ty<'arena> {
        let mut locals = self.cs.locals.borrow_mut();

        let ty = match ty {
            Some(ty) => {
                locals.insert(id, ty);
                self.checker.set_local(id, LocalBinding { ty, mutable });
                ty
            }
            None => {
                let ty = self.cs.infer_cx.next_ty_var(span);
                locals.insert(id, ty);
                self.checker.set_local(id, LocalBinding { ty, mutable });
                ty
            }
        };

        ty
    }

    fn declare(&mut self, id: NodeID, ty: Option<&hir::Type>, span: Span, mutable: bool) {
        let annotation = ty.map(|f| self.checker.lower_type(f));
        self.assign(span, id, annotation, mutable);
    }
}

impl HirVisitor for GatherLocalsVisitor<'_, '_> {
    fn visit_pattern(&mut self, p: &hir::Pattern) -> Self::Result {
        let hir::PatternKind::Identifier(..) = &p.kind else {
            return hir::walk_pattern(self, p);
        };

        let _ = self.assign(p.span, p.id, None, self.pattern_mutable);
        return hir::walk_pattern(self, p);
    }
}
