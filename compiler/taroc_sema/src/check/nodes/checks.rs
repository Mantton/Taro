use crate::{
    check::{context::func::FnCtx, expectation::Expectation, gather::GatherLocalsVisitor},
    ty::Ty,
};

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn check_return(&self, expr: &taroc_hir::Expression, _: bool) {
        let Some(ret_ty) = self.ret_ty else {
            unreachable!("ICE: return check called outside function body")
        };

        let _ = self.check_expression_coercible_to_type(expr, ret_ty, None);
    }
}

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn check_statement(
        &self,
        statement: &taroc_hir::Statement,
        expectation: Option<Expectation<'gcx>>,
    ) -> Option<Ty<'gcx>> {
        if matches!(statement.kind, taroc_hir::StatementKind::Declaration(..)) {
            return None;
        }

        match &statement.kind {
            taroc_hir::StatementKind::Expression(node) => {
                let ty = if let Some(expectation) = expectation {
                    self.check_expression_with_expectation(node, expectation)
                } else {
                    self.check_expression(node)
                };

                return Some(ty);
            }
            taroc_hir::StatementKind::Variable(local) => {
                self.check_local(local);
                return Some(self.common_types().void);
            }
            taroc_hir::StatementKind::Break(_) => {}
            taroc_hir::StatementKind::Continue(_) => {}
            taroc_hir::StatementKind::Return(expression) => {
                if let Some(expression) = expression {
                    self.check_return(expression, true);
                } else {
                    // TODO: Coerce Unit
                }
            }
            taroc_hir::StatementKind::Loop(_, block) => {
                self.check_block(block);
            }
            taroc_hir::StatementKind::Defer(block) => {
                self.check_block(block);
            }
            _ => {}
        };

        return None;
    }

    pub fn check_block(&self, block: &taroc_hir::Block) {
        for statement in &block.statements {
            self.check_statement(statement, None);
        }
    }

    pub fn check_local(&self, local: &taroc_hir::Local) {
        GatherLocalsVisitor::from_local(self, local);
        let ty = self.local_ty(local.id);
        if let Some(initializer) = &local.initializer {
            self.check_expression_coercible_to_type(initializer, ty, None);
        }
        self.add_shape_obligation(&local.pattern, ty);
    }
}
