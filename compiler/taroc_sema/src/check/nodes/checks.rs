use crate::{
    check::{context::func::FnCtx, expectation::Expectation},
    lower::{LoweringRequest, TypeLowerer},
    ty::{Ty, TyKind},
    utils::ty2str,
};

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn check_return(&self, expr: &taroc_hir::Expression, explicit: bool) {
        let return_coercion = self
            .ret_coercion
            .as_ref()
            .expect("ICE: return check called outside function body");

        let return_ty = return_coercion.borrow().expected_ty();

        //
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
                return Some(self.commons().void);
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
        let ty = if let Some(annotation) = &local.ty {
            let annotation_ty = self
                .lowerer()
                .lower_type(annotation, &LoweringRequest::default());
            annotation_ty
        } else {
            self.next_ty_var(local.pattern.span)
        };

        if let Some(initializer) = &local.initializer {
            self.check_expression_coercible_to_type(initializer, ty, None);
        }

        self.resolve_binding_pattern(&local.pattern, ty);
    }

    fn resolve_binding_pattern(&self, pattern: &taroc_hir::BindingPattern, ty: Ty<'gcx>) {
        match &pattern.kind {
            taroc_hir::BindingPatternKind::Wildcard => {}
            taroc_hir::BindingPatternKind::Identifier(ident) => {
                let id = pattern.id;
                self.locals.borrow_mut().insert(id, ty);
                println!("Bound {} to {}", ident.symbol, ty2str(ty, self.gcx))
            }
            taroc_hir::BindingPatternKind::Tuple(patterns) => {
                // Only tuple types can be destructured
                if let TyKind::Tuple(elements) = ty.kind() {
                    // Arity mismatch
                    if elements.len() != patterns.len() {
                        let message = format!(
                            "mismatched tuple length: expected `{}`, found `{}`",
                            elements.len(),
                            patterns.len()
                        );
                        self.gcx.diagnostics.error(message, pattern.span);
                    } else {
                        // Recurse into each sub-pattern
                        for (pattern, &ty) in patterns.iter().zip(elements.iter()) {
                            self.resolve_binding_pattern(pattern, ty);
                        }
                    }
                } else {
                    // Cannot destruct non-tuple
                    let message = format!(
                        "cannot destructure non-tuple type `{}`",
                        ty2str(ty, self.gcx)
                    );
                    self.gcx.diagnostics.error(message, pattern.span);
                }
            }
        }
    }
}
