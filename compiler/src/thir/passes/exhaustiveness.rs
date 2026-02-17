#![allow(clippy::new_without_default)]

//! Exhaustiveness checks for match expressions.
use crate::{
    compile::context::GlobalContext,
    diagnostics::{Diagnostic, DiagnosticLevel},
    error::CompileResult,
    sema::models::TyKind,
    thir::{self, ExprId, ExprKind, ThirFunction, ThirPackage},
};
use thir::match_tree::compile_match;

pub fn run<'ctx>(package: &mut ThirPackage<'ctx>, gcx: GlobalContext<'ctx>) -> CompileResult<()> {
    let mut pass = ExhaustivenessPass::new(gcx);
    pass.check_package(package);
    gcx.dcx().ok()
}

struct ExhaustivenessPass<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> ExhaustivenessPass<'ctx> {
    fn new(gcx: GlobalContext<'ctx>) -> Self {
        Self { gcx }
    }

    fn check_package(&mut self, package: &mut ThirPackage<'ctx>) {
        for func in package.functions.values_mut() {
            self.check_function(func);
        }
    }

    fn check_function(&mut self, func: &mut ThirFunction<'ctx>) {
        let expr_ids: Vec<_> = func.exprs.indices().collect();
        for expr_id in expr_ids {
            let expr = &func.exprs[expr_id];
            if let ExprKind::Match { scrutinee, arms } = &expr.kind {
                let arms = arms.clone();
                self.check_match(func, expr_id, *scrutinee, &arms, expr.span);
            }
        }
    }

    fn check_match(
        &mut self,
        func: &mut ThirFunction<'ctx>,
        expr_id: ExprId,
        scrutinee: ExprId,
        arms: &[thir::ArmId],
        span: thir::Span,
    ) {
        let scrutinee_ty = func.exprs[scrutinee].ty;
        if matches!(scrutinee_ty.kind(), TyKind::Error | TyKind::Infer(_)) {
            return;
        }

        let result = compile_match(self.gcx, func, scrutinee, arms);
        let missing = result.missing_patterns(self.gcx);
        let diagnostics = result.diagnostics.clone();
        func.match_trees.insert(expr_id, result.tree);

        if diagnostics.missing {
            let message = if missing.is_empty() {
                "non-exhaustive match".to_string()
            } else {
                format!(
                    "non-exhaustive match, missing '{}' case",
                    missing.join(", ")
                )
            };

            self.gcx
                .dcx()
                .emit(Diagnostic::new(message, Some(span), DiagnosticLevel::Error));
        }

        let mut reachable = vec![false; func.arms.len()];
        for arm_id in diagnostics.reachable {
            reachable[arm_id.index()] = true;
        }

        for arm_id in arms {
            if !reachable[arm_id.index()] {
                let arm = &func.arms[*arm_id];
                self.gcx.dcx().emit(Diagnostic::new(
                    "unreachable match arm".to_string(),
                    Some(arm.span),
                    DiagnosticLevel::Warn,
                ));
            }
        }
    }
}
