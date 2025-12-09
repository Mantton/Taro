use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        error::SpannedError,
        models::{Ty, TyKind},
    },
};

mod context;
mod models;
mod node;

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: Gcx<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_function(
        &mut self,
        id: hir::DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        self.check_function(id, node, fn_ctx);
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_function(&self, id: DefinitionID, func: &hir::Function, _: hir::FunctionContext) {
        let rcx = context::TyCheckRootCtx::new(id, self.context);
        let mut fcx = context::FnCtx::new(id, &rcx);
        check_func(id, func, &mut fcx);
    }
}

fn check_func<'rcx, 'gcx>(
    id: DefinitionID,
    node: &hir::Function,
    fcx: &mut context::FnCtx<'rcx, 'gcx>,
) {
    let signature = fcx.gcx.get_signature(id);
    let signature = Ty::from_labeled_signature(fcx.gcx, signature);

    let (param_tys, return_ty) = match signature.kind() {
        TyKind::FnPointer { inputs, output, .. } => (inputs, output),
        _ => unreachable!("function signature must be of function pointer type"),
    };

    fcx.return_ty = Some(return_ty);

    // Add Parameters To Locals Map
    for (parameter, &parameter_ty) in node.signature.prototype.inputs.iter().zip(param_tys) {
        fcx.locals.borrow_mut().insert(parameter.id, parameter_ty);
    }

    let Some(body) = &node.block else {
        unreachable!("ICE: Checking Function without Body")
    };

    // Collect
    if let Some(body) = hir::is_expression_bodied(body) {
        // --- single-expression body ---
        fcx.check_return(body);
    } else {
        // --- regular block body ---
        fcx.check_block(body);
    }

    // Solve
    solve(fcx);
}

fn solve<'rcx, 'gcx>(fcx: &mut context::FnCtx<'rcx, 'gcx>) {
    let gcx = fcx.gcx;
    let mut solver = fcx.solver.borrow_mut();
    let errors = solver.solve_all();

    let report_errors = |errs: &Vec<SpannedError<'gcx>>| {
        for item in errs {
            gcx.dcx()
                .emit_error(item.value.format(gcx), Some(item.span));
        }
    };

    report_errors(&errors)
}
