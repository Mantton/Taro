use super::context::func::FnCtx;
use crate::{
    GlobalContext, check::context::root::TyCheckRootCtx, ty::TyKind, utils::labeled_signature_to_ty,
};
use taroc_error::CompileResult;
use taroc_hir::{
    DefinitionID,
    visitor::{AssocContext, FunctionContext, HirVisitor},
};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_function(
        &mut self,
        id: taroc_hir::NodeID,
        f: &taroc_hir::Function,
        c: taroc_hir::visitor::FunctionContext,
    ) -> Self::Result {
        // do not check interface functions
        if let FunctionContext::Assoc(AssocContext::Interface(..))
        | FunctionContext::AssocOperand(AssocContext::Interface(..), _) = c
        {
            return;
        }

        // self.context
        //     .diagnostics
        //     .warn("checking".into(), f.signature.span);
        self.check_function(id, f, c);
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_function(
        &self,
        id: taroc_hir::NodeID,
        func: &taroc_hir::Function,
        _: taroc_hir::visitor::FunctionContext,
    ) {
        let id = self.context.def_id(id);
        // let name = self.context.ident_for(id);
        // let msg = format!("--- Checking '{}'---", name.symbol);
        // self.context.diagnostics.info(msg, name.span);

        let rcx = TyCheckRootCtx::new(self.context, id);
        let mut fcx = FnCtx::new(&rcx, id);
        check_func(&mut fcx, id, func);
    }
}

fn check_func<'rcx, 'gcx>(
    fcx: &mut FnCtx<'rcx, 'gcx>,
    id: DefinitionID,
    node: &taroc_hir::Function,
) {
    // Get Signature
    let signature = fcx.gcx.fn_signature(id);
    let signature = labeled_signature_to_ty(signature, fcx.gcx);

    let (param_tys, return_ty) = match signature.kind() {
        TyKind::Function { inputs, output, .. } => (inputs, output),
        _ => unreachable!("function signature must be of function pointer type"),
    };

    fcx.ret_ty = Some(return_ty);

    for (parameter, &parameter_ty) in node.signature.prototype.inputs.iter().zip(param_tys) {
        fcx.locals.borrow_mut().insert(parameter.id, parameter_ty);
    }

    let Some(body) = &node.block else {
        unreachable!("ICE: Checking Function without Body")
    };

    // Collect Obligations
    collect(fcx, body);

    // Solve Obligations
    solve(fcx);
    // println!("--- \n")
}

fn collect<'rcx, 'gcx>(fcx: &mut FnCtx<'rcx, 'gcx>, node: &taroc_hir::Block) {
    if let Some(body) = is_expression_bodied(node) {
        // --- single-expression body ---
        fcx.check_return(body, false);
    } else {
        // --- regular block body ---
        fcx.check_block(node);
    }
}

fn solve<'rcx, 'gcx>(fcx: &mut FnCtx<'rcx, 'gcx>) {
    let mut solver = fcx.solver.borrow_mut();
    solver.solve(&fcx.icx, fcx.param_env());
}

fn is_expression_bodied(block: &taroc_hir::Block) -> Option<&taroc_hir::Expression> {
    match block.statements.as_slice() {
        [
            taroc_hir::Statement {
                kind: taroc_hir::StatementKind::Expression(expr),
                ..
            },
        ] => {
            Some(expr) // exactly one expression stmt → expr-bodied
        }
        _ => None, // otherwise treat as regular block
    }
}
