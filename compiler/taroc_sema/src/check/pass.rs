use super::context::func::FnCtx;
use crate::{
    GlobalContext,
    check::context::root::TyCheckRootCtx,
    normalize::assoc::normalize_ty,
    ty::{Constraint, GenericArgument, GenericParameter, ParamEnv, Ty, TyKind},
    utils::{GenericsBuilder, instantiate_ty_with_args, labeled_signature_to_ty},
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

    fn run(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
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
            && f.block.is_none()
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
    let signature = apply_env(id, &fcx.param_env(), signature, fcx.gcx);

    let (param_tys, return_ty) = match signature.kind() {
        TyKind::Function { inputs, output, .. } => (inputs, output),
        _ => unreachable!("function signature must be of function pointer type"),
    };

    fcx.ret_ty = Some(return_ty);

    for (parameter, &parameter_ty) in node.signature.prototype.inputs.iter().zip(param_tys) {
        fcx.locals.borrow_mut().insert(parameter.id, parameter_ty);
    }

    for (index, param) in node.signature.prototype.inputs.iter().enumerate() {
        let Some(expression) = &param.default_value else {
            continue;
        };

        let param_ty = param_tys[index];
        fcx.check_expression_coercible_to_type(expression, param_ty, None);
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
    let gcx = fcx.gcx;
    let mut solver = fcx.solver.borrow_mut();
    let mut errors = solver.solve(&fcx, fcx.param_env());
    // Commit adjustments from this solve pass into TypingResult
    {
        let adjustments = solver.take_adjustments();
        if !adjustments.is_empty() {
            let mut results = fcx.results.borrow_mut();
            for (node, mut adjs) in adjustments.into_iter() {
                results
                    .adjustments
                    .entry(node)
                    .or_default()
                    .append(&mut adjs);
            }
        }
        let assoc = solver.take_assoc_resolution();
        if !assoc.is_empty() {
            let mut results = fcx.results.borrow_mut();
            for (node, res) in assoc.into_iter() {
                results.assoc_resolution.insert(node, res);
            }
        }
    }

    // Defualt IntVars, FloatVars and NilVars
    // After the initial solve pass, default any unconstrained numeric vars
    // to concrete defaults so the next pass can propagate them.
    fcx.icx.default_numeric_vars();

    // Re-Run Solver
    errors.extend(solver.solve(&fcx, fcx.param_env()));
    // Commit adjustments from the second pass as well
    {
        let adjustments = solver.take_adjustments();
        if !adjustments.is_empty() {
            let mut results = fcx.results.borrow_mut();
            for (node, mut adjs) in adjustments.into_iter() {
                results
                    .adjustments
                    .entry(node)
                    .or_default()
                    .append(&mut adjs);
            }
        }
        let assoc = solver.take_assoc_resolution();
        if !assoc.is_empty() {
            let mut results = fcx.results.borrow_mut();
            for (node, res) in assoc.into_iter() {
                results.assoc_resolution.insert(node, res);
            }
        }
    }

    // println!("{:?}", fcx.results.borrow().adjustments);
    // Before persisting, replace all inference variables with concrete types
    // and normalize any associated types in the recorded node types.
    let fn_id = fcx.fn_id;
    let mut results = fcx.results.take();
    if !results.node_types.is_empty() {
        let icx = &fcx.icx;
        let gcx = fcx.gcx;
        for ty in results.node_types.values_mut() {
            let resolved = icx.resolve_vars_if_possible(*ty);
            *ty = normalize_ty(resolved, gcx);
        }
    }

    // Report Errors
    for err in errors.into_iter() {
        gcx.diagnostics.error(err.value.format(gcx), err.span);
    }

    gcx.with_session_type_database(|db| db.typing_results.insert(fn_id, gcx.alloc(results)));
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

fn apply_env<'ctx>(
    id: DefinitionID,
    env: &ParamEnv<'ctx>,
    ty: Ty<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> Ty<'ctx> {
    let arguments = GenericsBuilder::for_item(gcx, id, |p, _| {
        let ty = gcx.mk_ty(TyKind::Parameter(GenericParameter {
            index: p.index,
            name: p.name,
        }));

        let target = env.constraints.iter().find_map(|&c| match c {
            Constraint::TypeEquality(a, b) if a == ty => Some(b),
            Constraint::TypeEquality(a, b) if b == ty => Some(a),
            _ => None,
        });

        GenericArgument::Type(target.unwrap_or(ty))
    });

    instantiate_ty_with_args(gcx, ty, arguments)
}
