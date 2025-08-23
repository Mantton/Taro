use crate::GlobalContext;
use crate::check::solver::{Goal, Obligation, ObligationSolver};
use crate::infer::InferCtx;
use crate::lower::TypeLowerer;
use crate::ty::{GenericArgument, Ty, TyKind};
use crate::utils::{instantiate_constraint_with_args, labeled_signature_to_ty};
use taroc_error::CompileResult;
use taroc_hir::visitor::{HirVisitor, walk_declaration, walk_function_declaration};
use taroc_hir::{DefinitionID, NodeID};
use taroc_span::Span;

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
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        match &d.kind {
            taroc_hir::DeclarationKind::Struct(_) => {
                self.check_struct_or_enum(self.context.def_id(d.id));
            }
            taroc_hir::DeclarationKind::Enum(_) => {
                self.check_struct_or_enum(self.context.def_id(d.id));
            }
            taroc_hir::DeclarationKind::Function(f) => {
                self.check_function_signature(d.id, f);
            }
            taroc_hir::DeclarationKind::TypeAlias(node) => {
                // Ensure the aliased type itself is well-formed under alias env
                let def_id = self.context.def_id(d.id);
                let mut solver = ObligationSolver::new();
                let icx = InferCtx::new(self.context);
                if let Some(ty_node) = &node.ty {
                    let lcx = crate::lower::ItemCtx::new(self.context);
                    let ty = lcx
                        .lowerer()
                        .lower_type(ty_node, &crate::lower::LoweringRequest::default());
                    add_wf_obligations(self.context, &mut solver, ty, ty_node.span);
                }
                solve(self.context, &icx, &mut solver, def_id);
            }
            _ => {}
        }

        walk_declaration(self, d)
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        match &d.kind {
            taroc_hir::FunctionDeclarationKind::Struct(_) => {
                self.check_struct_or_enum(self.context.def_id(d.id));
            }
            taroc_hir::FunctionDeclarationKind::Enum(_) => {
                self.check_struct_or_enum(self.context.def_id(d.id));
            }
            taroc_hir::FunctionDeclarationKind::Function(f) => {
                self.check_function_signature(d.id, f);
            }
            taroc_hir::FunctionDeclarationKind::TypeAlias(node) => {
                // Associated type alias
                let def_id = self.context.def_id(d.id);
                let mut solver = ObligationSolver::new();
                let icx = InferCtx::new(self.context);
                if let Some(ty_node) = &node.ty {
                    let lcx = crate::lower::ItemCtx::new(self.context);
                    let ty = lcx
                        .lowerer()
                        .lower_type(ty_node, &crate::lower::LoweringRequest::default());
                    add_wf_obligations(self.context, &mut solver, ty, ty_node.span);
                }
                solve(self.context, &icx, &mut solver, def_id);
            }
            _ => {}
        }

        walk_function_declaration(self, d)
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_struct_or_enum(&mut self, def_id: DefinitionID) {
        let gcx = self.context;
        let mut solver = ObligationSolver::new();
        let icx = InferCtx::new(gcx);

        // Pull fields from type DB
        // Struct
        if let Some(sdef) = gcx.with_session_type_database(|db| db.structs.get(&def_id).copied()) {
            for field in sdef.variant.fields.iter() {
                let span = gcx.ident_for(field.id).span;
                add_wf_obligations(gcx, &mut solver, field.ty, span);
            }
        }
        // Enum
        if let Some(edef) = gcx.with_session_type_database(|db| db.enums.get(&def_id).copied()) {
            for variant in edef.variants.iter() {
                for field in variant.fields.iter() {
                    let span = gcx.ident_for(field.id).span;
                    add_wf_obligations(gcx, &mut solver, field.ty, span);
                }
            }
        }
        solve(gcx, &icx, &mut solver, def_id);
    }

    fn check_function_signature(&mut self, id: NodeID, f: &taroc_hir::Function) {
        let gcx = self.context;
        let def_id = gcx.def_id(id);
        let mut solver = ObligationSolver::new();
        let icx = InferCtx::new(gcx);

        // Convert signature → Ty and apply env equalities
        let sig = gcx.fn_signature(def_id);
        let sig_ty = labeled_signature_to_ty(sig, gcx);
        // Recurse WF across inputs/outputs of function type
        let span = f.signature.span;
        add_wf_obligations(gcx, &mut solver, sig_ty, span);
        solve(gcx, &icx, &mut solver, def_id);
    }
}

fn add_wf_obligations<'ctx>(
    gcx: crate::GlobalContext<'ctx>,
    solver: &mut ObligationSolver<'ctx>,
    ty: Ty<'ctx>,
    location: Span,
) {
    recurse_wf(gcx, solver, ty, location);
}

fn recurse_wf<'ctx>(
    gcx: crate::GlobalContext<'ctx>,
    solver: &mut ObligationSolver<'ctx>,
    ty: Ty<'ctx>,
    location: Span,
) {
    match ty.kind() {
        TyKind::Adt(def, args) => {
            let preds = gcx.canon_predicates_of(def.id);
            for sp in preds.iter() {
                let instantiated = instantiate_constraint_with_args(gcx, sp.value, args);
                solver.add_obligation(Obligation {
                    location,
                    goal: Goal::Constraint(instantiated),
                });
            }
            for ga in args.iter() {
                if let GenericArgument::Type(arg_ty) = *ga {
                    recurse_wf(gcx, solver, arg_ty, location);
                }
            }
        }
        TyKind::FnDef(_, args) => {
            if let Some(def_id) = gcx.ty_to_def(ty) {
                let preds = gcx.canon_predicates_of(def_id);
                for sp in preds.iter() {
                    let instantiated = instantiate_constraint_with_args(gcx, sp.value, args);
                    solver.add_obligation(Obligation {
                        location,
                        goal: Goal::Constraint(instantiated),
                    });
                }
            }
            for ga in args.iter() {
                if let GenericArgument::Type(arg_ty) = *ga {
                    recurse_wf(gcx, solver, arg_ty, location);
                }
            }
        }
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
            recurse_wf(gcx, solver, inner, location)
        }
        TyKind::Array(elem, _) => recurse_wf(gcx, solver, elem, location),
        TyKind::Tuple(elems) => {
            for &e in elems.iter() {
                recurse_wf(gcx, solver, e, location);
            }
        }
        TyKind::Function { inputs, output } => {
            for &i in inputs.iter() {
                recurse_wf(gcx, solver, i, location);
            }
            recurse_wf(gcx, solver, output, location);
        }
        _ => {}
    }
}

fn solve<'ctx>(
    gcx: crate::GlobalContext<'ctx>,
    icx: &InferCtx<'ctx>,
    solver: &mut ObligationSolver<'ctx>,
    def_id: taroc_hir::DefinitionID,
) {
    let param_env = gcx.param_env(def_id);
    let mut errors = solver.solve(icx, param_env);
    icx.default_numeric_vars();
    errors.extend(solver.solve(icx, param_env));
    for err in errors.into_iter() {
        gcx.diagnostics.error(err.value.format(gcx), err.span);
    }
}
