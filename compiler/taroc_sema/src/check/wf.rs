use crate::GlobalContext;
use crate::check::context::func::FnCtx;
use crate::check::context::root::TyCheckRootCtx;
use crate::check::solver::{Goal, Obligation};
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
                let rcx = TyCheckRootCtx::new(self.context, def_id);
                let mut fcx = FnCtx::new(&rcx, def_id);
                if let Some(ty_node) = &node.ty {
                    let icx = crate::lower::ItemCtx::new(self.context);
                    let ty = icx
                        .lowerer()
                        .lower_type(ty_node, &crate::lower::LoweringRequest::default());
                    add_wf_obligations(&fcx, ty, ty_node.span);
                }
                solve(&mut fcx);
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
                let rcx = TyCheckRootCtx::new(self.context, def_id);
                let mut fcx = FnCtx::new(&rcx, def_id);
                if let Some(ty_node) = &node.ty {
                    let icx = crate::lower::ItemCtx::new(self.context);
                    let ty = icx
                        .lowerer()
                        .lower_type(ty_node, &crate::lower::LoweringRequest::default());
                    add_wf_obligations(&fcx, ty, ty_node.span);
                }
                solve(&mut fcx);
            }
            _ => {}
        }

        walk_function_declaration(self, d)
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_struct_or_enum(&mut self, def_id: DefinitionID) {
        let gcx = self.context;
        let rcx = TyCheckRootCtx::new(gcx, def_id);
        let mut fcx = FnCtx::new(&rcx, def_id);

        // Pull fields from type DB
        // Struct
        if let Some(sdef) = gcx.with_session_type_database(|db| db.structs.get(&def_id).copied()) {
            for field in sdef.variant.fields.iter() {
                let span = gcx.ident_for(field.id).span;
                add_wf_obligations(&fcx, field.ty, span);
            }
        }
        // Enum
        if let Some(edef) = gcx.with_session_type_database(|db| db.enums.get(&def_id).copied()) {
            for variant in edef.variants.iter() {
                for field in variant.fields.iter() {
                    let span = gcx.ident_for(field.id).span;
                    add_wf_obligations(&fcx, field.ty, span);
                }
            }
        }

        solve(&mut fcx);
    }

    fn check_function_signature(&mut self, id: NodeID, f: &taroc_hir::Function) {
        let gcx = self.context;
        let def_id = gcx.def_id(id);
        let rcx = TyCheckRootCtx::new(gcx, def_id);
        let mut fcx = FnCtx::new(&rcx, def_id);

        // Convert signature → Ty and apply env equalities
        let sig = gcx.fn_signature(def_id);
        let sig_ty = labeled_signature_to_ty(sig, gcx);
        // Recurse WF across inputs/outputs of function type
        let span = f.signature.span;
        add_wf_obligations(&fcx, sig_ty, span);
        solve(&mut fcx);
    }
}

fn add_wf_obligations<'rcx, 'ctx>(fcx: &FnCtx<'rcx, 'ctx>, ty: Ty<'ctx>, location: Span) {
    recurse_wf(fcx, ty, location);
}

fn recurse_wf<'rcx, 'ctx>(fcx: &FnCtx<'rcx, 'ctx>, ty: Ty<'ctx>, location: Span) {
    let gcx = fcx.gcx;
    match ty.kind() {
        TyKind::Adt(def, args) => {
            let preds = gcx.canon_predicates_of(def.id);
            for sp in preds.iter() {
                let instantiated = instantiate_constraint_with_args(gcx, sp.value, args);
                fcx.add_obligation(Obligation {
                    location,
                    goal: Goal::Constraint(instantiated),
                });
            }
            for ga in args.iter() {
                if let GenericArgument::Type(arg_ty) = *ga {
                    recurse_wf(fcx, arg_ty, location);
                }
            }
        }
        TyKind::FnDef(_, args) => {
            if let Some(def_id) = gcx.ty_to_def(ty) {
                let preds = gcx.canon_predicates_of(def_id);
                for sp in preds.iter() {
                    let instantiated = instantiate_constraint_with_args(gcx, sp.value, args);
                    fcx.add_obligation(Obligation {
                        location,
                        goal: Goal::Constraint(instantiated),
                    });
                }
            }
            for ga in args.iter() {
                if let GenericArgument::Type(arg_ty) = *ga {
                    recurse_wf(fcx, arg_ty, location);
                }
            }
        }
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => recurse_wf(fcx, inner, location),
        TyKind::Array(elem, _) => recurse_wf(fcx, elem, location),
        TyKind::Tuple(elems) => {
            for &e in elems.iter() {
                recurse_wf(fcx, e, location);
            }
        }
        TyKind::Function { inputs, output } => {
            for &i in inputs.iter() {
                recurse_wf(fcx, i, location);
            }
            recurse_wf(fcx, output, location);
        }
        _ => {}
    }
}

fn solve<'rcx, 'gcx>(fcx: &mut FnCtx<'rcx, 'gcx>) {
    let mut solver = fcx.solver.borrow_mut();
    let mut errors = solver.solve(&fcx, fcx.param_env());
    fcx.icx.default_numeric_vars();
    errors.extend(solver.solve(&fcx, fcx.param_env()));
    for err in errors.into_iter() {
        fcx.gcx
            .diagnostics
            .error(err.value.format(fcx.gcx), err.span);
    }
}
