use crate::{
    GlobalContext,
    check::context::func::FnCtx,
    lower::{LoweringRequest, TypeLowerer},
    ty::Ty,
    utils::autoderef::Autoderef,
};
use rustc_hash::FxHashSet;
use taroc_hir::{DefinitionID, OperatorKind, Resolution};
use taroc_span::{FileID, Identifier, Span};

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn resolve_qualified_method_call(
        &self,
        method: Identifier,
        self_ty: Ty<'ctx>,
    ) -> Result<Resolution, ()> {
        let gcx = self.gcx;

        // Probe for associated function
        let candidates = associated_functions_for_ty(method, self_ty, gcx);
        if candidates.is_empty() {
            return Err(());
        }

        if let [candidate] = candidates.as_slice() {
            return Ok(Resolution::Definition(*candidate, gcx.def_kind(*candidate)));
        }

        let set: FxHashSet<_> = candidates.into_iter().collect();
        return Ok(Resolution::FunctionSet(set));
    }
}

pub fn associated_functions_for_ty<'ctx>(
    method: Identifier,
    self_ty: Ty<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> Vec<DefinitionID> {
    let file = method.span.file;
    let packages = gcx.packages_at_file(file);
    let simple_ty = self_ty.to_simple_type();
    let mut candidates = vec![];
    for package in packages {
        gcx.with_type_database(package, |db| {
            let Some(index) = db.function_table.methods.get(&simple_ty) else {
                return;
            };
            let Some(set) = index.functions.get(&method.symbol) else {
                return;
            };
            candidates.extend(set.members.iter().copied());
        });
    }

    candidates
}

pub fn associated_operators_for_ty<'ctx>(
    op: OperatorKind,
    self_ty: Ty<'ctx>,
    gcx: GlobalContext<'ctx>,
    file: FileID,
) -> Vec<DefinitionID> {
    let packages = gcx.packages_at_file(file);

    let simple_ty = gcx.try_simple_type(self_ty);
    let Some(simple_ty) = simple_ty else {
        return vec![];
    };
    let mut candidates = vec![];
    for package in packages {
        gcx.with_type_database(package, |db| {
            let Some(index) = db.function_table.methods.get(&simple_ty) else {
                return;
            };
            let Some(set) = index.operators.get(&op) else {
                return;
            };
            candidates.extend(set.members.iter().copied());
        });
    }

    candidates
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn lower_ty(&self, ast_ty: &taroc_hir::Type) -> Ty<'ctx> {
        let ty = self
            .lowerer()
            .lower_type(ast_ty, &LoweringRequest::default());

        // TODO: Well Formed Obligations
        ty
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn autoderef(&'rcx self, span: Span, ty: Ty<'ctx>) -> Autoderef<'rcx, 'ctx> {
        Autoderef::new(&self.icx, ty, span)
    }
}
