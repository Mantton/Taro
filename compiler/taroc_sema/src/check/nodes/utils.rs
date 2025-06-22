use crate::{GlobalContext, check::context::func::FnCtx, ty::Ty};
use rustc_hash::FxHashSet;
use taroc_hir::{DefinitionID, PackageIndex, Resolution};
use taroc_span::Identifier;

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
    let packages = packages_at_file(file, gcx);
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

pub fn packages_at_file(file: taroc_span::FileID, gcx: GlobalContext) -> Vec<PackageIndex> {
    let mut packages = {
        let index = gcx.session().index();
        let resolutions = gcx.store.resolutions.borrow();
        let Some(resolutions) = resolutions.get(&index) else {
            unreachable!()
        };
        resolutions
            .file_to_imports
            .get(&file)
            .cloned()
            .unwrap_or_default()
    };

    packages.insert(gcx.session().index());

    packages.into_iter().collect()
}
