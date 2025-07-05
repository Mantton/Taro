use crate::{
    GlobalContext,
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    ty::{AssocTyKind, Ty, TyKind},
};

pub fn normalize_ty<'ctx>(ty: Ty<'ctx>, gcx: GlobalContext<'ctx>) -> Ty<'ctx> {
    let mut actor = AssocTypeFolder { gcx };
    ty.fold_with(&mut actor)
}

pub struct AssocTypeFolder<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for AssocTypeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::AssociatedType(k) => match k {
                AssocTyKind::Inherent(definition_id) => {
                    self.gcx().type_of(definition_id).fold_with(self)
                }
                AssocTyKind::DependentMember { base, name, .. } => {
                    let gcx = self.gcx;
                    let base = base.fold_with(self);

                    if !base.is_concrete() {
                        return ty;
                    }

                    let simple = base.to_simple_type();
                    let packages = self.gcx.packages_at_file(name.span.file);

                    let possible_ty = packages.into_iter().find_map(|pkg| {
                        let possible_id = gcx.with_type_database(pkg, |db| {
                            let possible_id = db
                                .alias_table
                                .by_type
                                .get(&simple)
                                .map(|table| table.aliases.get(&name.symbol))
                                .flatten()
                                .map(|(id, _)| *id);

                            possible_id
                        });
                        possible_id.map(|id| gcx.type_of(id))
                    });

                    let Some(assoc_ty) = possible_ty else {
                        todo!("unresolved associated type")
                    };
                    assoc_ty.fold_with(self)
                }
            },
            // Delegate to `TypeFoldable` on the *kind* itself, then rebuild
            // a fresh `Ty` only if something actually changed.
            _ => ty.super_fold_with(self),
        }
    }
}
