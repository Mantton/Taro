//! GC object storage. Logical fields already include instantiated inherited
//! fields; a metadata word followed by that fixed order preserves base offsets.
use crate::{
    compile::context::Gcx,
    sema::{
        models::{Ty, TyKind},
        tycheck::utils::instantiate::instantiate_ty_with_args,
    },
};

pub(crate) fn gc_class_payload_ty<'ctx>(gcx: Gcx<'ctx>, class: Ty<'ctx>) -> Option<Ty<'ctx>> {
    let class = crate::sema::tycheck::utils::normalize_aliases(gcx, class);
    if !gcx.is_class_type(class) {
        return None;
    }
    let TyKind::Adt(definition, arguments) = class.kind() else {
        unreachable!()
    };
    let definition = gcx.get_struct_definition(definition.id);
    let mut fields = Vec::with_capacity(definition.fields.len() + 1);
    // Linker metadata addresses are carried as an integer-shaped word so they
    // are never mistaken for managed object pointers by a descriptor walker.
    fields.push(gcx.types.uint);
    fields.extend(
        definition
            .fields
            .iter()
            .map(|field| instantiate_ty_with_args(gcx, field.ty, arguments)),
    );
    Some(Ty::new(
        TyKind::Tuple(gcx.store.interners.intern_ty_list(fields)),
        gcx,
    ))
}
