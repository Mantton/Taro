//! Exact unsafe raw-pointer read/write signatures and scanner-safe uninitialized storage.
use crate::{
    compile::context::Gcx,
    hir::{Abi, DefinitionID, StdItem},
    sema::models::{GenericArgument, TyKind},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Transfer {
    Read,
    Write,
}

pub(crate) fn transfer(gcx: Gcx<'_>, id: DefinitionID) -> Option<Transfer> {
    let name = gcx.definition_ident(id).symbol;
    let kind = match gcx.symbol_text(name).as_str() {
        "__intrinsic_ptr_read" => Transfer::Read,
        "__intrinsic_ptr_write" => Transfer::Write,
        _ => return None,
    };
    let sig = gcx.try_get_signature(id)?;
    let generics = gcx.generics_of(id);
    if sig.abi != Some(Abi::Intrinsic)
        || sig.is_variadic
        || !gcx.definition_is_unsafe(id)
        || gcx.definition_is_async(id)
        || generics.parent.is_some()
        || generics.parameters.len() != 1
        || sig.inputs.len() != if kind == Transfer::Read { 1 } else { 2 }
    {
        return None;
    }
    let element = match sig.inputs[0].ty.kind() {
        TyKind::Pointer(element, _) => element,
        _ => return None,
    };
    if !matches!(element.kind(), TyKind::Parameter(p) if p.index == 0) {
        return None;
    }
    (match kind {
        Transfer::Read => sig.output == element,
        Transfer::Write => sig.inputs[1].ty == element && sig.output == gcx.types.void,
    })
    .then_some(kind)
}

pub(crate) fn empty_uninit(gcx: Gcx<'_>, id: DefinitionID) -> bool {
    let Some(sig) = gcx.try_get_signature(id) else {
        return false;
    };
    let generics = gcx.generics_of(id);
    gcx.symbol_text(gcx.definition_ident(id).symbol).as_str() == "__intrinsic_maybe_uninit"
        && sig.abi == Some(Abi::Intrinsic)
        && !sig.is_variadic
        && sig.inputs.is_empty()
        && !gcx.definition_is_async(id)
        && generics.parent.is_none()
        && generics.parameters.len() == 1
        && matches!(sig.output.kind(), TyKind::Adt(def, args)
            if gcx.std_item_def(StdItem::MaybeUninit) == Some(def.id)
                && matches!(args.as_ref(), [GenericArgument::Type(ty)] if matches!(ty.kind(), TyKind::Parameter(p) if p.index == 0)))
}

#[cfg(test)]
mod tests {

    #[test]
    fn forged_or_safe_typed_transfers_are_rejected_before_mir() {
        for declaration in [
            "func __intrinsic_ptr_read[T](_ slot: *T) -> T",
            "unsafe func __intrinsic_ptr_read[T](_ slot: *T) -> bool",
            "unsafe func __intrinsic_ptr_write[T](_ slot: *T, _ value: bool)",
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(&format!(
                "extern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}"
            ));
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.message.contains("typed memory access")),
                "{declaration}: {diagnostics:?}"
            );
        }
    }
}
