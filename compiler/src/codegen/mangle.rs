use crate::{
    compile::context::GlobalContext,
    hir,
    sema::{
        models::{Ty, TyKind},
        resolve::models::{DefinitionKind, PrimaryType, TypeHead},
    },
};
use rustc_hash::FxHashSet;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub fn mangle(gcx: GlobalContext, id: hir::DefinitionID) -> String {
    fn sanitize(s: &str) -> String {
        s.chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() || c == '_' {
                    c
                } else {
                    '_'
                }
            })
            .collect()
    }

    fn ty_symbol(gcx: GlobalContext, ty: Ty) -> String {
        match ty.kind() {
            TyKind::Bool => "bool".into(),
            TyKind::Rune => "rune".into(),
            TyKind::String => "str".into(),
            TyKind::Int(i) => i.name_str().into(),
            TyKind::UInt(u) => u.name_str().into(),
            TyKind::Float(f) => f.name_str().into(),
            TyKind::Pointer(inner, mt) => {
                format!("ptr{}{}", mt.display_str(), ty_symbol(gcx, inner))
            }
            TyKind::Reference(inner, mt) => {
                format!("ref{}{}", mt.display_str(), ty_symbol(gcx, inner))
            }
            TyKind::Adt(def) => gcx.definition_ident(def.id).symbol.as_str().into(),
            TyKind::Tuple(items) => {
                let parts: Vec<_> = items.iter().map(|t| ty_symbol(gcx, *t)).collect();
                format!("tuple{}", parts.join("_"))
            }
            TyKind::FnPointer { .. } => "fnptr".into(),
            TyKind::Infer(_) | TyKind::Error => "err".into(),
        }
    }

    fn type_head_symbol(gcx: GlobalContext, head: TypeHead) -> String {
        match head {
            TypeHead::Primary(PrimaryType::Bool) => "bool".into(),
            TypeHead::Primary(PrimaryType::Rune) => "rune".into(),
            TypeHead::Primary(PrimaryType::String) => "str".into(),
            TypeHead::Primary(PrimaryType::Int(i)) => i.name_str().into(),
            TypeHead::Primary(PrimaryType::UInt(u)) => u.name_str().into(),
            TypeHead::Primary(PrimaryType::Float(f)) => f.name_str().into(),
            TypeHead::Nominal(def_id) => gcx.definition_ident(def_id).symbol.as_str().into(),
            TypeHead::Reference(mt) => format!("ref{}", mt.display_str()),
            TypeHead::Pointer(mt) => format!("ptr{}", mt.display_str()),
            TypeHead::Tuple(len) => format!("tuple{len}"),
            TypeHead::Array => "array".into(),
        }
    }

    let output = gcx.resolution_output(id.package());

    let pkg_ident = gcx
        .package_ident(id.package())
        .unwrap_or_else(|| gcx.config.identifier.clone());
    let pkg_ident = sanitize(pkg_ident.as_ref());

    let leaf_ident = output
        .definition_to_ident
        .get(&id)
        .map(|i| sanitize(i.symbol.as_str()))
        .unwrap_or_else(|| sanitize(gcx.definition_ident(id).symbol.as_str()));

    // Build module path from parents (skip root module).
    let mut modules: Vec<String> = vec![];
    let mut current = id;
    let mut seen: FxHashSet<hir::DefinitionID> = FxHashSet::default();
    while let Some(&parent) = output.definition_to_parent.get(&current) {
        if parent == current || !seen.insert(parent) {
            break;
        }
        current = parent;
        if matches!(
            output.definition_to_kind.get(&current),
            Some(DefinitionKind::Module)
        ) {
            if let Some(ident) = output.definition_to_ident.get(&current) {
                let name = ident.symbol.as_str();
                if !name.is_empty() {
                    modules.push(sanitize(name));
                }
            }
        }
    }
    modules.reverse();
    if !modules.is_empty() {
        modules.remove(0);
    }

    // Include extension target so associated functions don't collide.
    if let Some(parent) = output.definition_to_parent.get(&id) {
        if matches!(
            output.definition_to_kind.get(parent),
            Some(DefinitionKind::Extension)
        ) {
            if let Some(head) = gcx.get_extension_type_head(*parent) {
                modules.push(sanitize(&type_head_symbol(gcx, head)));
            }
        }
    }

    let mut mangled = if modules.is_empty() {
        format!("{pkg_ident}__{leaf_ident}")
    } else {
        format!("{pkg_ident}__{}__{leaf_ident}", modules.join("__"))
    };

    // Add hashed signature to disambiguate overloads.
    if matches!(
        output.definition_to_kind.get(&id),
        Some(DefinitionKind::Function | DefinitionKind::AssociatedFunction)
    ) {
        let sig = gcx.get_signature(id);
        let mut hasher = DefaultHasher::new();
        for input in &sig.inputs {
            ty_symbol(gcx, input.ty).hash(&mut hasher);
        }
        ty_symbol(gcx, sig.output).hash(&mut hasher);
        let hash = hasher.finish();
        mangled.push_str(&format!("__h{hash:016x}"));
    }

    mangled
}
