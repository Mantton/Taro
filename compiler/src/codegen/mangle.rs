use crate::{
    compile::context::GlobalContext,
    hir,
    sema::{
        models::{ConstKind, ConstValue, GenericArgument, Ty, TyKind},
        resolve::models::{DefinitionKind, PrimaryType, TypeHead},
    },
    specialize::{Instance, InstanceKind},
};
use rustc_hash::FxHashSet;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

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

fn const_symbol_with(gcx: GlobalContext, c: &crate::sema::models::Const) -> String {
    match &c.kind {
        ConstKind::Value(ConstValue::Integer(i)) => format!("i{i}"),
        ConstKind::Value(ConstValue::Bool(b)) => {
            if *b {
                "b1".into()
            } else {
                "b0".into()
            }
        }
        ConstKind::Value(ConstValue::Rune(ch)) => format!("r{}", *ch as u32),
        ConstKind::Value(ConstValue::String(sym)) => {
            let text = gcx.symbol_text(*sym);
            format!("s{}", sanitize(text.as_ref()))
        }
        ConstKind::Value(ConstValue::Float(f)) => format!("f{:x}", f.to_bits()),
        ConstKind::Value(ConstValue::Unit) => "unit".into(),
        ConstKind::Param(p) => {
            format!("cp{}", sanitize(gcx.symbol_text(p.name).as_ref()))
        }
        ConstKind::Infer(_) => "cinfer".into(),
    }
}

fn generic_arg_symbol_with(gcx: GlobalContext, arg: GenericArgument) -> String {
    match arg {
        GenericArgument::Type(ty) => ty_symbol_with(gcx, ty),
        GenericArgument::Const(c) => const_symbol_with(gcx, &c),
    }
}

fn ty_symbol_with(gcx: GlobalContext, ty: Ty) -> String {
    match ty.kind() {
        TyKind::Bool => "bool".into(),
        TyKind::Rune => "rune".into(),
        TyKind::String => "str".into(),
        TyKind::Int(i) => i.name_str().into(),
        TyKind::UInt(u) => u.name_str().into(),
        TyKind::Float(f) => f.name_str().into(),
        TyKind::Pointer(inner, mt) => {
            format!("ptr{}{}", mt.display_str(), ty_symbol_with(gcx, inner))
        }
        TyKind::Reference(inner, mt) => {
            format!("ref{}{}", mt.display_str(), ty_symbol_with(gcx, inner))
        }
        TyKind::Adt(def, args) => {
            let ident = gcx.definition_ident(def.id);
            let mut head_hash = DefaultHasher::new();
            def.id.hash(&mut head_hash);
            let mut out = format!(
                "{}{:x}",
                sanitize(gcx.symbol_text(ident.symbol).as_ref()),
                head_hash.finish()
            );

            if !args.is_empty() {
                out.push('_');
                out.push_str(
                    &args
                        .iter()
                        .map(|arg| generic_arg_symbol_with(gcx, *arg))
                        .collect::<Vec<_>>()
                        .join("_"),
                );
            }

            out
        }
        TyKind::Array { element, len } => {
            let elem = ty_symbol_with(gcx, element);
            let len_str = match len.kind {
                ConstKind::Value(ConstValue::Integer(i)) => format!("{i}"),
                ConstKind::Param(p) => sanitize(gcx.symbol_text(p.name).as_ref()),
                ConstKind::Infer(_) => "_".into(),
                _ => "c".into(),
            };
            format!("array{}_{}", elem, len_str)
        }
        TyKind::Tuple(items) => {
            let parts: Vec<_> = items.iter().map(|t| ty_symbol_with(gcx, *t)).collect();
            format!("tuple{}", parts.join("_"))
        }
        TyKind::FnPointer { .. } => "fnptr".into(),
        TyKind::BoxedExistential { interfaces } => {
            let mut parts: Vec<String> = Vec::with_capacity(interfaces.len());
            for iface in interfaces.iter() {
                let ident = gcx.definition_ident(iface.id);
                parts.push(sanitize(gcx.symbol_text(ident.symbol).as_ref()));
            }
            format!("any{}", parts.join("_"))
        }
        TyKind::Alias { def_id, args, .. } => {
            // Use alias definition name
            let ident = gcx.definition_ident(def_id);
            let mut head_hash = DefaultHasher::new();
            def_id.hash(&mut head_hash);
            let mut out = format!(
                "{}{:x}",
                sanitize(gcx.symbol_text(ident.symbol).as_ref()),
                head_hash.finish()
            );

            if !args.is_empty() {
                out.push('_');
                out.push_str(
                    &args
                        .iter()
                        .map(|arg| generic_arg_symbol_with(gcx, *arg))
                        .collect::<Vec<_>>()
                        .join("_"),
                );
            }

            out
        }
        TyKind::Parameter(p) => gcx.symbol_text(p.name).into(),
        TyKind::Closure { closure_def_id, .. } => {
            // Use a hash-based identifier for closures
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            closure_def_id.hash(&mut hasher);
            format!("closure{:x}", hasher.finish())
        }
        TyKind::Infer(_) | TyKind::Error => "<<error>>".into(),
        TyKind::Never => "never".into(),
        TyKind::Opaque(def_id) => format!("opaque{:?}", def_id),
    }
}

fn ty_symbol_for_mangle(gcx: GlobalContext, ty: Ty) -> String {
    ty_symbol_with(gcx, ty)
}

fn ty_symbol_for_instance(gcx: GlobalContext, ty: Ty) -> String {
    ty_symbol_with(gcx, ty)
}

pub fn mangle(gcx: GlobalContext, id: hir::DefinitionID) -> String {
    fn type_head_symbol(gcx: GlobalContext, head: TypeHead) -> String {
        match head {
            TypeHead::Primary(PrimaryType::Bool) => "bool".into(),
            TypeHead::Primary(PrimaryType::Rune) => "rune".into(),
            TypeHead::Primary(PrimaryType::String) => "str".into(),
            TypeHead::Primary(PrimaryType::Int(i)) => i.name_str().into(),
            TypeHead::Primary(PrimaryType::UInt(u)) => u.name_str().into(),
            TypeHead::Primary(PrimaryType::Float(f)) => f.name_str().into(),
            TypeHead::Nominal(def_id) => {
                gcx.symbol_text(gcx.definition_ident(def_id).symbol).into()
            }
            TypeHead::Closure(def_id) => {
                let mut hasher = DefaultHasher::new();
                def_id.hash(&mut hasher);
                format!("closure{:x}", hasher.finish())
            }
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

    // Check if this is a closure (synthetic definition)
    let leaf_ident = if let Some(ident) = output.definition_to_ident.get(&id) {
        sanitize(gcx.symbol_text(ident.symbol).as_ref())
    } else if gcx.get_closure_captures(id).is_some() {
        // This is a closure - generate a unique name based on def_id
        let mut hasher = DefaultHasher::new();
        id.hash(&mut hasher);
        format!("closure_{:x}", hasher.finish())
    } else {
        // Try to get from synthetic definitions, or use anonymous fallback
        if let Some(def) = gcx.store.synthetic_definitions.borrow().get(&id) {
            sanitize(gcx.symbol_text(def.name).as_ref())
        } else {
            let mut hasher = DefaultHasher::new();
            id.hash(&mut hasher);
            format!("anon_{:x}", hasher.finish())
        }
    };

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
                let name = gcx.symbol_text(ident.symbol);
                if !name.is_empty() {
                    modules.push(sanitize(name.as_ref()));
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
            Some(DefinitionKind::Impl)
        ) {
            if let Some(head) = gcx.get_impl_type_head(*parent) {
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
            ty_symbol_for_mangle(gcx, input.ty).hash(&mut hasher);
        }
        ty_symbol_for_mangle(gcx, sig.output).hash(&mut hasher);
        let hash = hasher.finish();
        mangled.push_str(&format!("__h{hash:016x}"));
    }

    mangled
}

/// Mangle an Instance (specialized function) to a unique symbol name.
pub fn mangle_instance(gcx: GlobalContext, instance: Instance) -> String {
    let def_id = match instance.kind() {
        InstanceKind::Item(def_id) => def_id,
        InstanceKind::Virtual(_) => {
            unreachable!("virtual instances do not have a global symbol")
        }
    };
    let base = mangle(gcx, def_id);
    let args = instance.args();

    if args.is_empty() {
        base
    } else {
        // Add type args suffix
        let suffix: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => ty_symbol_for_instance(gcx, *ty),
                GenericArgument::Const(c) => format!("c{:?}", c),
            })
            .collect();
        format!("{}$${}", base, suffix.join("_"))
    }
}
