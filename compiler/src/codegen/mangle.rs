use crate::{
    compile::context::GlobalContext,
    hir,
    sema::{
        models::{
            ClosureKind, Const, ConstKind, ConstValue, GenericArgument, GenericParameter,
            InterfaceReference, Ty, TyKind,
        },
        resolve::models::{DefinitionKind, PrimaryType, TypeHead},
    },
    specialize::{Instance, InstanceKind},
};
use rustc_hash::FxHashSet;

const STABLE_KEY_VERSION: &str = "taro-codegen-symbol-v1";

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

fn text_key(s: &str) -> String {
    format!("{}:{s}", s.len())
}

fn stable_hash_bytes(input: &str) -> [u8; 8] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STABLE_KEY_VERSION.as_bytes());
    hasher.update(&[0]);
    hasher.update(input.as_bytes());
    let hash = hasher.finalize();
    let mut bytes = [0; 8];
    bytes.copy_from_slice(&hash.as_bytes()[..8]);
    bytes
}

pub(crate) fn stable_hash_hex16(input: &str) -> String {
    stable_hash_bytes(input)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

pub(crate) fn stable_hash_u64(input: &str) -> u64 {
    u64::from_le_bytes(stable_hash_bytes(input))
}

fn symbol_with_key(prefix: impl AsRef<str>, key: &str) -> String {
    let prefix = sanitize(prefix.as_ref());
    format!("{prefix}__k{}", stable_hash_hex16(key))
}

pub(crate) fn definition_key(id: hir::DefinitionID) -> String {
    format!("def:{}:{}", id.package().raw(), id.index().raw())
}

fn generic_parameter_key(gcx: GlobalContext<'_>, param: GenericParameter) -> String {
    let name = gcx.symbol_text(param.name);
    format!("param:{}:{}", param.index, text_key(name.as_ref()))
}

fn generic_parameter_symbol(gcx: GlobalContext<'_>, param: GenericParameter) -> String {
    let name = gcx.symbol_text(param.name);
    format!("param{}_{}", param.index, sanitize(name.as_ref()))
}

fn generic_args_key<'gcx>(gcx: GlobalContext<'gcx>, args: &[GenericArgument<'gcx>]) -> String {
    let parts = args
        .iter()
        .map(|arg| generic_arg_key(gcx, *arg))
        .collect::<Vec<_>>()
        .join(",");
    format!("args[{}]({parts})", args.len())
}

fn closure_kind_key(kind: ClosureKind) -> &'static str {
    match kind {
        ClosureKind::Fn => "fn",
        ClosureKind::FnMut => "fnmut",
        ClosureKind::FnOnce => "fnonce",
        ClosureKind::AsyncFn => "asyncfn",
        ClosureKind::AsyncFnMut => "asyncfnmut",
        ClosureKind::AsyncFnOnce => "asyncfnonce",
    }
}

pub(crate) fn const_key<'gcx>(gcx: GlobalContext<'gcx>, c: Const<'gcx>) -> String {
    let kind = match c.kind {
        ConstKind::Value(ConstValue::Integer(i)) => format!("value:int:{i}"),
        ConstKind::Value(ConstValue::Bool(b)) => format!("value:bool:{b}"),
        ConstKind::Value(ConstValue::Rune(ch)) => format!("value:rune:{}", ch as u32),
        ConstKind::Value(ConstValue::String(sym)) => {
            let text = gcx.symbol_text(sym);
            format!("value:string:{}", text_key(text.as_ref()))
        }
        ConstKind::Value(ConstValue::Float(f)) => format!("value:float:{:016x}", f.to_bits()),
        ConstKind::Value(ConstValue::Unit) => "value:unit".into(),
        ConstKind::Value(ConstValue::EnumUnitVariant(def_id)) => {
            format!("value:enum-unit:{}", definition_key(def_id))
        }
        ConstKind::Param(param) => format!("param:{}", generic_parameter_key(gcx, param)),
        ConstKind::Infer(_) => panic!("ICE: unresolved inferred const reached codegen mangling"),
    };
    format!("const<ty={};kind={kind}>", ty_key(gcx, c.ty))
}

fn const_readable_prefix<'gcx>(gcx: GlobalContext<'gcx>, c: Const<'gcx>) -> String {
    match c.kind {
        ConstKind::Value(ConstValue::Integer(i)) => format!("i{i}"),
        ConstKind::Value(ConstValue::Bool(true)) => "b1".into(),
        ConstKind::Value(ConstValue::Bool(false)) => "b0".into(),
        ConstKind::Value(ConstValue::Rune(ch)) => format!("r{}", ch as u32),
        ConstKind::Value(ConstValue::String(sym)) => {
            let text = gcx.symbol_text(sym);
            format!("s{}", sanitize(text.as_ref()))
        }
        ConstKind::Value(ConstValue::Float(f)) => format!("f{:016x}", f.to_bits()),
        ConstKind::Value(ConstValue::Unit) => "unit".into(),
        ConstKind::Value(ConstValue::EnumUnitVariant(def_id)) => {
            format!("euv{}_{}", def_id.package().raw(), def_id.index().raw())
        }
        ConstKind::Param(param) => format!("cp{}", generic_parameter_symbol(gcx, param)),
        ConstKind::Infer(_) => panic!("ICE: unresolved inferred const reached codegen mangling"),
    }
}

fn const_symbol_with<'gcx>(gcx: GlobalContext<'gcx>, c: Const<'gcx>) -> String {
    symbol_with_key(const_readable_prefix(gcx, c), &const_key(gcx, c))
}

pub(crate) fn generic_arg_key<'gcx>(
    gcx: GlobalContext<'gcx>,
    arg: GenericArgument<'gcx>,
) -> String {
    match arg {
        GenericArgument::Type(ty) => format!("type:{}", ty_key(gcx, ty)),
        GenericArgument::Const(c) => format!("const:{}", const_key(gcx, c)),
    }
}

fn generic_arg_symbol_with<'gcx>(gcx: GlobalContext<'gcx>, arg: GenericArgument<'gcx>) -> String {
    match arg {
        GenericArgument::Type(ty) => ty_symbol_with(gcx, ty),
        GenericArgument::Const(c) => const_symbol_with(gcx, c),
    }
}

pub(crate) fn interface_ref_key<'gcx>(
    gcx: GlobalContext<'gcx>,
    iface: InterfaceReference<'gcx>,
) -> String {
    let bindings = iface
        .bindings
        .iter()
        .map(|binding| {
            let name = gcx.symbol_text(binding.name);
            format!("{}={}", text_key(name.as_ref()), ty_key(gcx, binding.ty))
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "iface<id={};args={};bindings[{}]=({bindings})>",
        definition_key(iface.id),
        generic_args_key(gcx, iface.arguments.as_slice()),
        iface.bindings.len()
    )
}

pub(crate) fn ty_key<'gcx>(gcx: GlobalContext<'gcx>, ty: Ty<'gcx>) -> String {
    match ty.kind() {
        TyKind::Bool => "ty:bool".into(),
        TyKind::Rune => "ty:rune".into(),
        TyKind::String => "ty:string".into(),
        TyKind::Int(i) => format!("ty:int:{}", i.name_str()),
        TyKind::UInt(u) => format!("ty:uint:{}", u.name_str()),
        TyKind::Float(f) => format!("ty:float:{}", f.name_str()),
        TyKind::Pointer(inner, mt) => {
            format!("ty:pointer:{}:{}", mt.display_str(), ty_key(gcx, inner))
        }
        TyKind::Reference(inner, mt) => {
            format!("ty:reference:{}:{}", mt.display_str(), ty_key(gcx, inner))
        }
        TyKind::Adt(def, args) => {
            format!(
                "ty:adt:{}:{}",
                definition_key(def.id),
                generic_args_key(gcx, args.as_slice())
            )
        }
        TyKind::Array { element, len } => {
            format!(
                "ty:array<elem={};len={}>",
                ty_key(gcx, element),
                const_key(gcx, len)
            )
        }
        TyKind::Tuple(items) => {
            let parts = items
                .iter()
                .map(|item| ty_key(gcx, *item))
                .collect::<Vec<_>>()
                .join(",");
            format!("ty:tuple[{}]({parts})", items.len())
        }
        TyKind::FnPointer { inputs, output } => {
            let input_count = inputs.len();
            let inputs = inputs
                .iter()
                .map(|input| ty_key(gcx, *input))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "ty:fnptr<inputs[{}]=({inputs});output={}>",
                input_count,
                ty_key(gcx, output)
            )
        }
        TyKind::BoxedExistential { interfaces } => {
            let parts = interfaces
                .iter()
                .map(|iface| interface_ref_key(gcx, *iface))
                .collect::<Vec<_>>()
                .join(",");
            format!("ty:boxed-existential[{}]({parts})", interfaces.len())
        }
        TyKind::Alias { kind, def_id, args } => {
            format!(
                "ty:alias:{kind:?}:{}:{}",
                definition_key(def_id),
                generic_args_key(gcx, args.as_slice())
            )
        }
        TyKind::Parameter(param) => format!("ty:{}", generic_parameter_key(gcx, param)),
        TyKind::Closure {
            closure_def_id,
            kind,
            captured_generics,
            inputs,
            output,
        } => {
            let input_count = inputs.len();
            let inputs = inputs
                .iter()
                .map(|input| ty_key(gcx, *input))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "ty:closure<id={};kind={};captured={};inputs[{}]=({inputs});output={}>",
                definition_key(closure_def_id),
                closure_kind_key(kind),
                generic_args_key(gcx, captured_generics.as_slice()),
                input_count,
                ty_key(gcx, output)
            )
        }
        TyKind::Opaque(def_id) => format!("ty:opaque:{}", definition_key(def_id)),
        TyKind::Error => panic!("ICE: error type reached codegen mangling"),
        TyKind::Infer(_) => panic!("ICE: unresolved inferred type reached codegen mangling"),
        TyKind::Never => "ty:never".into(),
    }
}

fn ty_symbol_with<'gcx>(gcx: GlobalContext<'gcx>, ty: Ty<'gcx>) -> String {
    let key = ty_key(gcx, ty);
    match ty.kind() {
        TyKind::Bool => "bool".into(),
        TyKind::Rune => "rune".into(),
        TyKind::String => "str".into(),
        TyKind::Int(i) => i.name_str().into(),
        TyKind::UInt(u) => u.name_str().into(),
        TyKind::Float(f) => f.name_str().into(),
        TyKind::Pointer(_, mt) => symbol_with_key(format!("ptr{}", mt.display_str()), &key),
        TyKind::Reference(_, mt) => symbol_with_key(format!("ref{}", mt.display_str()), &key),
        TyKind::Adt(def, _) => {
            let ident = gcx.definition_ident(def.id);
            symbol_with_key(gcx.symbol_text(ident.symbol).as_ref(), &key)
        }
        TyKind::Array { .. } => symbol_with_key("array", &key),
        TyKind::Tuple(items) => symbol_with_key(format!("tuple{}", items.len()), &key),
        TyKind::FnPointer { .. } => symbol_with_key("fnptr", &key),
        TyKind::BoxedExistential { interfaces } => {
            let mut prefix = String::from("any");
            for iface in interfaces.iter() {
                let ident = gcx.definition_ident(iface.id);
                prefix.push('_');
                prefix.push_str(gcx.symbol_text(ident.symbol).as_ref());
            }
            symbol_with_key(prefix, &key)
        }
        TyKind::Alias { def_id, .. } => {
            let ident = gcx.definition_ident(def_id);
            symbol_with_key(gcx.symbol_text(ident.symbol).as_ref(), &key)
        }
        TyKind::Parameter(param) => generic_parameter_symbol(gcx, param),
        TyKind::Closure { .. } => symbol_with_key("closure", &key),
        TyKind::Opaque(_) => symbol_with_key("opaque", &key),
        TyKind::Error | TyKind::Infer(_) => unreachable!("ty_key panics before symbol formatting"),
        TyKind::Never => "never".into(),
    }
}

pub(crate) fn type_head_key(_gcx: GlobalContext<'_>, head: TypeHead) -> String {
    match head {
        TypeHead::Primary(PrimaryType::Bool) => "head:bool".into(),
        TypeHead::Primary(PrimaryType::Rune) => "head:rune".into(),
        TypeHead::Primary(PrimaryType::String) => "head:string".into(),
        TypeHead::Primary(PrimaryType::Int(i)) => format!("head:int:{}", i.name_str()),
        TypeHead::Primary(PrimaryType::UInt(u)) => format!("head:uint:{}", u.name_str()),
        TypeHead::Primary(PrimaryType::Float(f)) => format!("head:float:{}", f.name_str()),
        TypeHead::Nominal(def_id) => format!("head:nominal:{}", definition_key(def_id)),
        TypeHead::Parameter(def_id) => format!("head:parameter:{}", definition_key(def_id)),
        TypeHead::Closure(def_id) => format!("head:closure:{}", definition_key(def_id)),
        TypeHead::Reference(mt) => format!("head:reference:{}", mt.display_str()),
        TypeHead::Pointer(mt) => format!("head:pointer:{}", mt.display_str()),
        TypeHead::Tuple(len) => format!("head:tuple:{len}"),
        TypeHead::Array => "head:array".into(),
    }
}

fn type_head_symbol(gcx: GlobalContext<'_>, head: TypeHead) -> String {
    let key = type_head_key(gcx, head);
    match head {
        TypeHead::Primary(PrimaryType::Bool) => "bool".into(),
        TypeHead::Primary(PrimaryType::Rune) => "rune".into(),
        TypeHead::Primary(PrimaryType::String) => "str".into(),
        TypeHead::Primary(PrimaryType::Int(i)) => i.name_str().into(),
        TypeHead::Primary(PrimaryType::UInt(u)) => u.name_str().into(),
        TypeHead::Primary(PrimaryType::Float(f)) => f.name_str().into(),
        TypeHead::Nominal(def_id) => {
            let ident = gcx.definition_ident(def_id);
            symbol_with_key(gcx.symbol_text(ident.symbol).as_ref(), &key)
        }
        TypeHead::Parameter(def_id) => {
            let ident = gcx.definition_ident(def_id);
            symbol_with_key(gcx.symbol_text(ident.symbol).as_ref(), &key)
        }
        TypeHead::Closure(_) => symbol_with_key("closure", &key),
        TypeHead::Reference(mt) => symbol_with_key(format!("ref{}", mt.display_str()), &key),
        TypeHead::Pointer(mt) => symbol_with_key(format!("ptr{}", mt.display_str()), &key),
        TypeHead::Tuple(len) => symbol_with_key(format!("tuple{len}"), &key),
        TypeHead::Array => symbol_with_key("array", &key),
    }
}

pub fn mangle(gcx: GlobalContext<'_>, id: hir::DefinitionID) -> String {
    let output = gcx.resolution_output(id.package());

    let pkg_ident = gcx
        .package_ident(id.package())
        .unwrap_or_else(|| gcx.config.identifier.clone());
    let pkg_ident = sanitize(pkg_ident.as_ref());
    let origin_tag = if gcx.store.synthetic_definitions.borrow().contains_key(&id) {
        "syn"
    } else if gcx.is_std_package(id.package()) {
        "std"
    } else {
        "usr"
    };

    let leaf_ident = if let Some(ident) = output.definition_to_ident.get(&id) {
        sanitize(gcx.symbol_text(ident.symbol).as_ref())
    } else if gcx.get_closure_captures(id).is_some() {
        format!("closure_{}", stable_hash_hex16(&definition_key(id)))
    } else if let Some(def) = gcx.store.synthetic_definitions.borrow().get(&id) {
        sanitize(gcx.symbol_text(def.name).as_ref())
    } else {
        format!("anon_{}", stable_hash_hex16(&definition_key(id)))
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
        format!("{pkg_ident}__bt_{origin_tag}__{leaf_ident}")
    } else {
        format!(
            "{pkg_ident}__bt_{origin_tag}__{}__{leaf_ident}",
            modules.join("__")
        )
    };

    // Add a stable hashed signature to disambiguate overloads.
    if matches!(
        output.definition_to_kind.get(&id),
        Some(DefinitionKind::Function | DefinitionKind::AssociatedFunction)
    ) {
        let sig = gcx.get_signature(id);
        let input_keys = sig
            .inputs
            .iter()
            .map(|input| ty_key(gcx, input.ty))
            .collect::<Vec<_>>()
            .join(",");
        // A signature alone is not a unique callable identity. Distinct legal
        // declarations can share one, notably an inherent method and an
        // interface implementation. Include the metadata-stable definition
        // identity so LLVM never has to append order-dependent suffixes.
        let sig_key = format!(
            "definition={};signature<inputs[{}]=({input_keys});output={}>",
            definition_key(id),
            sig.inputs.len(),
            ty_key(gcx, sig.output)
        );
        mangled.push_str(&format!("__h{}", stable_hash_hex16(&sig_key)));
    }

    mangled
}

/// Mangle an Instance (specialized function) to a unique symbol name.
pub fn mangle_instance<'gcx>(gcx: GlobalContext<'gcx>, instance: Instance<'gcx>) -> String {
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
        let suffix: Vec<_> = args
            .iter()
            .map(|arg| generic_arg_symbol_with(gcx, *arg))
            .collect();
        format!("{}$${}", base, suffix.join("_"))
    }
}

#[cfg(test)]
mod tests {
    use super::{stable_hash_hex16, stable_hash_u64};

    #[test]
    fn stable_hash_helpers_are_consistent() {
        let key = "mangle-test-key";
        let hex = stable_hash_hex16(key);
        assert_eq!(hex.len(), 16);
        assert!(hex.chars().all(|ch| ch.is_ascii_hexdigit()));

        let bytes = hex
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| {
                let text = std::str::from_utf8(pair).expect("hex utf8");
                u8::from_str_radix(text, 16).expect("hex byte")
            })
            .collect::<Vec<_>>();
        let mut first_eight = [0; 8];
        first_eight.copy_from_slice(&bytes);
        assert_eq!(stable_hash_u64(key), u64::from_le_bytes(first_eight));
    }
}
