use ena::unify::UnifyKey;
use rustc_hash::FxHashMap;
use std::hash::{Hash, Hasher};

use crate::{
    PackageIndex,
    compile::context::Gcx,
    hir::{self, DefinitionID, Mutability},
    interner::InternedConstArray,
    sema::{
        resolve::models::TypeHead,
        tycheck::{
            infer::keys::{FloatVarID, IntVarID, NilVarID},
            visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
        },
    },
    span::{Span, Spanned, Symbol},
    utils::intern::{Interned, List},
};

/// The interned kind is the type's identity for inference, overloads and ABI.
/// A spelling can additionally carry labeled positions through nested types.
#[derive(Clone, Copy)]
pub struct Ty<'arena>(&'arena TypeData<'arena>);

pub(crate) struct TypeData<'arena> {
    pub(crate) kind: TyKind<'arena>,
    pub(crate) canonical: Option<Ty<'arena>>,
    pub(crate) labels: &'arena [(usize, Symbol)],
}

impl PartialEq for Ty<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.canonical().0, other.canonical().0)
    }
}

impl Eq for Ty<'_> {}

impl Hash for Ty<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.canonical().0, state);
    }
}

impl std::fmt::Debug for Ty<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = Interned::new_unchecked(&self.canonical().0.kind);
        f.debug_tuple("Ty").field(&kind).finish()
    }
}

pub type TyList<'arena> = List<'arena, Ty<'arena>>;

impl<'arena> Ty<'arena> {
    pub(crate) fn from_data(data: &'arena TypeData<'arena>) -> Self {
        Ty(data)
    }

    pub fn new(k: TyKind<'arena>, gcx: Gcx<'arena>) -> Ty<'arena> {
        gcx.store.interners.intern_ty(k)
    }

    pub(crate) fn optional(self, gcx: Gcx<'arena>) -> (Self, GenericArguments<'arena>) {
        let id = gcx.std_item_def(hir::StdItem::Optional).expect("Optional type must exist");
        let adt = gcx.get_enum_definition(id).adt_def;
        let args = gcx.store.interners.intern_generic_args(vec![GenericArgument::Type(self)]);
        (Self::new(TyKind::Adt(adt, args), gcx), args)
    }

    pub fn error(gcx: Gcx<'arena>) -> Ty<'arena> {
        Ty::new(TyKind::Error, gcx)
    }

    #[inline]
    pub fn new_int(gcx: Gcx<'arena>, i: IntTy) -> Ty<'arena> {
        use IntTy::*;
        match i {
            I8 => gcx.types.int8,
            I16 => gcx.types.int16,
            I32 => gcx.types.int32,
            I64 => gcx.types.int64,
            ISize => gcx.types.int,
        }
    }

    #[inline]
    pub fn new_uint(gcx: Gcx<'arena>, i: UIntTy) -> Ty<'arena> {
        use UIntTy::*;
        match i {
            U8 => gcx.types.uint8,
            U16 => gcx.types.uint16,
            U32 => gcx.types.uint32,
            U64 => gcx.types.uint64,
            USize => gcx.types.uint,
        }
    }

    #[inline]
    pub fn new_float(gcx: Gcx<'arena>, f: FloatTy) -> Ty<'arena> {
        use FloatTy::*;
        match f {
            F32 => gcx.types.float32,
            F64 => gcx.types.float64,
        }
    }

    pub fn from_labeled_signature(
        gcx: Gcx<'arena>,
        signature: &LabeledFunctionSignature<'arena>,
    ) -> Ty<'arena> {
        let inputs: Vec<Ty<'arena>> = signature.inputs.iter().map(|param| param.ty).collect();
        let output = signature.output;

        let kind = TyKind::FnPointer {
            effects: FunctionPointerEffects {
                abi: signature.abi,
                ..Default::default()
            },
            inputs: gcx.store.interners.intern_ty_list(inputs),
            output,
        };

        Ty::new(kind, gcx)
    }

    #[inline]
    pub fn kind(self) -> TyKind<'arena> {
        self.0.kind
    }

    pub(crate) fn has_presentation(self) -> bool {
        self.0.canonical.is_some()
    }

    pub(crate) fn canonical(self) -> Self {
        self.0.canonical.unwrap_or(self)
    }

    pub(crate) fn presented(
        self,
        kind: TyKind<'arena>,
        labels: &'arena [(usize, Symbol)],
        arena: &'arena typed_arena::Arena<TypeData<'arena>>,
    ) -> Self {
        Ty(arena.alloc(TypeData {
            kind,
            labels,
            canonical: Some(self.canonical()),
        }))
    }

    pub(crate) fn tuple_labels(self) -> &'arena [(usize, Symbol)] {
        self.0.labels
    }

    pub(crate) fn labeled_tuple_field(self, name: Symbol) -> Option<(usize, Self)> {
        let TyKind::Tuple(elements) = self.kind() else {
            return None;
        };
        let &(index, _) = self
            .tuple_labels()
            .iter()
            .find(|(_, label)| *label == name)?;
        Some((index, elements[index]))
    }

    pub(crate) fn with_tuple_labels(
        self,
        labels: &'arena [(usize, Symbol)],
        gcx: Gcx<'arena>,
    ) -> Self {
        if labels.is_empty() {
            return self;
        }
        self.presented(self.kind(), labels, &gcx.store.arenas.types)
    }

    pub(crate) fn with_source_labels(
        self,
        labels: &crate::hir::TupleLabels,
        gcx: Gcx<'arena>,
    ) -> Self {
        if labels.is_empty() || !matches!(self.kind(), TyKind::Tuple(_)) {
            return self;
        }
        let labels = gcx.store.arenas.global.alloc_slice_fill_iter(
            labels
                .iter()
                .map(|(position, label)| (*position, label.symbol)),
        );
        self.with_tuple_labels(labels, gcx)
    }

    pub fn is_error(self) -> bool {
        matches!(self.kind(), TyKind::Error)
    }

    #[inline]
    pub fn is_infer(self) -> bool {
        matches!(self.kind(), TyKind::Infer(..))
    }

    #[inline]
    pub fn is_ty_var(self) -> bool {
        matches!(self.kind(), TyKind::Infer(InferTy::TyVar(_)))
    }

    /// Conservative normalization query: aliases may hide inference or projections.
    pub fn contains_inference(self) -> bool {
        struct Inference;
        impl<'ctx> TypeVisitor<'ctx> for Inference {
            fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
                matches!(ty.kind(), TyKind::Infer(_) | TyKind::Alias { .. })
                    || ty.super_visit_with(self)
            }
            fn visit_const(&mut self, value: Const<'ctx>) -> bool {
                matches!(value.kind, ConstKind::Infer(_)) || value.ty.visit_with(self)
            }
        }
        self.visit_with(&mut Inference)
    }

    pub fn is_pointer(self) -> bool {
        matches!(self.kind(), TyKind::Pointer(..) | TyKind::Reference(..))
    }

    pub fn dereference(self) -> Option<Ty<'arena>> {
        match self.kind() {
            TyKind::Reference(ty) | TyKind::Pointer(ty, _) => Some(ty),
            _ => None,
        }
    }
}

impl<'arena> Ty<'arena> {
    pub fn format(self, gcx: Gcx<'arena>) -> String {
        match self.kind() {
            TyKind::Bool => "bool".into(),
            TyKind::Rune => "rune".into(),
            TyKind::String => "string".into(),
            TyKind::Int(i) => i.name_str().into(),
            TyKind::UInt(u) => u.name_str().into(),
            TyKind::Float(f) => f.name_str().into(),
            TyKind::Array { element, len } => {
                let len_str = match len.kind {
                    ConstKind::Value(ConstValue::Integer(i)) => format!("{i}"),
                    ConstKind::Param(p) => gcx.symbol_text(p.name).into(),
                    ConstKind::Infer(_) => "_".into(),
                    _ => "<const>".into(),
                };
                format!("[{}; {}]", element.format(gcx), len_str)
            }
            TyKind::Adt(adt, args) => {
                fn write_name(gcx: Gcx<'_>, id: DefinitionID, out: &mut String) {
                    if let Some(parent) = gcx.nested_type_owner(id) {
                        write_name(gcx, parent, out);
                        out.push_str("::");
                    }
                    out.push_str(gcx.symbol_text(gcx.definition_ident(id).symbol).as_str());
                }
                let mut out = String::new();
                write_name(gcx, adt.id, &mut out);
                out.push_str(&format_generic_args(&args, gcx));
                out
            }
            TyKind::Pointer(inner, mt) => {
                format!("*{}{}", mt.display_str(), inner.format(gcx))
            }
            TyKind::Reference(inner) => {
                format!("&{}", inner.format(gcx))
            }
            TyKind::Tuple(items) => {
                let mut out = "(".to_owned();
                for (i, t) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&t.format(gcx));
                }
                if items.len() == 1 {
                    out.push(',');
                } // 1‑tuple trailing comma
                out.push(')');
                out
            }
            TyKind::FnPointer {
                inputs,
                output,
                effects,
            } => {
                let mut out = String::new();
                if effects.is_unsafe {
                    out.push_str("unsafe ");
                }
                if effects.kind == ClosureKind::AsyncFn {
                    out.push_str("async ");
                }
                if let Some(abi) = effects.abi {
                    out.push_str(&format!("extern {abi:?} "));
                }
                out.push('(');
                for (i, input) in inputs.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&input.format(gcx));
                }
                out.push_str(") -> ");
                out.push_str(&output.format(gcx));
                out
            }
            TyKind::BoxedExistential { interfaces } => {
                if interfaces.is_empty() {
                    return "any".into();
                }
                let parts: Vec<_> = interfaces.iter().map(|i| i.format(gcx)).collect();
                format!("any {}", parts.join(" & "))
            }
            TyKind::Error => "<<error>>".into(),
            TyKind::Never => "!".into(),
            TyKind::Infer(k) => match k {
                InferTy::TyVar(id) => format!("{{var({})}}", id._raw),
                InferTy::IntVar(id) => format!("{{integer({})}}", id.index()),
                InferTy::FloatVar(id) => format!("{{float({})}}", id.index()),
                InferTy::NilVar(id) => format!("{{nil({})}}", id.index()),
                InferTy::FreshTy(id) => format!("{{fresh({})}}", id),
            },
            TyKind::Parameter(p) => gcx.symbol_text(p.name).to_string(),
            TyKind::ExistentialSelf(_) => "Self".into(),
            TyKind::Alias { kind, def_id, args } => {
                if kind == AliasKind::Opaque {
                    let mut bounds = gcx
                        .constraints_of(def_id)
                        .into_iter()
                        .filter_map(|constraint| match constraint.value {
                            Constraint::Bound { ty, interface }
                                if matches!(
                                    ty.kind(),
                                    TyKind::Alias {
                                        kind: AliasKind::Opaque,
                                        def_id: bound_owner,
                                        ..
                                    } if bound_owner == def_id
                                ) =>
                            {
                                Some(interface.format(gcx))
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    bounds.sort();
                    bounds.dedup();
                    return if bounds.is_empty() {
                        "some <opaque>".into()
                    } else {
                        format!("some {}", bounds.join(" & "))
                    };
                }
                let ident = gcx.definition_ident(def_id);
                if kind == AliasKind::Projection {
                    if let Some(GenericArgument::Type(self_ty)) = args.get(0) {
                        let mut out =
                            format!("{}.{}", self_ty.format(gcx), gcx.symbol_text(ident.symbol));
                        if args.len() > 1 {
                            out.push_str(&format_generic_args(&args[1..], gcx));
                        }
                        out
                    } else {
                        // Fallback/Should not happen for valid projections
                        let mut out = String::from(gcx.symbol_text(ident.symbol).as_ref());
                        out.push_str(&format_generic_args(&args, gcx));
                        out
                    }
                } else {
                    let mut out = String::from(gcx.symbol_text(ident.symbol).as_ref());
                    out.push_str(&format_generic_args(&args, gcx));
                    out
                }
            }
            TyKind::Closure {
                kind,
                inputs,
                output,
                ..
            } => {
                let kind_name = match kind {
                    ClosureKind::Fn => "Fn",
                    ClosureKind::AsyncFn => "AsyncFn",
                };
                let mut out = format!("closure<{kind_name}>((");
                for (i, input) in inputs.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&input.format(gcx));
                }
                out.push_str(") -> ");
                out.push_str(&output.format(gcx));
                out.push(')');
                out
            }
            TyKind::Opaque(def_id) => {
                let ident = gcx.definition_ident(def_id);
                gcx.symbol_text(ident.symbol).into()
            }
        }
    }
}

// HELPERS
impl<'ctx> Ty<'ctx> {
    /// Syntactic substitution query; const inference is retained for callers
    /// that use this to decide whether a type is ready for monomorphization.
    pub fn needs_instantiation(self) -> bool {
        struct Parameters;
        impl<'ctx> TypeVisitor<'ctx> for Parameters {
            fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
                matches!(ty.kind(), TyKind::Parameter(_)) || ty.super_visit_with(self)
            }
            fn visit_const(&mut self, value: Const<'ctx>) -> bool {
                matches!(value.kind, ConstKind::Param(_) | ConstKind::Infer(_))
                    || value.ty.visit_with(self)
            }
        }
        self.visit_with(&mut Parameters)
    }

    /// Exact query for unresolved inference variables. Unlike
    /// contains_inference, aliases and projections do not count.
    pub fn has_inference_variables(self) -> bool {
        struct Variables;
        impl<'ctx> TypeVisitor<'ctx> for Variables {
            fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
                matches!(ty.kind(), TyKind::Infer(_)) || ty.super_visit_with(self)
            }
            fn visit_const(&mut self, value: Const<'ctx>) -> bool {
                matches!(value.kind, ConstKind::Infer(_)) || value.ty.visit_with(self)
            }
        }
        self.visit_with(&mut Variables)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyKind<'arena> {
    Array {
        element: Ty<'arena>,
        len: Const<'arena>,
    },
    Bool,
    Rune,
    String,
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),
    Adt(AdtDef, GenericArguments<'arena>),
    Pointer(Ty<'arena>, Mutability),
    Reference(Ty<'arena>),
    Tuple(TyList<'arena>),
    FnPointer {
        inputs: TyList<'arena>,
        output: Ty<'arena>,
        effects: FunctionPointerEffects,
    },
    BoxedExistential {
        interfaces: &'arena [InterfaceReference<'arena>],
    },
    Alias {
        kind: AliasKind,
        def_id: DefinitionID,
        args: GenericArguments<'arena>,
    },
    Infer(InferTy),
    Parameter(GenericParameter),
    /// Self bound by an erased interface, independent of outer generic indices.
    ExistentialSelf(u32),
    /// Anonymous closure type with captured environment
    Closure {
        /// Unique ID for this closure definition
        closure_def_id: DefinitionID,
        /// Whether the closure is synchronous or async.
        kind: ClosureKind,
        /// Generic arguments captured from enclosing scope
        captured_generics: GenericArguments<'arena>,
        /// Input parameter types
        inputs: TyList<'arena>,
        /// Output type
        output: Ty<'arena>,
    },
    /// Opaque external type - can only be used behind pointers
    Opaque(DefinitionID),
    Error,
    Never,
}

/// Function values preserve async, safety and ABI identity through inference
/// and metadata. Only safe Taro pointers implement the safe callable traits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionPointerEffects {
    pub kind: ClosureKind,
    pub is_unsafe: bool,
    pub abi: Option<crate::hir::Abi>,
}
impl Default for FunctionPointerEffects {
    fn default() -> Self {
        Self {
            kind: ClosureKind::Fn,
            is_unsafe: false,
            abi: None,
        }
    }
}

/// Kind of type alias
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AliasKind {
    /// Impl block associated type: `impl Foo { type Bar = Int }`
    Inherent,
    /// Top-level type alias: `type Foo = [Int]`
    Weak,
    /// Interface associated type accessed on a type parameter: `T.Item`
    Projection,
    /// Return-position opaque type owned by a concrete function or method.
    Opaque,
}

/// Classification of a closure's callable behavior
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClosureKind {
    /// Repeatable synchronous invocation over a persistent environment.
    Fn,
    /// Repeatable asynchronous invocation; each call produces its own future.
    AsyncFn,
}

/// Identify the built-in callable interfaces independently of their source spelling.
pub fn callable_kind(gcx: Gcx<'_>, interface_id: DefinitionID) -> Option<ClosureKind> {
    [
        (hir::StdItem::Fn, ClosureKind::Fn),
        (hir::StdItem::AsyncFn, ClosureKind::AsyncFn),
    ]
    .into_iter()
    .find_map(|(item, kind)| (gcx.std_item_def(item) == Some(interface_id)).then_some(kind))
}

/// Callable Args is always a tuple, including zero and one argument signatures.
pub fn callable_args_ty<'ctx>(gcx: Gcx<'ctx>, inputs: TyList<'ctx>) -> Ty<'ctx> {
    Ty::new(TyKind::Tuple(inputs), gcx)
}

/// Safe callable signature shared by closures and Taro function pointers.
pub fn callable_signature<'ctx>(ty: Ty<'ctx>) -> Option<(ClosureKind, TyList<'ctx>, Ty<'ctx>)> {
    match ty.kind() {
        TyKind::Closure {
            kind,
            inputs,
            output,
            ..
        } => Some((kind, inputs, output)),
        TyKind::FnPointer {
            inputs,
            output,
            effects,
        } if !effects.is_unsafe && effects.abi.is_none() => Some((effects.kind, inputs, output)),
        _ => None,
    }
}

/// The callable interface implemented by a concrete callable value.
pub fn callable_interface_ref<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
) -> Option<InterfaceReference<'ctx>> {
    let (kind, inputs, output) = callable_signature(ty)?;
    let item = match kind {
        ClosureKind::Fn => hir::StdItem::Fn,
        ClosureKind::AsyncFn => hir::StdItem::AsyncFn,
    };
    Some(InterfaceReference {
        id: gcx.std_item_def(item)?,
        arguments: gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(ty),
            GenericArgument::Type(callable_args_ty(gcx, inputs)),
            GenericArgument::Type(output),
        ]),
        bindings: &[],
    })
}

/// Expand a callable argument pack. Abstract tuple parameters remain opaque until
/// instantiated; they can still be forwarded to the explicit call methods.
pub fn callable_inputs<'ctx>(gcx: Gcx<'ctx>, args_ty: Ty<'ctx>) -> TyList<'ctx> {
    match crate::sema::tycheck::utils::normalize_aliases(gcx, args_ty).kind() {
        TyKind::Tuple(inputs) => inputs,
        _ => gcx.store.interners.intern_ty_list(vec![args_ty]),
    }
}

/// How a variable is captured by a closure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CaptureKind {
    ByCopy,
    /// The closure and its enclosing scope share one variable.
    ByRef,
}

/// A variable captured by a closure
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CaptureProjection<'arena> {
    pub field: crate::thir::FieldIndex,
    /// Instantiated type after selecting this stored field.
    pub ty: Ty<'arena>,
}

#[derive(Debug, Clone, Copy)]
pub struct CapturedVar<'arena> {
    /// The NodeID of the captured variable in the enclosing scope
    pub source_id: hir::NodeID,
    /// Original local type, used only to construct the projected source place.
    pub root_ty: Ty<'arena>,
    /// Named inline fields from source_id to the actual captured value.
    pub projection: &'arena [CaptureProjection<'arena>],
    /// Name of the captured variable
    pub name: Symbol,
    /// Type of the captured value (original type, not ref type)
    pub ty: Ty<'arena>,
    /// How this variable is captured.
    pub capture_kind: CaptureKind,
    /// The source binding can't change after this closure captures it.
    pub source_immutable: bool,
    /// Field index in the environment struct
    pub field_index: crate::thir::FieldIndex,
}

impl<'ctx> CapturedVar<'ctx> {
    /// The actual environment field type, rather than the type of the value
    /// seen inside the closure body. Borrow captures store a reference slot.
    pub fn storage_ty(self, gcx: Gcx<'ctx>, arguments: GenericArguments<'ctx>) -> Ty<'ctx> {
        let value = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            gcx, self.ty, arguments,
        );
        match self.capture_kind {
            CaptureKind::ByCopy => value,
            CaptureKind::ByRef => Ty::new(TyKind::Reference(value), gcx),
        }
    }
}

/// Information about a closure's captured environment
#[derive(Debug, Clone)]
pub struct ClosureCaptures<'arena> {
    /// All captured variables
    pub captures: Vec<CapturedVar<'arena>>,
    /// The callable kind inferred from body analysis.
    pub kind: ClosureKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdtKind {
    Struct,
    Enum,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AdtDef {
    pub kind: AdtKind,
    pub id: DefinitionID,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructField<'arena> {
    pub default_provider: Option<DefinitionID>,
    pub name: Symbol,
    pub ty: Ty<'arena>,
    pub mutability: Mutability,
    pub def_id: DefinitionID,
    pub visibility: crate::sema::resolve::models::Visibility,
    pub coding_key: Option<Symbol>,
    pub coding_skip: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StructRepr {
    Taro,
    C,
}

impl Default for StructRepr {
    fn default() -> Self {
        StructRepr::Taro
    }
}

/// Reference-class metadata is separate from an inline value's lifecycle.
/// The declaration's fields describe object payload storage; the value itself
/// contains one native ClassHandle. Inheritance is added by S29.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassInfo<'ctx> {
    pub base: Option<Ty<'ctx>>,
    pub methods: &'ctx [ClassMethod<'ctx>],
    pub initializers: &'ctx [ClassInitializer<'ctx>],
    /// Hidden, uniquely owned value layout used for construction and cleanup.
    pub payload: Option<DefinitionID>,
    pub is_final: bool,
}

/// Constructor categories and families survive package boundaries. A later
/// inherited entry point keeps the designated family's identity but constructs
/// the requested subclass, rather than forwarding a base-object allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassInitializer<'ctx> {
    pub definition: DefinitionID,
    pub family: DefinitionID,
    pub implementation: DefinitionID,
    pub owner: Ty<'ctx>,
    pub is_convenience: bool,
    pub is_required: bool,
    pub is_inherited: bool,
    /// Resolved self.init targets of a source convenience body. Inherited
    /// entries recover their source body instead of copying stale local facts.
    pub delegations: &'ctx [DefinitionID],
}

/// Conditional facts proved on an interface default or a blanket receiver
/// implementation before lowering. They restrict class instantiations, never
/// the body's ordinary struct callers. The historical name remains internal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ClassDefaultContract {
    pub preserves_dynamic_self: Option<bool>,
}

/// A virtual family keeps its original declaration identity across overrides.
/// owner is the implementation's class expressed in this class's parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassMethod<'ctx> {
    /// Owned result preserves the receiver's actual dynamic class. Bodies are
    /// checked before inherited calls may refine this result to their receiver.
    pub returns_self: bool,
    pub family: DefinitionID,
    pub implementation: DefinitionID,
    pub owner: Ty<'ctx>,
    pub is_final: bool,
}

/// Conformance-owned class families may be introduced after the class's package
/// was compiled. Keep them separate from its immutable nominal descriptor.
#[derive(Debug, Clone, Copy)]
pub struct ClassAdoption<'ctx> {
    pub conformance: ConformanceRecordId,
    pub methods: &'ctx [ClassWitnessMethod<'ctx>],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassWitnessMethod<'ctx> {
    pub requirement: DefinitionID,
    pub slot: ClassMethod<'ctx>,
    /// True for a late family registered through the nonnull argument-key
    /// registry, even when it has no own generic arguments. False reuses an
    /// already published inherent family and its original descriptor table.
    pub is_registered: bool,
}

#[derive(Debug, Clone)]
pub struct StructDefinition<'arena> {
    pub positional: bool,
    pub adt_def: AdtDef,
    pub class_info: Option<ClassInfo<'arena>>,
    pub has_initializer: bool,
    pub repr: StructRepr,
    pub fields: &'arena [StructField<'arena>],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumVariantField<'arena> {
    pub label: Option<Symbol>,
    pub ty: Ty<'arena>,
    pub mutability: Mutability,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EnumVariantKind<'arena> {
    Unit,
    Tuple(&'arena [EnumVariantField<'arena>]),
    Struct(&'arena [EnumVariantField<'arena>]),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumVariant<'arena> {
    pub name: Symbol,
    pub def_id: DefinitionID,
    pub ctor_def_id: DefinitionID,
    pub kind: EnumVariantKind<'arena>,
    pub discriminant: u64,
}

#[derive(Debug, Clone)]
pub struct EnumDefinition<'arena> {
    pub adt_def: AdtDef,
    pub variants: &'arena [EnumVariant<'arena>],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntTy {
    ISize,
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UIntTy {
    USize,
    U8,
    U16,
    U32,
    U64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatTy {
    F32,
    F64,
}
impl IntTy {
    pub fn name_str(&self) -> &'static str {
        match *self {
            IntTy::ISize => "isize",
            IntTy::I8 => "int8",
            IntTy::I16 => "int16",
            IntTy::I32 => "int32",
            IntTy::I64 => "int64",
        }
    }
}

impl UIntTy {
    pub fn name_str(&self) -> &'static str {
        match *self {
            UIntTy::USize => "usize",
            UIntTy::U8 => "uint8",
            UIntTy::U16 => "uint16",
            UIntTy::U32 => "uint32",
            UIntTy::U64 => "uint64",
        }
    }
}

impl FloatTy {
    pub fn name_str(self) -> &'static str {
        match self {
            FloatTy::F32 => "float",
            FloatTy::F64 => "double",
        }
    }
}

#[derive(Debug, Clone)]
pub struct LabeledFunctionSignature<'ctx> {
    pub inputs: Vec<LabeledFunctionParameter<'ctx>>,
    pub output: Ty<'ctx>,
    pub is_variadic: bool,
    pub abi: Option<crate::hir::Abi>,
}

impl<'ctx> LabeledFunctionSignature<'ctx> {
    pub fn min_parameter_count(&self) -> usize {
        self.inputs
            .len()
            .checked_sub(
                self.inputs
                    .iter()
                    .filter(|i| i.default_provider.is_some())
                    .count(),
            )
            .unwrap_or(0)
    }

    /// Compare two signatures ignoring types (`ty`, `output`).
    ///
    /// Returns `true` when:
    /// * both have the same `is_variadic` flag,
    /// * the parameter list is the same length, and
    /// * every parameter's label, evaluation mode and default-provider status match in order.
    pub fn same_shape(&self, other: &Self) -> bool {
        // Quick field/length checks first.
        if self.is_variadic != other.is_variadic || self.inputs.len() != other.inputs.len() {
            return false;
        }

        // Compare each parameter, ignoring `ty`.
        self.inputs.iter().zip(&other.inputs).all(|(a, b)| {
            a.label == b.label
                && a.is_lazy == b.is_lazy
                && a.default_provider.is_some() == b.default_provider.is_some()
        })
    }

    pub fn format_for_display(&self, gcx: Gcx<'ctx>) -> String {
        let mut out = String::new();
        out.push('(');

        for (index, _) in self.inputs.iter().enumerate() {
            if index > 0 {
                out.push_str(", ");
            }

            out.push_str(&format_parameter_for_display(self, index, gcx));
        }

        out.push_str(") -> ");
        out.push_str(&self.output.format(gcx));
        out
    }
}

pub fn lazy_parameter_result_ty<'ctx>(gcx: Gcx<'ctx>, param_ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
    let fn_id = gcx.std_item_def(hir::StdItem::Fn)?;
    let TyKind::BoxedExistential { interfaces } = param_ty.kind() else {
        return None;
    };
    let [interface] = interfaces else {
        return None;
    };
    if interface.id != fn_id {
        return None;
    }
    interface.arguments.get(2)?.ty()
}

fn format_parameter_for_display<'ctx>(
    signature: &LabeledFunctionSignature<'ctx>,
    index: usize,
    gcx: Gcx<'ctx>,
) -> String {
    let param = &signature.inputs[index];
    let is_variadic = signature.is_variadic && index + 1 == signature.inputs.len();
    if param.is_lazy
        && let Some(result) = lazy_parameter_result_ty(gcx, param.ty)
    {
        return format!("@lazy {}", result.format(gcx));
    }
    format_parameter_type_for_display(param.ty, is_variadic, gcx)
}

fn format_parameter_type_for_display<'ctx>(
    ty: Ty<'ctx>,
    is_variadic: bool,
    gcx: Gcx<'ctx>,
) -> String {
    if is_variadic && let Some(element_ty) = variadic_element_type(ty, gcx) {
        return format!("{}...", element_ty.format(gcx));
    }

    ty.format(gcx)
}

fn variadic_element_type<'ctx>(ty: Ty<'ctx>, gcx: Gcx<'ctx>) -> Option<Ty<'ctx>> {
    let span_id = gcx.std_item_def(hir::StdItem::Span)?;

    match ty.kind() {
        TyKind::Adt(adt, args) if adt.id == span_id => match args.get(0) {
            Some(GenericArgument::Type(inner)) if args.len() == 1 => Some(*inner),
            _ => None,
        },
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LabeledFunctionParameter<'ctx> {
    pub is_lazy: bool,
    pub label: Option<Symbol>,
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub default_provider: Option<DefinitionID>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constraint<'ctx> {
    /// `T == U`
    TypeEquality(Ty<'ctx>, Ty<'ctx>),
    /// `T: Interface`
    Bound {
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },
}

index_vec::define_index_type! {
    pub struct TyVarID = u32;
}

index_vec::define_index_type! {
    pub struct ConstVarID = u32;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferTy {
    TyVar(TyVarID),
    IntVar(IntVarID),
    FloatVar(FloatVarID),
    NilVar(NilVarID),
    FreshTy(u32),
}

// MARK: Generics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericParameter {
    pub index: usize,
    pub name: Symbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Const<'arena> {
    pub ty: Ty<'arena>,
    pub kind: ConstKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstKind {
    Value(ConstValue),
    Param(GenericParameter),
    Infer(ConstVarID),
}

#[derive(Debug, Clone, Copy)]
pub enum ConstValue {
    Bytes(crate::span::InternedBytes),
    Integer(i128),
    Bool(bool),
    Rune(char),
    String(crate::span::Symbol),
    Float(f64),
    Unit,
    EnumUnitVariant(DefinitionID),
    Array(InternedConstArray),
}

impl PartialEq for ConstValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => a == b,
            (ConstValue::Bool(a), ConstValue::Bool(b)) => a == b,
            (ConstValue::Rune(a), ConstValue::Rune(b)) => a == b,
            (ConstValue::Bytes(a), ConstValue::Bytes(b)) => a == b,
            (ConstValue::String(a), ConstValue::String(b)) => a == b,
            (ConstValue::Float(a), ConstValue::Float(b)) => a.to_bits() == b.to_bits(),
            (ConstValue::Unit, ConstValue::Unit) => true,
            (ConstValue::EnumUnitVariant(a), ConstValue::EnumUnitVariant(b)) => a == b,
            (ConstValue::Array(a), ConstValue::Array(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for ConstValue {}

impl Hash for ConstValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            ConstValue::Integer(v) => {
                0u8.hash(state);
                v.hash(state);
            }
            ConstValue::Bool(v) => {
                1u8.hash(state);
                v.hash(state);
            }
            ConstValue::Rune(v) => {
                2u8.hash(state);
                v.hash(state);
            }
            ConstValue::Bytes(v) => {
                7u8.hash(state);
                v.hash(state);
            }
            ConstValue::String(v) => {
                3u8.hash(state);
                v.hash(state);
            }
            ConstValue::Float(v) => {
                4u8.hash(state);
                v.to_bits().hash(state);
            }
            ConstValue::Unit => {
                5u8.hash(state);
            }
            ConstValue::EnumUnitVariant(v) => {
                6u8.hash(state);
                v.hash(state);
            }
            ConstValue::Array(v) => {
                8u8.hash(state);
                v.hash(state);
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenericArgument<'arena> {
    Type(Ty<'arena>),
    Const(Const<'arena>),
}

impl<'arena> GenericArgument<'arena> {
    pub(crate) fn has_presentation(self) -> bool {
        match self {
            Self::Type(ty) => ty,
            Self::Const(c) => c.ty,
        }
        .has_presentation()
    }

    pub(crate) fn canonical(self) -> Self {
        match self {
            Self::Type(ty) => Self::Type(ty.canonical()),
            Self::Const(c) => Self::Const(Const {
                ty: c.ty.canonical(),
                ..c
            }),
        }
    }

    pub fn ty(self) -> Option<Ty<'arena>> {
        match self {
            GenericArgument::Type(ty) => Some(ty),
            GenericArgument::Const(_) => None,
        }
    }
}

pub type GenericArguments<'arena> = List<'arena, GenericArgument<'arena>>;

/// Format generic arguments as a bracketed list, e.g., "[Int, String]"
/// Returns empty string if args is empty.
pub fn format_generic_args<'ctx>(args: &[GenericArgument<'ctx>], gcx: Gcx<'ctx>) -> String {
    if args.is_empty() {
        return String::new();
    }

    let mut out = String::from("[");
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        match arg {
            GenericArgument::Type(ty) => out.push_str(&ty.format(gcx)),
            GenericArgument::Const(c) => out.push_str(&format!("{:?}", c)),
        }
    }
    out.push(']');
    out
}
#[derive(Debug, Clone)]
pub struct Generics {
    pub parameters: Vec<GenericParameterDefinition>,
    pub has_self: bool,
    pub parent: Option<DefinitionID>,
    pub parent_count: usize,
}

impl Generics {
    pub fn explicit_parameter_count(&self) -> usize {
        self.parameters.iter().filter(|p| !p.is_anonymous).count()
    }

    pub fn total_count(&self) -> usize {
        return self.parameters.len();
    }
    pub fn is_empty(&self) -> bool {
        self.parameters.is_empty() && self.parent_count == 0
    }
    pub fn default_count(&self) -> usize {
        let mut count = 0;
        for param in self.parameters.iter() {
            match &param.kind {
                GenericParameterDefinitionKind::Type { default, .. } => {
                    if default.is_some() {
                        count += 1;
                    }
                }
                GenericParameterDefinitionKind::Const { default, .. } => {
                    if default.is_some() {
                        count += 1;
                    }
                }
            }
        }

        return count;
    }
}

#[derive(Debug, Clone)]
pub struct GenericParameterDefinition {
    /// Hidden parameters participate in inference and specialization only.
    pub is_anonymous: bool,
    pub name: Symbol,
    pub id: DefinitionID,
    pub index: usize,
    pub kind: GenericParameterDefinitionKind,
}

#[derive(Debug, Clone)]
pub enum GenericParameterDefinitionKind {
    Type {
        default: Option<Box<hir::Type>>,
    },
    Const {
        ty: Box<hir::Type>,
        default: Option<hir::AnonConst>,
    },
}

impl GenericParameterDefinitionKind {
    pub fn has_default(&self) -> bool {
        match self {
            GenericParameterDefinitionKind::Type { default, .. } => default.is_some(),
            GenericParameterDefinitionKind::Const { default, .. } => default.is_some(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct InterfaceDefinition<'ctx> {
    pub id: DefinitionID,
    pub superfaces: Vec<Spanned<InterfaceReference<'ctx>>>,
    pub assoc_types: FxHashMap<Symbol, DefinitionID>,
}

#[derive(Debug, Clone, Default)]
pub struct InterfaceRequirements<'ctx> {
    pub methods: Vec<InterfaceMethodRequirement<'ctx>>,
    pub properties: Vec<InterfacePropertyRequirement<'ctx>>,
    pub types: Vec<AssociatedTypeDefinition<'ctx>>,
    pub constants: Vec<InterfaceConstantRequirement<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct InterfaceMethodRequirement<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub signature: &'ctx LabeledFunctionSignature<'ctx>,
    pub has_self: bool,
    pub is_required: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct InterfacePropertyRequirement<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub getter_id: DefinitionID,
    pub getter_is_required: bool,
}

#[derive(Debug, Clone)]
pub struct InterfaceConstantRequirement<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub has_default: bool,
}

// For interface types (any/some Protocol)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InterfaceReference<'ctx> {
    pub id: DefinitionID,
    pub arguments: GenericArguments<'ctx>, // Self is arguments[0] when has_self
    pub bindings: &'ctx [AssociatedTypeBinding<'ctx>],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssociatedTypeBinding<'ctx> {
    pub name: Symbol,
    pub ty: Ty<'ctx>,
}

fn format_callable_interface<'ctx>(
    gcx: Gcx<'ctx>,
    interface_id: DefinitionID,
    args: &[GenericArgument<'ctx>],
) -> Option<String> {
    let kind = match callable_kind(gcx, interface_id)? {
        ClosureKind::Fn => "Fn",
        ClosureKind::AsyncFn => "AsyncFn",
    };

    if args.len() != 2 {
        return None;
    }

    let inputs_ty = match args.first() {
        Some(GenericArgument::Type(ty)) => *ty,
        _ => return None,
    };
    let output_ty = match args.get(1) {
        Some(GenericArgument::Type(ty)) => *ty,
        _ => return None,
    };

    let mut out = String::from(kind);
    out.push('(');
    match inputs_ty.kind() {
        TyKind::Tuple(items) => {
            for (i, input) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&input.format(gcx));
            }
        }
        _ => out.push_str(&inputs_ty.format(gcx)),
    }
    out.push_str(") -> ");
    out.push_str(&output_ty.format(gcx));
    Some(out)
}

impl<'ctx> InterfaceReference<'ctx> {
    pub fn self_ty(self) -> Option<Ty<'ctx>> {
        match self.arguments.first().copied() {
            Some(GenericArgument::Type(ty)) => Some(ty),
            _ => None,
        }
    }

    pub fn interface_args_without_self(self, gcx: Gcx<'ctx>) -> GenericArguments<'ctx> {
        if self.arguments.len() > 1 {
            gcx.store
                .interners
                .intern_generic_args_slice(&self.arguments[1..])
        } else {
            GenericArguments::empty()
        }
    }

    pub fn to_goal(
        self,
        gcx: Gcx<'ctx>,
        param_env: &'ctx [Constraint<'ctx>],
    ) -> Option<InterfaceGoal<'ctx>> {
        Some(self.to_goal_with_self_ty(gcx, param_env, self.self_ty()?))
    }

    pub fn to_goal_with_self_ty(
        self,
        gcx: Gcx<'ctx>,
        param_env: &'ctx [Constraint<'ctx>],
        self_ty: Ty<'ctx>,
    ) -> InterfaceGoal<'ctx> {
        InterfaceGoal {
            interface_id: self.id,
            self_ty,
            interface_args: self.interface_args_without_self(gcx),
            bindings: self.bindings,
            param_env,
        }
    }

    pub fn format(self, gcx: Gcx<'ctx>) -> String {
        let name = gcx.definition_ident(self.id).symbol;

        // Skip Self (index 0) when formatting - it's implicit
        let skip = if self.arguments.len() > 0 { 1 } else { 0 };
        let display_args = &self.arguments[skip..];

        if self.bindings.is_empty() {
            if let Some(callable) = format_callable_interface(gcx, self.id, display_args) {
                return callable;
            }
        }

        let mut out = String::from(gcx.symbol_text(name).as_ref());
        out.push_str(&format_generic_args(display_args, gcx));

        if !self.bindings.is_empty() {
            if display_args.is_empty() {
                out.push('<');
            } else {
                // Remove closing ']'
                out.pop();
                out.push_str(", ");
            }

            let bindings: Vec<_> = self
                .bindings
                .iter()
                .map(|b| format!("{} = {}", gcx.symbol_text(b.name), b.ty.format(gcx)))
                .collect();
            out.push_str(&bindings.join(", "));

            if display_args.is_empty() {
                out.push('>');
            } else {
                out.push(']');
            }
        }

        out
    }
}

#[derive(Debug, Clone)]
pub struct AssociatedTypeDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    // Optional: A default type if the implementer doesn't provide one
    pub default_type: Option<Ty<'ctx>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ConformanceRecord<'ctx> {
    pub target: TypeHead,
    pub interface: InterfaceReference<'ctx>,
    pub extension: DefinitionID,
    pub location: Span,
    pub is_conditional: bool,
    /// True if the conformance was declared inline on the type definition (struct Foo: T {}),
    /// false if declared via impl block (impl T for Foo {}). Inline conformances allow auto-synthesis.
    pub is_inline: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConformanceRecordId {
    pub package: PackageIndex,
    pub index: u32,
}

impl ConformanceRecordId {
    pub fn new(package: PackageIndex, index: u32) -> Self {
        Self { package, index }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SelectionMode {
    Typecheck,
    Codegen,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CandidateSource {
    Impl(ConformanceRecordId),
    ParamEnv,
    BuiltinTuple,
    BuiltinTupleConformance,
    BuiltinCallable,
    BuiltinClone,
    BuiltinAnyObject,
    BuiltinOperator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InterfaceGoal<'ctx> {
    pub interface_id: DefinitionID,
    pub self_ty: Ty<'ctx>,
    /// Interface arguments excluding the implicit Self argument.
    pub interface_args: GenericArguments<'ctx>,
    pub bindings: &'ctx [AssociatedTypeBinding<'ctx>],
    pub param_env: &'ctx [Constraint<'ctx>],
}

impl<'ctx> InterfaceGoal<'ctx> {
    pub fn to_interface_ref(self, gcx: Gcx<'ctx>) -> InterfaceReference<'ctx> {
        let mut args = Vec::with_capacity(self.interface_args.len() + 1);
        args.push(GenericArgument::Type(self.self_ty));
        args.extend(self.interface_args.iter().copied());
        InterfaceReference {
            id: self.interface_id,
            arguments: gcx.store.interners.intern_generic_args(args),
            bindings: self.bindings,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CanonicalGoalKey<'ctx> {
    pub package: PackageIndex,
    pub mode: SelectionMode,
    pub interface_id: DefinitionID,
    pub self_ty: Ty<'ctx>,
    pub interface_args: GenericArguments<'ctx>,
    pub bindings: &'ctx [AssociatedTypeBinding<'ctx>],
    pub param_env: &'ctx [Constraint<'ctx>],
}

impl<'ctx> CanonicalGoalKey<'ctx> {
    pub fn from_goal(
        package: PackageIndex,
        mode: SelectionMode,
        goal: InterfaceGoal<'ctx>,
    ) -> Self {
        Self {
            package,
            mode,
            interface_id: goal.interface_id,
            self_ty: goal.self_ty,
            interface_args: goal.interface_args,
            bindings: goal.bindings,
            param_env: goal.param_env,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GoalResult {
    Proven,
    NoSolution,
    Ambiguous,
}

#[derive(Debug, Clone)]
pub struct SelectedImpl<'ctx> {
    pub source: CandidateSource,
    pub extension_id: Option<DefinitionID>,
    pub record_id: Option<ConformanceRecordId>,
    pub subst: GenericArguments<'ctx>,
    pub obligations: Vec<InterfaceGoal<'ctx>>,
}

#[derive(Debug, Clone)]
pub enum SelectionResult<'ctx> {
    Selected(SelectedImpl<'ctx>),
    Ambiguous(Vec<SelectedImpl<'ctx>>),
    NoSolution(Vec<SelectionError<'ctx>>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SelectionError<'ctx> {
    NoCandidates(InterfaceGoal<'ctx>),
    Ambiguous(InterfaceGoal<'ctx>),
    ObligationFailed {
        candidate: CandidateSource,
        obligation: InterfaceGoal<'ctx>,
    },
}

/// Witness mappings for a conformance - maps interface requirements to implementations
#[derive(Debug, Clone, Default)]
pub struct ConformanceWitness<'ctx> {
    /// Maps interface method → implementing method
    pub method_witnesses: FxHashMap<DefinitionID, MethodWitness<'ctx>>,
    /// Maps interface constant → implementing constant
    pub constant_witnesses: FxHashMap<DefinitionID, DefinitionID>,
    /// Maps interface associated type → concrete type
    pub type_witnesses: FxHashMap<DefinitionID, Ty<'ctx>>,
    /// The ID of the extension or definition providing compliance.
    pub extension_id: Option<DefinitionID>,
}

/// How a method requirement is satisfied in a conformance.
#[derive(Debug, Clone, Copy)]
pub enum MethodImplementation {
    /// User-provided implementation.
    Concrete(DefinitionID),
    /// Compiler-synthesized implementation.
    /// The DefinitionID is populated during THIR synthesis to allow linkage.
    Synthetic(SyntheticMethodKind, Option<DefinitionID>),
    /// Default implementation from interface definition.
    Default(DefinitionID),
}

impl MethodImplementation {
    /// Returns the implementing definition ID for concrete/default implementations.
    /// Returns None for synthetic implementations (which require special code generation).
    pub fn impl_id(self) -> Option<DefinitionID> {
        match self {
            MethodImplementation::Concrete(id) | MethodImplementation::Default(id) => Some(id),
            MethodImplementation::Synthetic(_, id) => id,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SyntheticDefinition<'arena> {
    pub kind: SyntheticDefinitionKind,
    pub name: crate::span::Symbol,
    pub generics: &'arena Generics,
    pub signature: &'arena LabeledFunctionSignature<'arena>,
    pub span: crate::span::Span,
}

/// Code-generation behavior of a compiler-generated declaration. Drop glue has
/// no shared MIR body: its concrete value layout is known at instantiation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntheticDefinitionKind {
    /// Ordinary derived codec body with a nominal class method environment.
    ClassEncoder {
        class: DefinitionID,
    },
    /// Decodable's factory forwards to a checked decoding initializer family.
    ClassDecoder {
        class: DefinitionID,
        initializer: DefinitionID,
    },
    /// Required designated decoder synthesized for this exact class level.
    ClassDecodingInitializer {
        class: DefinitionID,
    },
    /// A nominal value type, not a callable declaration. Its fields are the
    /// class's object storage; the public class value remains a GC object handle.
    ClassPayload {
        class: DefinitionID,
    },
    /// Checked initializer body returning initialized object storage.
    ClassPayloadInitializer {
        class: DefinitionID,
        initializer: DefinitionID,
    },
    /// Concrete subclass constructor forwarding an inherited designated entry.
    /// Its body builds a nested base payload; it never allocates a base object.
    InheritedClassInitializer {
        class: DefinitionID,
        initializer: DefinitionID,
    },
    /// Non-callable generic scope: nominal parameters precede the base
    /// constructor's parent parameters; init-own generics stay separate.
    InitializerEnvironment {
        class: DefinitionID,
        initializer: DefinitionID,
    },
    /// A default argument needs the inherited constructor's substitution, not
    /// the source extension's original parameter positions.
    InheritedInitializerDefault {
        initializer: DefinitionID,
        provider: DefinitionID,
    },
    /// Native forwarding stub: the private descriptor selects the concrete
    /// constructor family, while remaining arguments keep the source ABI.
    ClassInitializerDispatch {
        initializer: DefinitionID,
    },
    /// Private body of a source convenience initializer. Its context input is
    /// forwarded through delegation; self is an ordinary initialized handle.
    ClassConvenienceInitializer {
        initializer: DefinitionID,
    },
    /// Zero-argument factory for immutable, process-long class metadata.
    ClassConstructionDescriptor {
        class: DefinitionID,
    },
    /// Consume a copied strong class handle and return its process-long actual
    /// class descriptor. Used by dynamic Self factories, never a source API.
    ClassObjectDescriptor {
        class: DefinitionID,
    },
    /// Exact generic default body, outside its interface's witness lookup.
    /// A class adoption forwards here; ordinary calls within the body still
    /// use normal interface/virtual dispatch. Its generic coordinates are
    /// identical to source, so checked MIR can be reused without type rebasing.
    ClassDefaultBody {
        source: DefinitionID,
    },
    /// An overridable, conformance-owned entry forwarding to an exact default
    /// body. Generic coordinates belong to the adopting extension, not P.
    AdoptedClassDefault {
        conformance: ConformanceRecordId,
        source: DefinitionID,
    },
    /// Conformance-owned forwarder through a resolved stored field.
    DelegatedMethod {
        conformance: ConformanceRecordId,
        source: DefinitionID,
        field: u32,
        borrow_field: bool,
    },
    /// Rebase a default argument into its adopted entry's generic environment.
    AdoptedClassDefaultArgument {
        method: DefinitionID,
        provider: DefinitionID,
    },
    /// Exact checked extraction; ordinary checked MIR owns both result arms.
    ErasedTakeAs {
        context: DefinitionID,
    },
    /// Checked optional view of the exact stored concrete type.
    ErasedAsRef {
        context: DefinitionID,
    },
    /// Private Native projection used only after an exact stored-type test.
    ErasedPayloadReference {
        context: DefinitionID,
    },
    /// Evaluate a default provider with the concrete generic type selected
    /// from one borrowed, already prepared call argument.
    StaticInitializer {
        storage: DefinitionID,
    },
    StaticReference {
        storage: DefinitionID,
    },
    ErasedAsyncSelf {
        context: DefinitionID,
        method: DefinitionID,
    },
    ErasedAsyncSelfDefault {
        adapter: DefinitionID,
        provider: DefinitionID,
    },
    ErasedDefault {
        source: DefinitionID,
        provider: DefinitionID,
        parameter: usize,
    },
    Ordinary,
    /// Compiler-generated C-unwind callback used by the runtime async driver.
    /// Its three raw pointer inputs / u8 status have a C ABI, not a public
    /// source-call ownership contract or a suspension-safety certificate.
    AsyncPoll,
    /// Generic intrinsic Clone, materialized for each full concrete type.
    BuiltinCopyClone,
    /// Pack-adapting witness instantiated for a safe function-pointer signature.
    FunctionPointerCall {
        is_async: bool,
    },
    /// Ordered element-wise tuple Clone with initialized-prefix cleanup.
    TupleClone,
    /// Ordered fixed-array element Clone with initialized-prefix cleanup.
    ArrayClone,
    /// Owned closure environment Clone in first lexical capture order.
    ClosureClone,
    /// Primitive operator witnesses are instantiated in the consuming package
    /// so checked arithmetic follows that package's compilation profile.
    PrimitiveOperator(crate::hir::StdItem),
    /// Built-in structural tuple conformance (`PartialEq`, `Hashable`,
    /// `PartialOrd`, `Ord`, `Default`, `Debug`), materialized per concrete tuple.
    TupleConformance(crate::hir::StdItem),
}

impl SyntheticDefinitionKind {
    pub fn is_instance_generated(self) -> bool {
        self.is_builtin_clone()
            || self.is_primitive_operator()
            || self.is_tuple_conformance()
            || matches!(self, Self::FunctionPointerCall { .. })
    }

    pub fn is_builtin_clone(self) -> bool {
        matches!(
            self,
            Self::BuiltinCopyClone | Self::TupleClone | Self::ArrayClone | Self::ClosureClone
        )
    }

    pub fn is_primitive_operator(self) -> bool {
        matches!(self, Self::PrimitiveOperator(_))
    }

    pub fn is_tuple_conformance(self) -> bool {
        matches!(self, Self::TupleConformance(_))
    }
}

/// Kind of synthesized method for code generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntheticMethodKind {
    /// Intrinsic Clone whose specified operation is a copy (`*self`).
    CopyClone,
    /// Nominal Clone: call Clone on each field, regardless of Copy.
    MemberwiseClone,
    /// Hashable.hash: hash each field
    MemberwiseHash,
    /// PartialEq.eq: compare each field for equality
    MemberwiseEquality,
    /// Fn.call: invoke closure with shared access.
    ClosureCall,
    /// Struct fields encoded through the format-neutral codec.
    MemberwiseEncode,
    /// Struct fields decoded through the format-neutral codec.
    MemberwiseDecode,
    /// PartialOrd.partialCmp: lexicographic over fields, enum cases by declaration order.
    MemberwisePartialOrder,
    /// Ord.cmp: lexicographic over fields, enum cases by declaration order.
    MemberwiseTotalOrder,
    /// Default.default: each field's declared default, else its type's Default.
    MemberwiseDefault,
    /// Debug.debug: the type or case name, then each field's own debug text.
    MemberwiseDebug,
    EnumRawValue,
    EnumFromRawValue,
    EnumCaseName,
    EnumCaseAt,
    /// Getter synthesized from a stored field.
    PropertyFieldGetter(usize),
}

/// Mapping from an interface method to its implementation and instantiation template.
#[derive(Debug, Clone, Copy)]
pub struct MethodWitness<'ctx> {
    /// How this method is implemented (concrete, synthetic, or default).
    pub implementation: MethodImplementation,
    /// Generic argument template expressed in terms of the interface method's params.
    pub args_template: GenericArguments<'ctx>,
}

/// Definition of a type alias (top-level or associated)
#[derive(Debug, Clone, Default)]
pub struct PackageAliasTable {
    pub aliases: FxHashMap<DefinitionID, AliasDefinition>,
    /// Source definitions for transparent interface-set aliases in the package
    /// currently being compiled. Dependencies use their resolved metadata form.
    pub interface_sets: FxHashMap<DefinitionID, InterfaceAliasDefinition>,
    pub by_type: FxHashMap<TypeHead, AliasBucket>,
}

#[derive(Default, Debug, Clone)]
pub struct AliasBucket {
    /// All aliases visible on this type head, grouped by name.
    /// Multiple entries are allowed per name (for different impl blocks).
    pub aliases: FxHashMap<Symbol, Vec<(DefinitionID, Span)>>,
}

#[derive(Debug, Clone)]
pub struct AliasDefinition {
    pub id: DefinitionID,
    pub name: Symbol,
    pub kind: AliasKind,
    pub span: Span,
    /// The HIR type to lower
    pub ast_ty: Box<hir::Type>,
    /// For Inherent aliases - which extension declared it
    pub extension_id: Option<DefinitionID>,
}

#[derive(Debug, Clone)]
pub struct InterfaceAliasDefinition {
    pub id: DefinitionID,
    pub name: Symbol,
    pub span: Span,
    /// Constituent interface paths, retained until semantic lowering expands
    /// nested aliases and generic arguments.
    pub interfaces: Vec<hir::PathNode>,
}

#[cfg(test)]
mod tests {
    use super::{
        AssociatedTypeBinding, GenericArguments, GenericParameter, InferTy, InterfaceReference, Ty,
        TyKind, TyVarID,
    };
    use crate::{
        PackageIndex, compile::context::Gcx, hir::DefinitionID,
        sema::resolve::models::DefinitionIndex, test_support::with_test_gcx,
    };
    use std::rc::Rc;

    fn dummy_definition(index: u32) -> DefinitionID {
        DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(index))
    }

    fn boxed_existential_with_binding<'ctx>(gcx: Gcx<'ctx>, binding_ty: Ty<'ctx>) -> Ty<'ctx> {
        let binding = AssociatedTypeBinding {
            name: gcx.intern_symbol("Item"),
            ty: binding_ty,
        };
        let bindings = gcx.store.arenas.global.alloc_slice_copy(&[binding]);
        let iface = InterfaceReference {
            id: dummy_definition(10),
            arguments: GenericArguments::empty(),
            bindings,
        };
        let interfaces = gcx.store.arenas.global.alloc_slice_copy(&[iface]);
        Ty::new(TyKind::BoxedExistential { interfaces }, gcx)
    }

    #[test]
    fn boxed_existential_binding_counts_as_inference() {
        with_test_gcx(|gcx| {
            let infer_ty = Ty::new(TyKind::Infer(InferTy::TyVar(TyVarID::from_raw(0))), gcx);
            let existential = boxed_existential_with_binding(gcx, infer_ty);

            assert!(existential.contains_inference());
        });
    }

    #[test]
    fn boxed_existential_binding_counts_as_needing_instantiation() {
        with_test_gcx(|gcx| {
            let param_ty = Ty::new(
                TyKind::Parameter(GenericParameter {
                    index: 0,
                    name: gcx.intern_symbol("T"),
                }),
                gcx,
            );
            let existential = boxed_existential_with_binding(gcx, param_ty);

            assert!(existential.needs_instantiation());
        });
    }
    #[test]
    fn closure_inference_is_normalized_in_all_children() {
        use crate::sema::models::{ClosureKind, GenericArgument};
        use crate::sema::tycheck::{
            infer::InferCtx,
            utils::{ParamEnv, normalize_ty, unify::TypeUnifier},
        };
        with_test_gcx(|gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let inferred =
                icx.next_ty_var(crate::span::Span::empty(crate::span::FileID::from_raw(0)));
            TypeUnifier::new(icx.clone())
                .unify(inferred, gcx.types.int32)
                .unwrap();
            let closure = Ty::new(
                TyKind::Closure {
                    closure_def_id: dummy_definition(20),
                    kind: ClosureKind::Fn,
                    captured_generics: gcx
                        .store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(inferred)]),
                    inputs: gcx.store.interners.intern_ty_list(vec![inferred]),
                    output: inferred,
                },
                gcx,
            );
            let normalized = normalize_ty(icx, closure, &ParamEnv::default());
            let TyKind::Closure {
                captured_generics,
                inputs,
                output,
                ..
            } = normalized.kind()
            else {
                panic!("closure");
            };
            assert_eq!(captured_generics[0], GenericArgument::Type(gcx.types.int32));
            assert_eq!(inputs[0], gcx.types.int32);
            assert_eq!(output, gcx.types.int32);
        });
    }

    #[test]
    fn array_length_inference_is_normalized() {
        use crate::sema::models::{ConstKind, ConstValue};
        use crate::sema::tycheck::{
            infer::{
                InferCtx,
                keys::{ConstVarValue, ConstVariableOrigin},
            },
            utils::{ParamEnv, normalize_ty},
        };
        with_test_gcx(|gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let len = icx.new_const_var(
                gcx.types.uint,
                ConstVariableOrigin {
                    location: crate::span::Span::empty(crate::span::FileID::from_raw(0)),
                    param_name: None,
                },
            );
            let ConstKind::Infer(id) = len.kind else {
                panic!("inference variable");
            };
            icx.instantiate_const_var_raw(id, ConstVarValue::Known(ConstValue::Integer(2)));
            let array = Ty::new(
                TyKind::Array {
                    element: gcx.types.int32,
                    len,
                },
                gcx,
            );
            let TyKind::Array { len, .. } = normalize_ty(icx, array, &ParamEnv::default()).kind()
            else {
                panic!("array");
            };
            assert_eq!(len.kind, ConstKind::Value(ConstValue::Integer(2)));
        });
    }
    #[test]
    fn structural_queries_preserve_alias_and_parameter_policies() {
        use crate::sema::models::{AliasKind, Const, ConstKind, ConstVarID, GenericArgument};
        use crate::sema::tycheck::utils::unresolved::{
            contains_unresolved_generics, ty_contains_unresolved_inference,
        };
        with_test_gcx(|gcx| {
            let alias = Ty::new(
                TyKind::Alias {
                    kind: AliasKind::Weak,
                    def_id: dummy_definition(30),
                    args: GenericArguments::empty(),
                },
                gcx,
            );
            assert!(
                alias.contains_inference(),
                "aliases must still trigger normalization"
            );
            assert!(
                !ty_contains_unresolved_inference(alias),
                "an alias is not itself an inference variable"
            );
            assert!(!alias.needs_instantiation());
            assert!(contains_unresolved_generics(alias));

            let inferred_const = Const {
                ty: gcx.types.uint,
                kind: ConstKind::Infer(ConstVarID::from_raw(0)),
            };
            let array = Ty::new(
                TyKind::Array {
                    element: gcx.types.int32,
                    len: inferred_const,
                },
                gcx,
            );
            assert!(ty_contains_unresolved_inference(array));
            assert!(array.needs_instantiation());
            assert!(contains_unresolved_generics(array));

            let generic = GenericArgument::Type(Ty::new(
                TyKind::Parameter(GenericParameter {
                    index: 0,
                    name: gcx.intern_symbol("T"),
                }),
                gcx,
            ));
            let interface = InterfaceReference {
                id: dummy_definition(31),
                arguments: gcx.store.interners.intern_generic_args(vec![generic]),
                bindings: &[],
            };
            assert!(contains_unresolved_generics(interface));
        });
    }

    #[test]
    fn resolving_const_parameters_releases_the_table_before_resolving_their_type() {
        use crate::sema::models::ConstKind;
        use crate::sema::tycheck::infer::{
            InferCtx,
            keys::{ConstVarValue, ConstVariableOrigin},
        };
        use crate::sema::tycheck::utils::unify::TypeUnifier;
        with_test_gcx(|gcx| {
            let icx = Rc::new(InferCtx::new(gcx));
            let span = crate::span::Span::empty(crate::span::FileID::from_raw(0));
            let inferred_ty = icx.next_ty_var(span);
            TypeUnifier::new(icx.clone())
                .unify(inferred_ty, gcx.types.uint)
                .unwrap();
            let value = icx.new_const_var(
                inferred_ty,
                ConstVariableOrigin {
                    location: span,
                    param_name: None,
                },
            );
            let ConstKind::Infer(id) = value.kind else {
                panic!("const variable");
            };
            let param = GenericParameter {
                index: 0,
                name: gcx.intern_symbol("N"),
            };
            icx.instantiate_const_var_raw(id, ConstVarValue::Param(param));
            for resolved in [
                icx.resolve_const_if_possible(value),
                icx.resolve_vars_if_possible(value),
                icx.resolve_vars_or_error(value),
            ] {
                assert_eq!(resolved.ty, gcx.types.uint);
                assert_eq!(resolved.kind, ConstKind::Param(param));
            }
        });
    }
}
