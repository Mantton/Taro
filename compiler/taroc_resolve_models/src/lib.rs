use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::{Cell, RefCell};
use taroc_data_structures::Interned;
use taroc_hir::{
    DefinitionID, DefinitionKind, NodeID, PartialRes, Path, Resolution, SymbolNamespace,
};
use taroc_span::{FileID, Identifier, Span, Symbol};

#[derive(Clone, Copy)]
pub struct DefinitionContext<'arena>(pub Interned<'arena, DefContextData<'arena>>);

pub struct DefContextData<'arena> {
    pub parent: Option<DefinitionContext<'arena>>,
    pub kind: DefContextKind,
    pub span: Span,
    pub resolutions: RefCell<ContextResolutions<'arena>>,
    pub glob_exports: RefCell<Vec<ExternalDefinitionUsage<'arena>>>,
    pub glob_imports: RefCell<Vec<ExternalDefinitionUsage<'arena>>>,
}

impl<'arena> DefinitionContext<'arena> {
    pub fn new(data: Interned<'arena, DefContextData<'arena>>) -> DefinitionContext<'arena> {
        DefinitionContext(data)
    }

    pub fn def_id(&self) -> Option<DefinitionID> {
        match &self.0.kind {
            DefContextKind::Block => None,
            DefContextKind::File => None,
            DefContextKind::Definition(definition_id, ..) => Some(*definition_id),
        }
    }

    pub fn resolution(&self) -> Option<Resolution> {
        match self.kind {
            DefContextKind::Block => None,
            DefContextKind::File => None,
            DefContextKind::Definition(id, kind, _) => Some(Resolution::Definition(id, kind)),
        }
    }
}

impl<'arena> std::ops::Deref for DefinitionContext<'arena> {
    type Target = DefContextData<'arena>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DefContextKind {
    Block,
    File,
    Definition(DefinitionID, DefinitionKind, Symbol),
}

impl DefContextKind {
    pub fn is_module_kind(self) -> bool {
        match self {
            DefContextKind::Definition(_, k, _)
                if matches!(k, DefinitionKind::Module | DefinitionKind::Namespace) =>
            {
                true
            }
            _ => false,
        }
    }

    pub fn name(self) -> Symbol {
        match self {
            DefContextKind::Block => Symbol::with("BLOCK"),
            DefContextKind::File => Symbol::with("FILE"),
            DefContextKind::Definition(_, _, s) => s,
        }
    }
}

#[derive(Clone, Copy)]
pub enum NameHolder<'arena> {
    Single(NameBinding<'arena>),
    Set(&'arena [NameBinding<'arena>]),
}

impl<'arena> NameHolder<'arena> {
    pub fn nearest(&self) -> NameBinding<'arena> {
        match self {
            NameHolder::Single(v) => *v,
            NameHolder::Set(set) => *set.iter().next().expect("non-empty set"),
        }
    }

    pub fn all(&self) -> Vec<NameBinding<'arena>> {
        match self {
            NameHolder::Single(v) => vec![*v],
            NameHolder::Set(set) => set.iter().map(|v| *v).collect(),
        }
    }

    pub fn resolution(self) -> Resolution {
        match self {
            NameHolder::Single(value) => value.resolution(),
            NameHolder::Set(values) => {
                let mut set = FxHashSet::default();
                for value in values.iter() {
                    let id = value.def_id().expect("function set must provide def id");
                    set.insert(id);
                }
                Resolution::FunctionSet(set)
            }
        }
    }

    pub fn context(self) -> Option<DefinitionContext<'arena>> {
        match self {
            NameHolder::Single(value) => value.context(),
            NameHolder::Set(_) => None,
        }
    }
}
pub type NameBinding<'arena> = Interned<'arena, NameBindingData<'arena>>;
pub struct NameBindingData<'arena> {
    pub kind: NameBindingKind<'arena>,
    pub span: Span,
    pub vis: taroc_hir::TVisibility,
}

impl<'arena> NameBindingData<'arena> {
    pub fn def_id(&self) -> Option<DefinitionID> {
        match &self.kind {
            NameBindingKind::Resolution(resolution) => resolution.def_id(),
            NameBindingKind::Context(context) => context.def_id(),
            NameBindingKind::ExternalUsage { binding, .. } => binding.def_id(),
        }
    }

    pub fn resolution(&self) -> Resolution {
        match &self.kind {
            NameBindingKind::Resolution(resolution) => resolution.clone(),
            NameBindingKind::Context(context) => context
                .resolution()
                .expect("definition context MUST have self resolution"),
            NameBindingKind::ExternalUsage { binding, .. } => binding.resolution(),
        }
    }

    pub fn context(&self) -> Option<DefinitionContext<'arena>> {
        match &self.kind {
            NameBindingKind::Resolution(..) => None,
            NameBindingKind::Context(context) => Some(*context),
            NameBindingKind::ExternalUsage { binding, .. } => binding.context(),
        }
    }

    pub fn is_function(&self) -> bool {
        match &self.kind {
            NameBindingKind::Resolution(Resolution::Definition(_, DefinitionKind::Function)) => {
                true
            }
            NameBindingKind::ExternalUsage { binding, .. } => binding.is_function(),
            _ => false,
        }
    }
}

pub enum NameBindingKind<'arena> {
    Resolution(Resolution),
    Context(DefinitionContext<'arena>),
    ExternalUsage {
        binding: NameBinding<'arena>,
        usage: ExternalDefinitionUsage<'arena>,
    },
}

pub type ExternalDefinitionUsage<'arena> = Interned<'arena, ExternalDefUsageData<'arena>>;

pub struct ExternalDefUsageData<'arena> {
    pub span: Span,
    pub module_path: Vec<Segment>,
    pub module_context: Cell<Option<DefinitionContext<'arena>>>,
    pub file: FileID,
    pub kind: ExternalDefUsageKind<'arena>,
    pub root_id: NodeID,
    pub root_span: Span,
    pub is_import: bool,
}

pub enum ExternalDefUsageKind<'arena> {
    Single(DefUsageBinding<'arena>),
    Glob { id: NodeID },
}

pub struct DefUsageBinding<'arena> {
    pub source: Identifier,
    pub target: Identifier,
    pub parent: DefinitionContext<'arena>,
    pub source_binding: RefCell<Option<NameHolder<'arena>>>,
    pub target_binding: RefCell<Option<NameHolder<'arena>>>,
    pub id: NodeID,
    pub is_nested: bool,
}

#[derive(Default)]
pub struct ContextResolutions<'arena> {
    pub bindings: FxHashMap<Symbol, NameHolder<'arena>>,
}

impl<'arena> ContextResolutions<'arena> {
    pub fn contains(&self, symbol: &Symbol) -> bool {
        self.bindings.contains_key(symbol)
    }

    pub fn find(&self, symbol: &Symbol) -> Option<NameHolder<'arena>> {
        self.bindings.get(symbol).map(|v| *v)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Segment {
    pub identifier: Identifier,
    pub id: Option<NodeID>,
    pub has_generic_args: bool,
    pub args_span: Span,
}

impl Segment {
    pub fn from_path(path: &Path) -> Vec<Segment> {
        path.segments.iter().map(|s| s.into()).collect()
    }

    pub fn from_ident(ident: Identifier) -> Segment {
        Segment {
            identifier: ident,
            id: None,
            has_generic_args: false,
            args_span: Span::empty(ident.span.file),
        }
    }

    pub fn from_ident_and_id(ident: Identifier, id: NodeID) -> Segment {
        Segment {
            identifier: ident,
            id: Some(id),
            has_generic_args: false,
            args_span: Span::empty(ident.span.file),
        }
    }
}

impl<'a> From<&'a taroc_hir::PathSegment> for Segment {
    fn from(segment: &'a taroc_hir::PathSegment) -> Segment {
        let has_generic_args = segment.arguments.is_some();
        Segment {
            identifier: segment.identifier,
            id: Some(segment.id),
            has_generic_args,
            args_span: Span::empty(segment.identifier.span.file),
        }
    }
}

// MARK: PathResult
pub enum PathResult<'arena> {
    Context(DefinitionContext<'arena>),
    NonContext(PartialRes),
    Indeterminate,
    Failed {
        segment: Identifier,
        is_last_segment: bool,
    },
}

#[derive(PartialEq)]
pub enum PatBoundCtx {
    /// A product pattern context, e.g., `Variant(a, b)`.
    Product,
    /// An or-pattern context, e.g., `p_0 | ... | p_n`.
    Or,
}

#[derive(Debug, Clone, Copy)]
pub enum PatternSource {
    Variable,
    FunctionParameter,
}

#[derive(Debug, Clone, Copy)]
pub enum Determinacy {
    Determined,
    Undetermined,
}

pub enum ResolutionError {
    FailedToResolve { segment: Symbol },
    Ambiguous { segment: Symbol },
    IdentifierBoundMoreThanOnceInParameterList,
    IdentifierBoundMoreThanOnceInSamePattern,
}

#[derive(Clone, Copy)]
pub enum PathSource {
    Type,
    Interface,
    Expression, // TODO: Method Call For Checking Constructor
}

impl PathSource {
    pub fn namespace(&self) -> SymbolNamespace {
        match self {
            PathSource::Type | PathSource::Interface => SymbolNamespace::Type,
            PathSource::Expression => SymbolNamespace::Value,
        }
    }

    pub fn is_allowed(&self, res: &Resolution) -> bool {
        match self {
            PathSource::Type => {
                matches!(
                    res,
                    Resolution::Definition(
                        _,
                        DefinitionKind::Struct
                            | DefinitionKind::Enum
                            | DefinitionKind::Interface
                            | DefinitionKind::TypeParameter
                            | DefinitionKind::TypeAlias,
                    ) | Resolution::SelfTypeAlias(..)
                        | Resolution::InterfaceSelfTypeAlias(..)
                )
            }
            PathSource::Interface => {
                matches!(res, Resolution::Definition(_, DefinitionKind::Interface))
            }
            PathSource::Expression => matches!(
                res,
                Resolution::Definition(
                    _,
                    DefinitionKind::Function
                        | DefinitionKind::Constructor(..)
                        | DefinitionKind::Struct
                        | DefinitionKind::Variant
                        | DefinitionKind::Variable
                ) | Resolution::Local(..)
                    | Resolution::FunctionSet(..)
            ),
        }
    }

    pub fn defer_to_typecheck(&self) -> bool {
        match self {
            PathSource::Type | PathSource::Expression => true,
            PathSource::Interface => false,
        }
    }

    pub fn expected(&self) -> String {
        match self {
            PathSource::Type => "type".into(),
            PathSource::Interface => "interface".into(),
            PathSource::Expression => "value".into(),
        }
    }
}

#[derive(Clone)]
pub struct LexicalScope<'arena> {
    pub source: LexicalScopeSource<'arena>,
    pub table: FxHashMap<Symbol, Resolution>,
}

impl<'arena> LexicalScope<'arena> {
    pub fn new(source: LexicalScopeSource) -> LexicalScope {
        LexicalScope {
            source,
            table: Default::default(),
        }
    }

    pub fn define(&mut self, name: Symbol, resolution: Resolution) {
        self.table.insert(name, resolution);
    }
}
#[derive(Clone)]
pub enum LexicalScopeSource<'arena> {
    Plain,
    Function,
    Definition(DefinitionKind),
    Context(DefinitionContext<'arena>),
}

pub enum LexicalScopeBinding<'arena> {
    Declaration(NameHolder<'arena>),
    Resolution(Resolution),
}
