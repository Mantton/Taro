use crate::ast::{NodeID, Variant, VariantKind};
use crate::sema::resolve::resolver::Resolver;
use crate::{ast, error::CompileResult};

mod define;
mod resolver;
mod tag;

pub fn resolve_package(package: &ast::Package) -> CompileResult<()> {
    let resolver = Resolver::new();
    // First Resolve DefinitionIDs
    tag::tag_package_symbols(package, &resolver)?;
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    Module,
    Struct,
    Enum,
    Function,
    Constant,
    ModuleVariable,
    Interface,
    TypeAlias,
    Namespace,
    Extension,
    Import,
    Export,
    TypeParameter,
    ConstParameter,
    Field,
    Variant,
    AssociatedFunction,
    AssociatedConstant,
    AssociatedInitializer,
    EnumVariant,
    Ctor(CtorOf, CtorKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CtorOf {
    Struct,
    EnumVariant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CtorKind {
    Function,
    Constant,
}

impl CtorKind {
    pub fn from_variant(vdata: &VariantKind) -> CtorKind {
        match *vdata {
            VariantKind::Tuple(..) | VariantKind::Struct(..) => CtorKind::Function,
            VariantKind::Unit => CtorKind::Constant,
        }
    }
}

index_vec::define_index_type! {
    pub struct DefinitionIndex = u32;
}

index_vec::define_index_type! {
    pub struct PackageIndex = u32;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefinitionID {
    package_index: PackageIndex,
    definition_index: DefinitionIndex,
}

impl DefinitionID {
    pub fn new(package: PackageIndex, index: DefinitionIndex) -> DefinitionID {
        DefinitionID {
            package_index: package,
            definition_index: index,
        }
    }

    pub fn is_local(&self, index: usize) -> bool {
        self.package_index == PackageIndex::from_usize(index)
    }

    pub fn package(&self) -> PackageIndex {
        self.package_index
    }
}
