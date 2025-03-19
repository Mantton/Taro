use rustc_hash::FxHashMap;
use std::rc::Rc;
use taroc_context::CompilerSession;
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DeclarationContext, DeclarationKind, DefinitionID, Enum, Generics, Interface,
    NodeID, Package, Struct, TypeAlias, TypeParameterKind, TypeParameters, visitor::HirVisitor,
};
use taroc_span::Symbol;
use taroc_ty::{AdtData, AdtKind, GenericArgument, Ty, TyKind};

use crate::lower;

pub fn run(package: &taroc_hir::Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    GenericsCollector::run(package, session.clone())?;
    TypeCollector::run(package, session.clone())?;
    AliasCollector::run(package, session.clone())?;
    session.context.diagnostics.report()
}

/// This pass Collects generic information for top level declarations
struct GenericsCollector<'ctx> {
    session: Rc<CompilerSession<'ctx>>,
    table: FxHashMap<DefinitionID, taroc_ty::Generics>,
}

impl<'ctx> GenericsCollector<'ctx> {
    fn new(session: Rc<CompilerSession<'ctx>>) -> GenericsCollector<'ctx> {
        GenericsCollector {
            session,
            table: Default::default(),
        }
    }

    fn run<'a>(package: &Package, session: Rc<CompilerSession<'ctx>>) -> CompileResult<()> {
        let mut actor = GenericsCollector::new(session.clone());
        taroc_hir::visitor::walk_package(&mut actor, package);
        session.context.store.types.borrow_mut().def_to_generics = actor.table;
        session.context.diagnostics.report()
    }
}

impl HirVisitor for GenericsCollector<'_> {
    fn visit_declaration(&mut self, decl: &Declaration, _c: DeclarationContext) -> Self::Result {
        match &decl.kind {
            DeclarationKind::Struct(node) => self.collect(decl.id, &node.generics),
            DeclarationKind::Enum(node) => self.collect(decl.id, &node.generics),
            DeclarationKind::TypeAlias(node) => self.collect(decl.id, &node.generics),
            DeclarationKind::Interface(node) => self.collect(decl.id, &node.generics),
            _ => {}
        }
    }
}

impl<'ctx> GenericsCollector<'ctx> {
    fn collect(&mut self, id: NodeID, generics: &Generics) {
        let mut parameters = Vec::with_capacity(generics.parameters.parameters.len());
        for (index, param) in generics.parameters.parameters.iter().enumerate() {
            match &param.kind {
                TypeParameterKind::Type { default } => {
                    let def = taroc_ty::GenericParameterDefinition {
                        name: param.identifier.symbol,
                        id: self.session.context.def_id(param.id, self.session.index),
                        index,
                        kind: taroc_ty::GenericParameterDefinitionKind::Type {
                            has_default: default.is_some(),
                        },
                    };

                    parameters.push(def);
                }
                TypeParameterKind::Constant { default, .. } => {
                    let def = taroc_ty::GenericParameterDefinition {
                        name: param.identifier.symbol,
                        id: self.session.context.def_id(param.id, self.session.index),
                        index,
                        kind: taroc_ty::GenericParameterDefinitionKind::Const {
                            has_default: default.is_some(),
                        },
                    };

                    parameters.push(def);
                }
            }
        }
        let def_id = self.session.context.def_id(id, self.session.index);
        let generics = taroc_ty::Generics { parameters };
        self.table.insert(def_id, generics);
    }
}

/// This Pass, Collects top level symbols  & converts them to `types::Ty`
///
/// Once Converted they are mapped as `hir::DefinitionID` -> `types::Ty`
struct TypeCollector<'ctx> {
    session: Rc<CompilerSession<'ctx>>,
    ty_table: FxHashMap<DefinitionID, Ty<'ctx>>,
}

impl<'ctx> TypeCollector<'ctx> {
    fn new(session: Rc<CompilerSession<'ctx>>) -> TypeCollector<'ctx> {
        TypeCollector {
            session,
            ty_table: Default::default(),
        }
    }

    fn run<'a>(package: &Package, session: Rc<CompilerSession<'ctx>>) -> CompileResult<()> {
        let mut actor = TypeCollector::new(session.clone());
        taroc_hir::visitor::walk_package(&mut actor, package);
        session.context.store.types.borrow_mut().def_to_ty = actor.ty_table;
        session.context.diagnostics.report()
    }
}

impl HirVisitor for TypeCollector<'_> {
    fn visit_declaration(&mut self, decl: &Declaration, _c: DeclarationContext) -> Self::Result {
        match &decl.kind {
            DeclarationKind::Struct(node) => {
                self.collect_struct(&decl.id, decl.identifier.symbol, node)
            }
            DeclarationKind::Enum(node) => {
                self.collect_enum(&decl.id, decl.identifier.symbol, node)
            }
            DeclarationKind::TypeAlias(node) => self.collect_alias(&decl.id, node),
            DeclarationKind::Interface(node) => self.collect_interface(&decl.id, node),
            _ => {}
        }
    }
}

impl<'ctx> TypeCollector<'ctx> {
    fn def_id(&self, node: &NodeID) -> DefinitionID {
        let resolutions = self.session.context.store.resolutions.borrow();
        let resolutions = resolutions
            .get(&self.session.index)
            .expect("resolution data");

        *resolutions.node_to_def.get(node).expect("nodeid")
    }

    fn tag(&mut self, node: &NodeID, ty: Ty<'ctx>) {
        let id = self.def_id(node);
        self.ty_table.insert(id, ty);
    }
}

impl<'ctx> TypeCollector<'ctx> {
    fn collect_struct(&mut self, id: &NodeID, name: Symbol, node: &Struct) {
        let def_id = self.def_id(id);
        if self.session.config.is_std
            && let Some(builtin) = self.check_builtin(name)
        {
            self.tag(id, builtin);
        } else {
            let arguments = self.collect_type_parameters(&node.generics.parameters);
            let arguments = self.session.context.store.interners.mk_args(arguments);
            let data = AdtData {
                id: def_id,
                name,
                kind: AdtKind::Struct,
            };
            let kind = TyKind::Adt(data, arguments);
            let ty = self.session.context.store.interners.intern_ty(kind);
            self.tag(id, ty);
        }
    }

    fn collect_enum(&mut self, id: &NodeID, name: Symbol, node: &Enum) {
        let def_id = self.def_id(id);

        let arguments = self.collect_type_parameters(&node.generics.parameters);
        let arguments = self.session.context.store.interners.mk_args(arguments);
        let data = AdtData {
            id: def_id,
            name,
            kind: AdtKind::Enum,
        };
        let kind = TyKind::Adt(data, arguments);
        let ty = self.session.context.store.interners.intern_ty(kind);
        self.tag(id, ty);
    }

    fn collect_alias(&mut self, id: &NodeID, node: &TypeAlias) {
        let def_id = self.def_id(id);
        let _ = self.collect_type_parameters(&node.generics.parameters);
        let kind = TyKind::AliasPlaceholder;
        let ty = self.session.context.store.interners.intern_ty(kind);
        self.tag(id, ty);
    }

    fn collect_interface(&mut self, id: &NodeID, node: &Interface) {}
}
impl<'ctx> TypeCollector<'ctx> {
    fn check_builtin(&self, symbol: Symbol) -> Option<Ty<'ctx>> {
        let store = &self.session.context.store;
        let value = match symbol.as_str() {
            "Bool" => store.common_types.bool,
            "Rune" => store.common_types.rune,
            "Void" => store.common_types.void,
            "UInt" => store.common_types.uint,
            "UInt8" => store.common_types.uint8,
            "UInt16" => store.common_types.uint16,
            "UInt32" => store.common_types.uint32,
            "UInt64" => store.common_types.uint64,
            "Int" => store.common_types.int,
            "Int8" => store.common_types.int8,
            "Int16" => store.common_types.int16,
            "Int32" => store.common_types.int32,
            "Int64" => store.common_types.int64,
            "Float32" => store.common_types.float32,
            "Float64" => store.common_types.float64,
            _ => return None,
        };

        return Some(value);
    }
    fn collect_type_parameters(
        &mut self,
        parameters: &TypeParameters,
    ) -> Vec<GenericArgument<'ctx>> {
        let mut arguments = Vec::new();

        for parameter in parameters.parameters.iter() {
            match parameter.kind {
                TypeParameterKind::Type { .. } => {
                    let kind = TyKind::Parameter;
                    let ty = self.session.context.store.interners.intern_ty(kind);
                    self.tag(&parameter.id, ty);
                    let argument = GenericArgument::Type(ty);
                    arguments.push(argument);
                }
                TypeParameterKind::Constant { .. } => {
                    continue;
                }
            }
        }

        arguments
    }
}

/// Populate Body of Each Type
struct AliasCollector<'ctx> {
    session: Rc<CompilerSession<'ctx>>,
}

impl<'ctx> AliasCollector<'ctx> {
    fn new(session: Rc<CompilerSession<'ctx>>) -> AliasCollector<'ctx> {
        AliasCollector { session }
    }

    fn run<'a>(package: &Package, session: Rc<CompilerSession<'ctx>>) -> CompileResult<()> {
        let mut actor = AliasCollector::new(session.clone());
        taroc_hir::visitor::walk_package(&mut actor, package);
        session.context.diagnostics.report()
    }
}

impl HirVisitor for AliasCollector<'_> {
    fn visit_declaration(&mut self, d: &Declaration, _c: DeclarationContext) -> Self::Result {
        match &d.kind {
            DeclarationKind::TypeAlias(node) => self.collect(node, d),
            _ => {}
        }
    }
}

impl<'ctx> AliasCollector<'ctx> {
    fn collect(&mut self, node: &TypeAlias, declaration: &Declaration) {
        let Some(rhs) = &node.ty else {
            return;
        };

        let rhs = lower::lower_type(rhs, self.session.context, self.session.index);
        todo!("update types table");
        todo!()
    }
}
