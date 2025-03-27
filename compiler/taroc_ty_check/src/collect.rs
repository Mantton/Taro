use crate::lower;
use rustc_hash::FxHashMap;
use std::rc::Rc;
use taroc_context::{CompilerSession, TypeDatabase};
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DeclarationContext, DeclarationKind, DefinedType, DefinedTypeKind, DefinitionID,
    Generics, NodeID, Package, TypeAlias, TypeParameters, visitor::HirVisitor,
};
use taroc_span::Symbol;
use taroc_ty::{AdtData, AdtKind, GenericArgument, Ty, TyKind};

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

        // First Pass, Create Struct
        let mut data = TypeDatabase::default();
        data.def_to_generics = actor.table;
        session
            .context
            .store
            .types
            .borrow_mut()
            .insert(session.index, data);
        session.context.diagnostics.report()
    }
}

impl HirVisitor for GenericsCollector<'_> {
    fn visit_declaration(&mut self, decl: &Declaration, c: DeclarationContext) -> Self::Result {
        match &decl.kind {
            DeclarationKind::TypeAlias(node) => self.collect(decl.id, &node.generics),
            DeclarationKind::DefinedType(node) => self.collect(decl.id, &node.generics),
            DeclarationKind::Function(node) => self.collect(decl.id, &node.generics),
            DeclarationKind::Constructor(node, _) => self.collect(decl.id, &node.generics),
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, decl, c)
    }
}

impl<'ctx> GenericsCollector<'ctx> {
    fn collect(&mut self, id: NodeID, generics: &Generics) {
        if generics.type_parameters.is_none() {
            let def_id = self.session.context.def_id(id, self.session.index);
            let generics = taroc_ty::Generics { parameters: vec![] };
            self.table.insert(def_id, generics);
            return;
        }

        let mut parameters =
            Vec::with_capacity(generics.type_parameters.as_ref().unwrap().parameters.len());

        for (index, param) in generics
            .type_parameters
            .as_ref()
            .unwrap()
            .parameters
            .iter()
            .enumerate()
        {
            let def = taroc_ty::GenericParameterDefinition {
                name: param.identifier.symbol,
                id: self.session.context.def_id(param.id, self.session.index),
                index,
                kind: match &param.kind {
                    taroc_hir::TypeParameterKind::Type { default } => {
                        taroc_ty::GenericParameterDefinitionKind::Type {
                            has_default: default.is_some(),
                        }
                    }
                    taroc_hir::TypeParameterKind::Constant { default, .. } => {
                        taroc_ty::GenericParameterDefinitionKind::Const {
                            has_default: default.is_some(),
                        }
                    }
                },
            };

            parameters.push(def);
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
        let mut types = session.context.store.types.borrow_mut();
        let db = types.get_mut(&session.index).expect("database");
        db.def_to_ty = actor.ty_table;
        session.context.diagnostics.report()
    }
}

impl HirVisitor for TypeCollector<'_> {
    fn visit_declaration(
        &mut self,
        decl: &Declaration,
        context: DeclarationContext,
    ) -> Self::Result {
        match &decl.kind {
            DeclarationKind::DefinedType(node) => {
                self.collect_defined_type(&decl.id, decl.identifier.symbol, node)
            }
            DeclarationKind::TypeAlias(node) => self.collect_alias(&decl.id, node),
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, decl, context)
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
    fn collect_defined_type(&mut self, id: &NodeID, name: Symbol, node: &DefinedType) {
        let def_id = self.def_id(id);

        if node.kind == DefinedTypeKind::Interface {
            return;
        }

        if self.session.config.is_std
            && let Some(builtin) = self.check_builtin(name)
        {
            self.tag(id, builtin);
        } else {
            let arguments = self.collect_type_parameters(&node.generics.type_parameters);
            let arguments = self.session.context.store.interners.mk_args(arguments);
            let data = AdtData {
                id: def_id,
                name,
                kind: AdtKind::Struct,
            };
            let kind = TyKind::Adt(def_id, arguments);
            let ty = self.session.context.store.interners.intern_ty(kind);
            self.tag(id, ty);
        }
    }

    fn collect_alias(&mut self, id: &NodeID, node: &TypeAlias) {
        let def_id = self.def_id(id);
        let _ = self.collect_type_parameters(&node.generics.type_parameters);
        let kind = TyKind::AliasPlaceholder;
        let ty = self.session.context.store.interners.intern_ty(kind);
        self.tag(id, ty);
    }
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
            "Float" => store.common_types.float32,
            "Double" => store.common_types.float64,
            _ => return None,
        };

        return Some(value);
    }
    fn collect_type_parameters(
        &mut self,
        parameters: &Option<TypeParameters>,
    ) -> Vec<GenericArgument<'ctx>> {
        if parameters.is_none() {
            return vec![];
        }

        let parameters = parameters.as_ref().unwrap();
        let mut arguments = Vec::new();

        for parameter in parameters.parameters.iter() {
            let kind = TyKind::Parameter;
            let ty = self.session.context.store.interners.intern_ty(kind);
            self.tag(&parameter.id, ty);
            let argument = GenericArgument::Type(ty);
            arguments.push(argument);
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
    fn visit_declaration(&mut self, d: &Declaration, c: DeclarationContext) -> Self::Result {
        match &d.kind {
            DeclarationKind::TypeAlias(node) => self.collect(node, d),
            _ => {}
        }
        taroc_hir::visitor::walk_declaration(self, d, c)
    }
}

impl<'ctx> AliasCollector<'ctx> {
    fn collect(&mut self, node: &TypeAlias, declaration: &Declaration) {
        let Some(rhs) = &node.ty else {
            return;
        };

        let rhs = lower::lower_type(
            rhs,
            self.session.context,
            self.session.index,
            Default::default(),
        );

        let context = self.session.context;
        let mut database = context.store.types.borrow_mut();
        let database = database.get_mut(&self.session.index).expect("types db");
        database.def_to_ty.insert(
            self.session
                .context
                .def_id(declaration.id, self.session.index),
            rhs,
        );
    }
}

/// Collects bodies of types
/// Fields, TypeAliases, AssociatedTypes, Variants, Computed Properties
struct DefinitionCollector<'ctx> {
    session: Rc<CompilerSession<'ctx>>,
}
