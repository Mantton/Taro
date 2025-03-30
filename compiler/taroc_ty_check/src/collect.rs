use crate::{lower, utils};
use rustc_hash::FxHashMap;
use std::rc::Rc;
use taroc_context::{CompilerSession, TypeDatabase};
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DeclarationContext, DeclarationKind, DefinedType, DefinedTypeKind, DefinitionID,
    Generics, Mutability, NodeID, Package, TypeAlias, TypeParameters, visitor::HirVisitor,
};
use taroc_span::Symbol;
use taroc_ty::{
    AssociatedTypeDefinition, EnumDefinition, EnumVariant, EnumVariantKind, GenericArgument,
    GenericParameter, InterfaceDefinition, InterfaceMethodRequirement, InterfaceReference,
    InterfaceRequirement, StructDefinition, StructField, Ty, TyKind,
};

pub fn run(package: &taroc_hir::Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    GenericsCollector::run(package, session.clone())?;
    TypeCollector::run(package, session.clone())?;
    AliasCollector::run(package, session.clone())?;
    DefinitionCollector::run(package, session.clone())?;
    InterfaceRequirementsCollector::run(package, session.clone())?;
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
                            default: default.clone(),
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

        if self.session.config.is_std
            && let Some(builtin) = self.check_builtin(name)
        {
            self.tag(id, builtin);
        } else {
            let arguments = self.collect_type_parameters(&node.generics.type_parameters);
            let arguments = self.session.context.store.interners.mk_args(arguments);

            match node.kind {
                DefinedTypeKind::Struct | DefinedTypeKind::Enum => {
                    let kind = TyKind::Adt(def_id, arguments);
                    let ty = self.session.context.store.interners.intern_ty(kind);
                    self.tag(id, ty);
                }
                DefinedTypeKind::Interface => {}
            }
        }
    }

    fn collect_alias(&mut self, id: &NodeID, node: &TypeAlias) {
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

        for (index, parameter) in parameters.parameters.iter().enumerate() {
            let kind = TyKind::Parameter(GenericParameter {
                index,
                name: parameter.identifier.symbol,
            });
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
    parent: Option<DefinitionID>,
    structs: FxHashMap<DefinitionID, StructDefinition<'ctx>>,
    enums: FxHashMap<DefinitionID, EnumDefinition<'ctx>>,
    interfaces: FxHashMap<DefinitionID, InterfaceDefinition<'ctx>>,
}

impl<'ctx> DefinitionCollector<'ctx> {
    fn new(session: Rc<CompilerSession<'ctx>>) -> DefinitionCollector<'ctx> {
        DefinitionCollector {
            session,
            parent: None,
            structs: Default::default(),
            enums: Default::default(),
            interfaces: Default::default(),
        }
    }

    fn run<'a>(package: &Package, session: Rc<CompilerSession<'ctx>>) -> CompileResult<()> {
        let mut actor = DefinitionCollector::new(session.clone());
        taroc_hir::visitor::walk_package(&mut actor, package);
        session.context.diagnostics.report()
    }
}
impl<'ctx> HirVisitor for DefinitionCollector<'ctx> {
    fn visit_declaration(
        &mut self,
        declaration: &Declaration,
        context: DeclarationContext,
    ) -> Self::Result {
        let previous = self.parent;
        match &declaration.kind {
            DeclarationKind::DefinedType(node) => {
                let id = self
                    .session
                    .context
                    .def_id(declaration.id, self.session.index);
                let name = declaration.identifier.symbol;
                let conformances = self.collect_interface_conformances(&node.generics.inheritance);
                match &node.kind {
                    DefinedTypeKind::Struct => {
                        // create struct definition
                        let def = StructDefinition {
                            id,
                            name,
                            conformances,
                            fields: Default::default(),
                        };

                        self.structs.insert(id, def);
                    }
                    DefinedTypeKind::Enum => {
                        let def = EnumDefinition {
                            id,
                            name,
                            conformances,
                            variants: Default::default(),
                        };

                        self.enums.insert(id, def);
                    }
                    DefinedTypeKind::Interface => {
                        let def = InterfaceDefinition {
                            id,
                            name,
                            conformances,
                            associated_types: Default::default(),
                            requirements: vec![],
                        };

                        self.interfaces.insert(id, def);
                    }
                };

                self.parent = Some(id);
            }
            DeclarationKind::Computed(node) => {
                let _name = declaration.identifier.symbol;
                let ty = &node.ty;
                let _ty = lower::lower_type(
                    ty,
                    self.session.context,
                    self.session.index,
                    Default::default(),
                );
            }
            DeclarationKind::Variable(node) if matches!(context, DeclarationContext::Struct) => {
                let name = declaration.identifier.symbol;

                // Struct Field
                let ty = lower::lower_type(
                    node.ty.as_ref().expect("annotated field"),
                    self.session.context,
                    self.session.index,
                    Default::default(),
                );

                let field = StructField {
                    name,
                    ty,
                    mutability: node.mutability,
                };

                let parent = self.parent.expect("parent_id");
                let def = self.structs.get_mut(&parent).expect("struct definition");
                let previous = def.fields.insert(declaration.identifier.symbol, field);

                debug_assert!(
                    previous.is_none(),
                    "overlapping field defintions should be caught by resolver"
                );
            }

            DeclarationKind::Constant(ty, _) => {
                let _ty = lower::lower_type(
                    ty,
                    self.session.context,
                    self.session.index,
                    Default::default(),
                );
            }

            DeclarationKind::AssociatedType(generics, default_ty)
                if matches!(context, DeclarationContext::Interface) =>
            {
                let name = declaration.identifier.symbol;
                let conformances = self.collect_interface_conformances(&generics.inheritance);

                let assoc = AssociatedTypeDefinition {
                    name,
                    conformances,
                    default_type: default_ty.as_ref().map(|ty| {
                        lower::lower_type(
                            &ty,
                            self.session.context,
                            self.session.index,
                            Default::default(),
                        )
                    }),
                };

                let parent = self.parent.expect("parent_id");
                let def = self.interfaces.get_mut(&parent).expect("struct definition");
                let previous = def.associated_types.insert(name, assoc);

                debug_assert!(
                    previous.is_none(),
                    "overlapping associated types should be caught by resolver"
                );
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, declaration, context);
        self.parent = previous
    }

    fn visit_variant(&mut self, variant: &taroc_hir::Variant) -> Self::Result {
        let id = self.session.context.def_id(variant.id, self.session.index);
        let name = variant.identifier.symbol;
        let kind = match &variant.kind {
            taroc_hir::VariantKind::Unit => EnumVariantKind::Unit,
            taroc_hir::VariantKind::Tuple(fields) => {
                let types: Vec<Ty<'ctx>> = fields
                    .iter()
                    .map(|f| {
                        let ty = lower::lower_type(
                            &f.ty,
                            self.session.context,
                            self.session.index,
                            Default::default(),
                        );
                        ty
                    })
                    .collect();

                EnumVariantKind::Tuple(types)
            }
            taroc_hir::VariantKind::Struct(fields) => {
                let fields: FxHashMap<Symbol, StructField<'ctx>> =
                    fields.iter().fold(Default::default(), |mut acc, field| {
                        let ty = lower::lower_type(
                            &field.ty,
                            self.session.context,
                            self.session.index,
                            Default::default(),
                        );

                        let field = StructField {
                            name,
                            ty,
                            mutability: Mutability::Immutable,
                        };

                        let previous = acc.insert(field.name, field);

                        debug_assert!(
                            previous.is_none(),
                            "fields must be unique, this should be caught by the resolver"
                        );

                        acc
                    });

                let def = StructDefinition {
                    id,
                    name,
                    fields,
                    conformances: vec![],
                };

                EnumVariantKind::Struct(def)
            }
        };
        // Enum Variant

        let node = EnumVariant {
            id,
            name,
            kind,
            discriminant: 0, // TODO
        };

        let parent = self.parent.expect("parent_id");
        let def = self.enums.get_mut(&parent).expect("enum definition");
        let previous = def.variants.insert(node.name, node);

        debug_assert!(
            previous.is_none(),
            "variant names must be unique, this should be caught by the resolver"
        );
    }
}

impl<'ctx> DefinitionCollector<'ctx> {
    pub fn collect_interface_conformances(
        &mut self,
        node: &Option<taroc_hir::Inheritance>,
    ) -> Vec<InterfaceReference<'ctx>> {
        let mut out = vec![];

        let Some(node) = node else {
            return out;
        };

        for node in node.interfaces.iter() {
            let resolution = self.session.context.resolution(node.id, self.session.index);

            match resolution {
                taroc_hir::Resolution::Definition(id, taroc_hir::DefinitionKind::Interface) => {
                    let arguments = node
                        .path
                        .segments
                        .last()
                        .map(|f| f.arguments.as_ref())
                        .flatten();

                    let generics = self.session.context.generics_of(id);
                    lower::check_generic_arg_count(
                        &generics,
                        node.path.segments.last().unwrap(),
                        self.session.context,
                    );
                    let arguments: Vec<GenericArgument<'ctx>> = if let Some(arguments) = arguments {
                        let arguments = arguments.arguments.iter().map(|argument| match argument {
                            taroc_hir::TypeArgument::Type(ty) => {
                                let ty = lower::lower_type(
                                    ty,
                                    self.session.context,
                                    self.session.index,
                                    Default::default(),
                                );

                                GenericArgument::Type(ty)
                            }
                            taroc_hir::TypeArgument::Const(..) => todo!(),
                        });
                        arguments.collect()
                    } else {
                        vec![]
                    };

                    let reference = InterfaceReference {
                        id,
                        arguments: self.session.context.store.interners.mk_args(arguments),
                    };

                    out.push(reference);
                }
                _ => unreachable!("resolver must validate provided paths are interfaces"),
            }
        }

        out
    }
}

/// Collect InterfaceRequirements
struct InterfaceRequirementsCollector<'ctx> {
    session: Rc<CompilerSession<'ctx>>,
    parent: Option<DefinitionID>,
}

impl<'ctx> InterfaceRequirementsCollector<'ctx> {
    fn new(session: Rc<CompilerSession<'ctx>>) -> InterfaceRequirementsCollector<'ctx> {
        InterfaceRequirementsCollector {
            session,
            parent: None,
        }
    }

    fn run<'a>(package: &Package, session: Rc<CompilerSession<'ctx>>) -> CompileResult<()> {
        let mut actor = InterfaceRequirementsCollector::new(session.clone());
        taroc_hir::visitor::walk_package(&mut actor, package);
        session.context.diagnostics.report()
    }
}

impl<'ctx> HirVisitor for InterfaceRequirementsCollector<'ctx> {
    fn visit_declaration(
        &mut self,
        declaration: &Declaration,
        context: DeclarationContext,
    ) -> Self::Result {
        let previous = self.parent;

        match &declaration.kind {
            DeclarationKind::DefinedType(node)
                if matches!(node.kind, DefinedTypeKind::Interface) =>
            {
                let id = self
                    .session
                    .context
                    .def_id(declaration.id, self.session.index);

                self.parent = Some(id)
            }
            DeclarationKind::Function(func) if matches!(context, DeclarationContext::Interface) => {
                self.session
                    .context
                    .diagnostics
                    .info("Target".into(), declaration.identifier.span);

                let is_required = func.block.is_none();

                let requirement = InterfaceMethodRequirement {
                    name: declaration.identifier.symbol,
                    is_required,
                    signature: utils::convert_to_labeled_signature(func, self.session.clone()),
                };

                let kind = InterfaceRequirement::Method(requirement);

                todo!("update interface")
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, declaration, context);
        self.parent = previous
    }
}

// TODO: Recursive Checker
// TODO: Extension Blocks
