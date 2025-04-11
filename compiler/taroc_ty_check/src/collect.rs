use crate::{lower, utils};
use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DeclarationContext, DeclarationKind, DefinedType, DefinedTypeKind, DefinitionID,
    Generics, Mutability, NodeID, Package, TypeAlias, visitor::HirVisitor,
};
use taroc_span::Symbol;
use taroc_ty::{
    AssociatedTypeDefinition, ComputedPropertySignature, EnumDefinition, EnumVariant,
    EnumVariantKind, GenericArgument, GenericParameter, InterfaceDefinition,
    InterfaceMethodRequirement, InterfaceOperatorRequirement, InterfaceReference,
    InterfaceRequirement, StructDefinition, StructField, Ty, TyKind,
};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    GenericsCollector::run(package, context)?;
    TypeCollector::run(package, context)?;
    DefinitionCollector::run(package, context)?;
    FunctionCollector::run(package, context)?;
    context.diagnostics.report()
}

/// Collect & Cache Generics Information for a Definition
struct GenericsCollector<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> GenericsCollector<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> GenericsCollector<'ctx> {
        GenericsCollector { context }
    }

    fn run<'a>(package: &Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = GenericsCollector::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
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
            let def_id = self.context.def_id(id);
            let generics = taroc_ty::Generics { parameters: vec![] };
            self.context.cache_generics(def_id, generics);
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
            let id = self.context.def_id(param.id);
            let name = param.identifier.symbol;

            // Definition
            let def = taroc_ty::GenericParameterDefinition {
                name,
                id,
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

            // Type
            let kind = TyKind::Parameter(GenericParameter { index, name });
            let ty = self.context.store.interners.intern_ty(kind);
            self.context.cache_type(id, ty);
        }
        let def_id = self.context.def_id(id);
        let generics = taroc_ty::Generics { parameters };
        self.context.cache_generics(def_id, generics);
    }
}

/// Collect Top Level Defintitions and Generate Corresponding `types::Ty`
struct TypeCollector<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> TypeCollector<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> TypeCollector<'ctx> {
        TypeCollector { context }
    }

    fn run<'a>(package: &Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = TypeCollector::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
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
                self.collect_defined_type(decl.id, decl.identifier.symbol, node)
            }
            DeclarationKind::TypeAlias(node) => self.collect_alias(decl.id, node),
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, decl, context)
    }
}

impl<'ctx> TypeCollector<'ctx> {
    fn collect_defined_type(&mut self, id: NodeID, name: Symbol, node: &DefinedType) {
        let def_id = self.context.def_id(id);
        if self.context.session().config.is_std
            && let Some(builtin) = self.check_builtin(name)
        {
            self.context.cache_type(def_id, builtin);
        } else if self.context.session().config.is_std && self.check_generic_builtin(name, def_id) {
            return;
        } else {
            let arguments = self.context.type_arguments(def_id);
            match node.kind {
                DefinedTypeKind::Struct | DefinedTypeKind::Enum => {
                    let kind = TyKind::Adt(def_id, arguments);
                    let ty = self.context.store.interners.intern_ty(kind);
                    self.context.cache_type(def_id, ty);
                }
                DefinedTypeKind::Interface => {}
            }
        }
    }

    fn collect_alias(&mut self, id: NodeID, node: &TypeAlias) {
        let def_id = self.context.def_id(id);
        let Some(rhs) = &node.ty else {
            return;
        };
        let rhs = lower::lower_type(rhs, self.context, Default::default());
        self.context.cache_type(def_id, rhs);
    }
}
impl<'ctx> TypeCollector<'ctx> {
    fn check_builtin(&self, symbol: Symbol) -> Option<Ty<'ctx>> {
        let store = &self.context.store;
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

    fn check_generic_builtin(&self, symbol: Symbol, id: DefinitionID) -> bool {
        let store = &self.context.store;
        match symbol.as_str() {
            "Array" => {
                store.common_types.array.set(Some(id));
                return true;
            }
            "ImmutablePointer" => {
                store.common_types.const_ptr.set(Some(id));
                return true;
            }
            "MutablePointer" => {
                store.common_types.ptr.set(Some(id));
                return true;
            }
            "ImmutableReference" => {
                store.common_types.const_ref.set(Some(id));
                return true;
            }
            "MutableReference" => {
                store.common_types.mut_ref.set(Some(id));
                return true;
            }
            _ => return false,
        };
    }
}

/// Collect bodies of types:
///
/// Fields, TypeAliases, AssociatedTypes, Variants, Computed Properties
struct DefinitionCollector<'ctx> {
    context: GlobalContext<'ctx>,
    parent: Option<DefinitionID>,
}

impl<'ctx> DefinitionCollector<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> DefinitionCollector<'ctx> {
        DefinitionCollector {
            context,
            parent: None,
        }
    }

    fn run<'a>(package: &Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = DefinitionCollector::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
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
                let id = self.context.def_id(declaration.id);
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

                        self.context.cache_struct_def(id, def);
                    }
                    DefinedTypeKind::Enum => {
                        let def = EnumDefinition {
                            id,
                            name,
                            conformances,
                            variants: Default::default(),
                        };

                        self.context.cache_enum_def(id, def);
                    }
                    DefinedTypeKind::Interface => {
                        let def = InterfaceDefinition {
                            id,
                            name,
                            conformances,
                            associated_types: Default::default(),
                            requirements: vec![],
                        };

                        self.context.cache_interface_def(id, def);
                    }
                };

                self.parent = Some(id);
            }
            DeclarationKind::Variable(node) if matches!(context, DeclarationContext::Struct) => {
                let name = declaration.identifier.symbol;

                // Struct Field
                let ty = lower::lower_type(
                    node.ty.as_ref().expect("annotated field"),
                    self.context,
                    Default::default(),
                );
                let field = StructField {
                    name,
                    ty,
                    mutability: node.mutability,
                };
                self.context.update_struct_def(self.parent(), move |def| {
                    let previous = def.fields.insert(declaration.identifier.symbol, field);
                    debug_assert!(
                        previous.is_none(),
                        "overlapping field defintions should be caught by resolver"
                    );
                });
            }

            DeclarationKind::Constant(ty, _) => {
                let _ty = lower::lower_type(ty, self.context, Default::default());
            }
            DeclarationKind::AssociatedType(generics, default_ty)
                if matches!(context, DeclarationContext::Interface) =>
            {
                let name = declaration.identifier.symbol;
                let conformances = self.collect_interface_conformances(&generics.inheritance);

                let assoc = AssociatedTypeDefinition {
                    name,
                    conformances,
                    default_type: default_ty
                        .as_ref()
                        .map(|ty| lower::lower_type(&ty, self.context, Default::default())),
                };

                self.context.update_interface_def(self.parent(), |def| {
                    let previous = def.associated_types.insert(name, assoc);

                    debug_assert!(
                        previous.is_none(),
                        "overlapping associated types should be caught by resolver"
                    );
                });
            }
            DeclarationKind::TypeAlias(_) => {
                // TODO!
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, declaration, context);
        self.parent = previous
    }

    fn visit_variant(&mut self, variant: &taroc_hir::Variant) -> Self::Result {
        let id = self.context.def_id(variant.id);
        let name = variant.identifier.symbol;
        let kind = match &variant.kind {
            taroc_hir::VariantKind::Unit => EnumVariantKind::Unit,
            taroc_hir::VariantKind::Tuple(fields) => {
                let types: Vec<Ty<'ctx>> = fields
                    .iter()
                    .map(|f| {
                        let ty = lower::lower_type(&f.ty, self.context, Default::default());
                        ty
                    })
                    .collect();

                EnumVariantKind::Tuple(types)
            }
            taroc_hir::VariantKind::Struct(fields) => {
                let fields: FxHashMap<Symbol, StructField<'ctx>> =
                    fields.iter().fold(Default::default(), |mut acc, field| {
                        let ty = lower::lower_type(&field.ty, self.context, Default::default());

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

        self.context.update_enum_def(self.parent(), |def| {
            let previous = def.variants.insert(node.name, node);

            debug_assert!(
                previous.is_none(),
                "variant names must be unique, this should be caught by the resolver"
            );
        });
    }
}

impl<'ctx> DefinitionCollector<'ctx> {
    pub fn parent(&self) -> DefinitionID {
        self.parent.expect("parent_id")
    }
    pub fn collect_interface_conformances(
        &mut self,
        node: &Option<taroc_hir::Inheritance>,
    ) -> Vec<InterfaceReference<'ctx>> {
        let mut out = vec![];

        let Some(node) = node else {
            return out;
        };

        for node in node.interfaces.iter() {
            let resolution = self.context.resolution(node.id);

            match resolution {
                taroc_hir::Resolution::Definition(id, taroc_hir::DefinitionKind::Interface) => {
                    let arguments = node
                        .path
                        .segments
                        .last()
                        .map(|f| f.arguments.as_ref())
                        .flatten();

                    let generics = self.context.generics_of(id);
                    lower::check_generic_arg_count(
                        &generics,
                        node.path.segments.last().unwrap(),
                        self.context,
                    );
                    let arguments: Vec<GenericArgument<'ctx>> = if let Some(arguments) = arguments {
                        let arguments = arguments.arguments.iter().map(|argument| match argument {
                            taroc_hir::TypeArgument::Type(ty) => {
                                let ty = lower::lower_type(ty, self.context, Default::default());

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
                        arguments: self.context.store.interners.mk_args(arguments),
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
    context: GlobalContext<'ctx>,
    parent: Option<DefinitionID>,
}

struct FunctionCollector<'ctx> {
    context: GlobalContext<'ctx>,
    parent: Option<DefinitionID>,
}

impl<'ctx> FunctionCollector<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> FunctionCollector<'ctx> {
        FunctionCollector {
            context,
            parent: None,
        }
    }

    fn run<'a>(package: &Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = FunctionCollector::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl<'ctx> HirVisitor for FunctionCollector<'ctx> {
    fn visit_declaration(
        &mut self,
        decl: &Declaration,
        context: DeclarationContext,
    ) -> Self::Result {
        let def_id = self.context.def_id(decl.id);
        let previous = self.parent;

        match &decl.kind {
            DeclarationKind::DefinedType(_) => {
                self.parent = Some(def_id);
            }
            DeclarationKind::Extend(_) => {
                self.parent = Some(self.context.extension_target(def_id));
            }
            DeclarationKind::Function(func) => {
                let signature = utils::convert_to_labeled_signature(func, self.context);
                match context {
                    DeclarationContext::Module => {
                        // Top Level Function
                        self.context.with_type_database(None, |database| {
                            database.functions.insert(def_id, signature);
                        });
                    }
                    DeclarationContext::Interface => {
                        // Interface Requirements
                        let parent = self.parent.expect("parent must be defined");
                        let is_required = func.block.is_none();
                        let requirement = InterfaceMethodRequirement {
                            name: decl.identifier.symbol,
                            is_required,
                            signature,
                        };
                        let kind = InterfaceRequirement::Method(requirement);
                        self.context.update_interface_def(parent, |def| {
                            def.requirements.push(kind);
                        });
                    }
                    DeclarationContext::Extern => {
                        // External function
                        todo!()
                    }
                    _ => {
                        // Method
                        let parent = self.parent.expect("parent must be defined");
                        self.context.with_type_database(None, |database| {
                            let store = database
                                .def_to_functions
                                .entry(parent)
                                .or_insert(Default::default());
                            // TODO: Static
                            store
                                .methods
                                .entry(decl.identifier.symbol)
                                .or_default()
                                .push(signature);
                        });
                    }
                }
            }
            DeclarationKind::Operator(kind, func) => {
                debug_assert!(
                    self.parent.is_some(),
                    "operators must only appear in type bodies"
                );
                let signature = utils::convert_to_labeled_signature(func, self.context);
                let parent = self.parent.expect("parent must be defined");

                match context {
                    DeclarationContext::Interface => {
                        // Operator Requirement
                        let requirement = InterfaceOperatorRequirement {
                            kind: *kind,
                            signature,
                        };
                        let kind = InterfaceRequirement::Operator(requirement);
                        self.context.update_interface_def(parent, |def| {
                            def.requirements.push(kind);
                        });
                    }
                    _ => {
                        // Operator Implementation
                        self.context.with_type_database(None, |database| {
                            let store = database
                                .def_to_functions
                                .entry(parent)
                                .or_insert(Default::default());

                            store.operators.entry(*kind).or_default().push(signature);
                        });
                    }
                }
            }
            DeclarationKind::Computed(node) => {
                debug_assert!(
                    self.parent.is_some(),
                    "computed properties must only appear in type bodies"
                );
                let parent = self.parent.expect("parent must be defined");
                let ty = lower::lower_type(&node.ty, self.context, Default::default());

                match context {
                    DeclarationContext::Interface => {
                        todo!()
                    }
                    _ => {
                        self.context.with_type_database(None, |database| {
                            let store = database
                                .def_to_functions
                                .entry(parent)
                                .or_insert(Default::default());

                            let signature = ComputedPropertySignature { ty };
                            store.properties.insert(decl.identifier.symbol, signature)
                        });
                    }
                }
            }
            DeclarationKind::Constructor(func, _) => {
                debug_assert!(
                    self.parent.is_some(),
                    "constructors must only appear in type bodies"
                );
                let signature = utils::convert_to_labeled_signature(func, self.context);
                let parent = self.parent.expect("parent must be defined");

                self.context.with_type_database(None, |database| {
                    let store = database
                        .def_to_functions
                        .entry(parent)
                        .or_insert(Default::default());

                    store.constructors.push(signature)
                });
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, decl, context);
        self.parent = previous;
    }
}
