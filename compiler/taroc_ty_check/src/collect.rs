use crate::{lower, models::InferenceContext, utils};
use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{
    AttributeList, Declaration, DeclarationContext, DeclarationKind, DefinedType, DefinedTypeKind,
    DefinitionID, Generics, Mutability, NodeID, Package, TypeAlias, attributes_contain,
    visitor::HirVisitor,
};
use taroc_span::{Identifier, Symbol};
use taroc_ty::{
    AdtDef, AdtKind, AssociatedTypeDefinition, ComputedPropertySignature, Constraint,
    DefinitionConstraints, EnumDefinition, EnumVariant, EnumVariantKind, GenericArguments,
    GenericParameter, InterfaceDefinition, InterfaceMethodRequirement,
    InterfaceOperatorRequirement, StructDefinition, StructField, Ty, TyKind,
};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    GenericsCollector::run(package, context)?;
    TypeCollector::run(package, context)?;
    ConstraintsCollector::run(package, context)?;
    DefinitionCollector::run(package, context)?;
    ConformanceCollector::run(package, context)?;
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
        let def_id = self.context.def_id(id);

        // Interfaces have implicit self type parameter
        let interface_self_type = if matches!(
            self.context.def_kind(def_id),
            taroc_hir::DefinitionKind::Interface
        ) {
            let def = taroc_ty::GenericParameterDefinition {
                index: 0,
                name: Symbol::with("Self"),
                id: def_id,
                kind: taroc_ty::GenericParameterDefinitionKind::Type { default: None },
            };
            Some(def)
        } else {
            None
        };
        let has_self = interface_self_type.is_some();
        let parameters_len = &generics
            .type_parameters
            .as_ref()
            .map(|f| f.parameters.len())
            .unwrap_or_default();
        let mut parameters = Vec::with_capacity(parameters_len + (has_self as usize));

        let start = has_self as usize;
        if let Some(s) = interface_self_type {
            parameters.push(s);
        };
        // Parameters
        let hir_parameters = generics.type_parameters.as_ref().map(|f| &f.parameters);
        if let Some(hir_parameters) = hir_parameters {
            for (index, param) in hir_parameters.iter().enumerate() {
                let id = self.context.def_id(param.id);
                let name = param.identifier.symbol;
                let index = start + index;
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
                let kind = TyKind::Parameter(GenericParameter {
                    // parent: def_id,
                    // id,
                    index,
                    name,
                });
                let ty = self.context.store.interners.intern_ty(kind);
                self.context.cache_type(id, ty);
            }
        }
        let def_id = self.context.def_id(id);
        let generics = taroc_ty::Generics {
            parameters,
            has_self,
        };
        self.context.cache_generics(def_id, generics);
    }
}

/// Collect & Cache Generics Information for a Definition
struct ConstraintsCollector<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> ConstraintsCollector<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> ConstraintsCollector<'ctx> {
        ConstraintsCollector { context }
    }

    fn run<'a>(package: &Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = ConstraintsCollector::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for ConstraintsCollector<'_> {
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

impl<'ctx> ConstraintsCollector<'ctx> {
    fn collect(&mut self, id: NodeID, generics: &taroc_hir::Generics) {
        let def_id = self.context.def_id(id);
        let mut constraints = vec![];

        // Type Parameters
        let hir_parameters = generics.type_parameters.as_ref().map(|f| &f.parameters);
        if let Some(hir_parameters) = hir_parameters {
            for param in hir_parameters.iter() {
                let Some(bounds) = &param.bounds else {
                    continue;
                };

                let param_def_id = self.context.def_id(param.id);
                let ty = self.context.type_of(param_def_id);
                for bound in bounds.iter() {
                    let span = bound.path.path.span;
                    let constraint = Constraint::Bound {
                        ty,
                        interface: lower::lower_interface_reference(
                            param_def_id,
                            &bound.path,
                            self.context,
                        ),
                    };
                    constraints.push((constraint, span));
                }
            }
        }

        // Where Clause
        let mut icx = InferenceContext::new(self.context);
        if let Some(clause) = &generics.where_clause {
            for requirement in clause.requirements.iter() {
                match &requirement {
                    taroc_hir::GenericRequirement::SameTypeRequirement(node) => {
                        let constraint = Constraint::TypeEquality(
                            lower::lower_type(&node.bounded_type, &mut icx),
                            lower::lower_type(&node.bound, &mut icx),
                        );

                        let constraint = (constraint, node.bounded_type.span.to(node.bound.span));
                        constraints.push(constraint);
                    }
                    taroc_hir::GenericRequirement::ConformanceRequirement(node) => {
                        for bound in node.bounds.iter() {
                            let def_id = self
                                .context
                                .resolution(node.bounded_type.id)
                                .def_id()
                                .expect("def id");

                            let constraint = Constraint::Bound {
                                ty: lower::lower_type(&node.bounded_type, &mut icx),
                                interface: lower::lower_interface_reference(
                                    def_id,
                                    &bound.path,
                                    self.context,
                                ),
                            };

                            let span = node.bounded_type.span.to(node
                                .bounds
                                .last()
                                .map(|f| f.path.path.span)
                                .unwrap_or(node.bounded_type.span));
                            constraints.push((constraint, span));
                        }
                    }
                };
            }
        }

        let predicates = DefinitionConstraints { constraints };
        self.context.cache_def_constraints(def_id, predicates);
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
                self.collect_defined_type(decl.id, decl.identifier, node, &decl.attributes)
            }
            DeclarationKind::TypeAlias(node) => self.collect_alias(decl.id, node),
            DeclarationKind::EnumCase(node) => {
                for variant in node.members.iter() {
                    let id = self.context.def_id(variant.id);
                    let parent = self.context.parent(id);
                    let parent_ty = self.context.type_of(parent);
                    self.context.cache_type(id, parent_ty);
                }
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, decl, context)
    }
}

impl<'ctx> TypeCollector<'ctx> {
    fn collect_defined_type(
        &mut self,
        id: NodeID,
        ident: Identifier,
        node: &DefinedType,
        attrs: &AttributeList,
    ) {
        let name = ident.symbol;
        let def_id = self.context.def_id(id);
        let is_std = self.context.session().config.is_std;
        let arguments = self.context.type_arguments(def_id);

        let ty = if is_std && attributes_contain(attrs, Symbol::with("builtin")) {
            if let Some(builtin) = self.check_builtin(name, def_id) {
                builtin
            } else if let Some(builtin) = self.check_generic_builtin(name, def_id, arguments) {
                builtin
            } else {
                let message = format!("uknown builtin type {}", name);
                self.context.diagnostics.error(message, ident.span);
                self.context.store.common_types.error
            }
        } else {
            match node.kind {
                DefinedTypeKind::Struct | DefinedTypeKind::Enum => {
                    let adt_def = AdtDef {
                        name,
                        kind: if matches!(node.kind, DefinedTypeKind::Struct) {
                            AdtKind::Struct
                        } else {
                            AdtKind::Enum
                        },
                        id: def_id,
                    };
                    let kind = TyKind::Adt(adt_def, arguments, None);
                    let ty = self.context.store.interners.intern_ty(kind);
                    ty
                }
                DefinedTypeKind::Interface => self.context.store.common_types.ignore,
            }
        };

        self.context.cache_type(def_id, ty);

        if is_std && attributes_contain(attrs, Symbol::with("foundation")) {
            let mut store = self
                .context
                .store
                .common_types
                .mappings
                .foundation
                .borrow_mut();

            let previous = store.insert(name, def_id);

            if let Some(_) = previous {
                let message = format!("already set foundation type {}", name);
                self.context.diagnostics.error(message, ident.span);
            }
        }
    }

    fn collect_alias(&mut self, id: NodeID, node: &TypeAlias) {
        let def_id = self.context.def_id(id);
        let Some(rhs) = &node.ty else {
            return;
        };
        let mut icx = InferenceContext::new(self.context);
        let rhs = lower::lower_type(rhs, &mut icx);
        self.context.cache_type(def_id, rhs);
    }
}
impl<'ctx> TypeCollector<'ctx> {
    fn check_builtin(&self, symbol: Symbol, id: DefinitionID) -> Option<Ty<'ctx>> {
        let store = &self.context.store;
        let value = match symbol.as_str() {
            "Bool" => {
                store.common_types.mappings.bool.set(Some(id));
                store.common_types.bool
            }
            "Rune" => {
                store.common_types.mappings.rune.set(Some(id));
                store.common_types.rune
            }
            "USize" => {
                store.common_types.mappings.uint.set(Some(id));
                store.common_types.uint
            }
            "UInt8" => {
                store.common_types.mappings.uint8.set(Some(id));
                store.common_types.uint8
            }
            "UInt16" => {
                store.common_types.mappings.uint16.set(Some(id));
                store.common_types.uint16
            }
            "UInt32" => {
                store.common_types.mappings.uint32.set(Some(id));
                store.common_types.uint32
            }
            "UInt64" => {
                store.common_types.mappings.uint64.set(Some(id));
                store.common_types.uint64
            }
            "ISize" => {
                store.common_types.mappings.int.set(Some(id));
                store.common_types.int
            }
            "Int8" => {
                store.common_types.mappings.int8.set(Some(id));
                store.common_types.int8
            }
            "Int16" => {
                store.common_types.mappings.int16.set(Some(id));
                store.common_types.int16
            }
            "Int32" => {
                store.common_types.mappings.int32.set(Some(id));
                store.common_types.int32
            }
            "Int64" => {
                store.common_types.mappings.int64.set(Some(id));
                store.common_types.int64
            }
            "Float" => {
                store.common_types.mappings.float32.set(Some(id));
                store.common_types.float32
            }
            "Double" => {
                store.common_types.mappings.float64.set(Some(id));
                store.common_types.float64
            }
            _ => return None,
        };

        return Some(value);
    }

    fn check_generic_builtin(
        &self,
        symbol: Symbol,
        id: DefinitionID,
        arguments: GenericArguments<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let store = &self.context.store;
        match symbol.as_str() {
            "Array" => {
                store.common_types.mappings.array.set(Some(id));
                let kind = TyKind::Array(arguments.first().unwrap().ty().unwrap(), 0); // TODO
                let ty = self.context.store.interners.intern_ty(kind);
                return Some(ty);
            }
            "ImmutablePointer" => {
                store.common_types.mappings.const_ptr.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Pointer(ty, Mutability::Immutable);
                let ty = self.context.store.interners.intern_ty(kind);
                return Some(ty);
            }
            "MutablePointer" => {
                store.common_types.mappings.ptr.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Pointer(ty, Mutability::Mutable);
                let ty = self.context.store.interners.intern_ty(kind);
                return Some(ty);
            }
            "ImmutableReference" => {
                store.common_types.mappings.const_ref.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Reference(ty, Mutability::Immutable);
                let ty = self.context.store.interners.intern_ty(kind);
                return Some(ty);
            }
            "MutableReference" => {
                store.common_types.mappings.mut_ref.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Reference(ty, Mutability::Mutable);
                let ty = self.context.store.interners.intern_ty(kind);
                return Some(ty);
            }
            _ => return None,
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
                match &node.kind {
                    DefinedTypeKind::Struct => {
                        // create struct definition
                        let def = StructDefinition {
                            id,
                            name,
                            fields: Default::default(),
                        };

                        self.context.cache_struct_def(id, def);
                    }
                    DefinedTypeKind::Enum => {
                        let def = EnumDefinition {
                            id,
                            name,
                            variants: Default::default(),
                        };

                        self.context.cache_enum_def(id, def);
                    }
                    DefinedTypeKind::Interface => {
                        let def = InterfaceDefinition {
                            id,
                            name,
                            requirements: Default::default(),
                            parameters: self.context.type_arguments(id),
                        };

                        self.context.cache_interface_def(id, def);
                    }
                };

                self.parent = Some(id);
            }
            DeclarationKind::Variable(node) if matches!(context, DeclarationContext::Struct) => {
                let name = declaration.identifier.symbol;
                let ty = node.ty.as_ref().unwrap();
                let mut icx = InferenceContext::new(self.context);

                // Struct Field
                let ty = lower::lower_type(ty, &mut icx);
                let field = StructField {
                    name,
                    ty,
                    mutability: node.mutability,
                };
                self.context
                    .update_struct_def(self.parent.unwrap(), move |def| {
                        let previous = def.fields.insert(declaration.identifier.symbol, field);
                        debug_assert!(
                            previous.is_none(),
                            "overlapping field defintions should be caught by resolver"
                        );
                    });
            }
            DeclarationKind::AssociatedType(_, default_ty)
                if matches!(context, DeclarationContext::Interface) =>
            {
                let name = declaration.identifier.symbol;
                let mut icx = InferenceContext::new(self.context);

                let assoc = AssociatedTypeDefinition {
                    name,
                    default_type: default_ty
                        .as_ref()
                        .map(|ty| lower::lower_type(&ty, &mut icx)),
                };

                self.context
                    .update_interface_def(self.parent.unwrap(), |def| {
                        def.requirements.types.push(assoc);
                    });
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, declaration, context);
        self.parent = previous
    }

    fn visit_variant(&mut self, variant: &taroc_hir::Variant) -> Self::Result {
        let id = self.context.def_id(variant.id);
        let name = variant.identifier.symbol;
        let mut icx = InferenceContext::new(self.context);

        let kind = match &variant.kind {
            taroc_hir::VariantKind::Unit => EnumVariantKind::Unit,
            taroc_hir::VariantKind::Tuple(fields) => {
                let types: Vec<Ty<'ctx>> = fields
                    .iter()
                    .map(|f| {
                        let ty = lower::lower_type(&f.ty, &mut icx);
                        ty
                    })
                    .collect();

                EnumVariantKind::Tuple(types)
            }
            taroc_hir::VariantKind::Struct(fields) => {
                let fields: FxHashMap<Symbol, StructField<'ctx>> =
                    fields.iter().fold(Default::default(), |mut acc, field| {
                        let ty = lower::lower_type(&field.ty, &mut icx);

                        let field = StructField {
                            name: field.identifier.symbol,
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

                let def = StructDefinition { id, name, fields };
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

        self.context.update_enum_def(self.parent.unwrap(), |def| {
            let previous = def.variants.insert(node.name, node);

            debug_assert!(
                previous.is_none(),
                "variant names must be unique, this should be caught by the resolver"
            );
        });
    }
}

/// Collect Conformances
struct ConformanceCollector<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> ConformanceCollector<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> ConformanceCollector<'ctx> {
        ConformanceCollector { context }
    }

    fn run<'a>(package: &Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = ConformanceCollector::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl<'ctx> HirVisitor for ConformanceCollector<'ctx> {
    fn visit_declaration(
        &mut self,
        declaration: &Declaration,
        context: DeclarationContext,
    ) -> Self::Result {
        let id = self.context.def_id(declaration.id);
        match &declaration.kind {
            DeclarationKind::DefinedType(node) => {
                self.collect_interface_conformances(id, &node.generics.inheritance);
            }
            DeclarationKind::Extend(node) => {
                let id = self.context.extension_target(id);
                self.collect_interface_conformances(id, &node.generics.inheritance);
            }
            _ => {}
        };

        taroc_hir::visitor::walk_declaration(self, declaration, context);
    }
}

impl<'ctx> ConformanceCollector<'ctx> {
    pub fn collect_interface_conformances(
        &mut self,
        def_id: DefinitionID,
        node: &Option<taroc_hir::Inheritance>,
    ) {
        let Some(node) = node else {
            return;
        };

        for node in node.interfaces.iter() {
            let reference = lower::lower_interface_reference(def_id, node, self.context);

            // Validate & Store
            self.context.with_type_database(None, |database| {
                let contains = database
                    .conformances
                    .entry(def_id)
                    .or_default()
                    .contains(&reference);

                if contains {
                    let msg = format!(
                        "redundant conformance to '{}'",
                        node.path.segments.last().unwrap().identifier.symbol
                    );
                    self.context.diagnostics.error(msg, node.path.span);
                    return;
                }

                database
                    .conformances
                    .entry(def_id)
                    .or_default()
                    .insert(reference);

                database
                    .conformances_span
                    .insert((def_id, reference), node.path.span);
            });
        }
    }
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
            DeclarationKind::DefinedType(_) | DeclarationKind::Namespace(_) => {
                self.parent = Some(def_id);
            }
            DeclarationKind::Extend(_) => {
                self.parent = Some(self.context.extension_target(def_id));
            }
            DeclarationKind::Function(func) => {
                let signature = utils::convert_to_labeled_signature(func, self.context);

                {
                    let arguments = self.context.type_arguments(def_id);
                    let kind = TyKind::FnDef(def_id, arguments);
                    let ty = self.context.store.interners.intern_ty(kind);
                    self.context.cache_type(def_id, ty);

                    self.context.cache_signature(def_id, signature.clone());
                };

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
                        self.context.update_interface_def(parent, |def| {
                            def.requirements.methods.push(requirement);
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
                                .clone()
                                .borrow_mut()
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
                            is_required: func.block.is_none(),
                        };
                        self.context.update_interface_def(parent, |def| {
                            def.requirements.operators.push(requirement);
                        });
                    }
                    _ => {
                        // Operator Implementation
                        self.context.with_type_database(None, |database| {
                            let store = database
                                .def_to_functions
                                .entry(parent)
                                .or_insert(Default::default());

                            store
                                .clone()
                                .borrow_mut()
                                .operators
                                .entry(*kind)
                                .or_default()
                                .push(signature);
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
                let mut icx = InferenceContext::new(self.context);
                let ty = lower::lower_type(&node.ty, &mut icx);

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
                            store
                                .clone()
                                .borrow_mut()
                                .properties
                                .insert(decl.identifier.symbol, signature)
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

                    store.clone().borrow_mut().constructors.push(signature)
                });
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, decl, context);
        self.parent = previous;
    }
}
