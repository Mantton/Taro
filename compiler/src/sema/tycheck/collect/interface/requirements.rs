use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor},
    sema::{
        models::{
            AssociatedTypeDefinition, InterfaceConstantRequirement, InterfaceMethodRequirement,
            InterfacePropertyRequirement, InterfaceRequirements,
        },
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
};

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: Gcx<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, d: &hir::Declaration) -> Self::Result {
        if !matches!(
            self.context.definition_kind(d.id),
            DefinitionKind::Interface
        ) {
            return;
        }

        if let hir::DeclarationKind::Interface(node) = &d.kind {
            self.collect(d.id, node);
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, id: DefinitionID, node: &hir::Interface) {
        let gcx = self.context;

        let mut methods = Vec::new();
        let mut properties = Vec::new();
        let mut types = Vec::new();
        let mut constants = Vec::new();

        for decl in &node.declarations {
            self.collect_requirement(
                id,
                decl,
                &mut methods,
                &mut properties,
                &mut types,
                &mut constants,
            );
        }

        let requirements = InterfaceRequirements {
            methods,
            properties,
            types,
            constants,
        };

        // Allocate and cache
        let requirements = gcx.store.arenas.interface_requirements.alloc(requirements);
        gcx.with_session_type_database(|db| {
            db.interface_requirements.insert(id, requirements);
        });
    }

    fn collect_requirement(
        &mut self,
        interface_id: DefinitionID,
        node: &hir::AssociatedDeclaration,
        methods: &mut Vec<InterfaceMethodRequirement<'ctx>>,
        properties: &mut Vec<InterfacePropertyRequirement<'ctx>>,
        types: &mut Vec<AssociatedTypeDefinition<'ctx>>,
        constants: &mut Vec<InterfaceConstantRequirement<'ctx>>,
    ) {
        let gcx = self.context;
        let def_id = node.id;

        match &node.kind {
            hir::AssociatedDeclarationKind::Function(func) => {
                let has_self = func
                    .signature
                    .prototype
                    .inputs
                    .first()
                    .is_some_and(|param| gcx.symbol_eq(param.name.symbol, "self"));
                let req = InterfaceMethodRequirement {
                    id: def_id,
                    name: node.identifier.symbol,
                    signature: gcx.get_signature(def_id),
                    has_self,
                    is_required: func.block.is_none(),
                };
                methods.push(req);
            }
            hir::AssociatedDeclarationKind::Type(_alias) => {
                // Don't lower default type here - defer to avoid circular dependencies
                let req = AssociatedTypeDefinition {
                    id: def_id,
                    name: node.identifier.symbol,
                    default_type: None,
                };
                types.push(req);
            }
            // Operators are now implemented via trait methods
            // hir::AssociatedDeclarationKind::Operator(op) => {
            //     let req = InterfaceOperatorRequirement {
            //         id: def_id,
            //         kind: op.kind,
            //         signature: gcx.get_signature(def_id),
            //         is_required: op.function.block.is_none(),
            //     };
            //     operators.push(req);
            // }
            hir::AssociatedDeclarationKind::Constant(c) => {
                let icx = DefTyLoweringCtx::new(interface_id, gcx);
                let ty = icx.lowerer().lower_type(&c.ty);
                let default = if c.expr.is_some() {
                    gcx.try_get_const(def_id)
                } else {
                    None
                };
                let req = InterfaceConstantRequirement {
                    id: def_id,
                    name: node.identifier.symbol,
                    ty,
                    default,
                };
                constants.push(req);
            }
            hir::AssociatedDeclarationKind::Property(property) => {
                let lowerer = DefTyLoweringCtx::new(def_id, gcx);
                let ty = lowerer.lowerer().lower_type(&property.ty);
                gcx.cache_type(def_id, ty);
                if let Some(setter_id) = property.setter_id {
                    let setter = gcx.get_signature(setter_id);
                    if setter.inputs.len() != 2 || setter.inputs[1].ty != ty {
                        gcx.dcx().emit_error(
                            format!(
                                "setter requirement for property '{}' must accept a value of type {}",
                                gcx.symbol_text(node.identifier.symbol),
                                ty.format(gcx)
                            ),
                            Some(node.span),
                        );
                    }
                }
                properties.push(InterfacePropertyRequirement {
                    id: def_id,
                    name: node.identifier.symbol,
                    ty,
                    getter_id: property.getter_id,
                    setter_id: property.setter_id,
                });
            }
        }
    }
}
