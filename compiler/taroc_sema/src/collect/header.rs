use crate::GlobalContext;
use crate::ty::{AdtDef, AdtKind, GenericArguments, Ty, TyKind};
use taroc_error::CompileResult;
use taroc_hir::{
    DefinitionID, DefinitionKind, Mutability, attributes_contain, visitor::HirVisitor,
};
use taroc_span::{Identifier, Symbol};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

/// Collect Top Level Defintitions and Generate Corresponding `types::Ty`
struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        let id = d.id;
        match &d.kind {
            taroc_hir::DeclarationKind::Struct(_) => self.collect(id, d.identifier, &d.attributes),
            taroc_hir::DeclarationKind::Enum(_) => self.collect(id, d.identifier, &d.attributes),
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, d);
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        let id = d.id;
        match &d.kind {
            taroc_hir::FunctionDeclarationKind::Struct(_) => {
                self.collect(id, d.identifier, &d.attributes)
            }
            taroc_hir::FunctionDeclarationKind::Enum(_) => {
                self.collect(id, d.identifier, &d.attributes)
            }
            _ => {}
        }

        taroc_hir::visitor::walk_function_declaration(self, d);
    }

    fn visit_variant(&mut self, v: &taroc_hir::Variant) -> Self::Result {
        let def_id = self.context.def_id(v.id);
        let parent = self.context.parent(def_id);
        let ty = self.context.type_of(parent);
        match &v.kind {
            taroc_hir::VariantKind::Unit(ctor_id) => {
                let ctor_def_id = self.context.def_id(*ctor_id);
                self.context.cache_type(ctor_def_id, ty);
            }
            taroc_hir::VariantKind::Tuple(ctor_id, _) => {
                let ctor_def_id = self.context.def_id(*ctor_id);
                let arguments = self.context.type_arguments(parent);
                let kind = TyKind::FnDef(ctor_def_id, arguments);
                let ty = self.context.mk_ty(kind);
                self.context.cache_type(ctor_def_id, ty);
            }
            taroc_hir::VariantKind::Struct(..) => {}
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(
        &mut self,
        id: taroc_hir::NodeID,
        ident: Identifier,
        attrs: &taroc_hir::AttributeList,
    ) {
        let name = ident.symbol;
        let def_id = self.context.def_id(id);
        let def_kind = self.context.def_kind(def_id);
        let arguments = self.context.type_arguments(def_id);
        let is_std = self.context.session().config.is_std;
        // println!("Collecting Type Header for '{name}'");

        let ty = if is_std && attributes_contain(attrs, Symbol::with("builtin")) {
            if let Some(builtin) = self.check_generic_builtin(name, def_id, arguments) {
                builtin
            } else {
                let message = format!("uknown builtin type {}", name);
                self.context.diagnostics.error(message, ident.span);
                self.context.store.common_types.error
            }
        } else {
            let adt_def = AdtDef {
                name,
                kind: if matches!(def_kind, DefinitionKind::Struct) {
                    AdtKind::Struct
                } else {
                    AdtKind::Enum
                },
                id: def_id,
            };
            let kind = TyKind::Adt(adt_def, arguments);
            self.context.mk_ty(kind)
        };

        self.context.cache_type(def_id, ty);
        let is_std = self.context.session().config.is_std;

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
                let ty = self.context.mk_ty(kind);
                return Some(ty);
            }
            "ImmutablePointer" => {
                store.common_types.mappings.const_ptr.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Pointer(ty, Mutability::Immutable);
                let ty = self.context.mk_ty(kind);
                return Some(ty);
            }
            "MutablePointer" => {
                store.common_types.mappings.ptr.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Pointer(ty, Mutability::Mutable);
                let ty = self.context.mk_ty(kind);
                return Some(ty);
            }
            "ImmutableReference" => {
                store.common_types.mappings.const_ref.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Reference(ty, Mutability::Immutable);
                let ty = self.context.mk_ty(kind);
                return Some(ty);
            }
            "MutableReference" => {
                store.common_types.mappings.mut_ref.set(Some(id));
                let ty = arguments.first().unwrap().ty().unwrap();
                let kind = TyKind::Reference(ty, Mutability::Mutable);
                let ty = self.context.mk_ty(kind);
                return Some(ty);
            }
            _ => return None,
        };
    }
}
