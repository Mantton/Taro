use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, HirVisitor},
    hir::{DefinitionID, StdItem},
    sema::models::{AdtDef, AdtKind, Ty, TyKind},
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
};

use rustc_hash::FxHashMap;
use std::rc::Rc;

/// Field types needed to check conditional inline derivations before all
/// layouts exist. Defaults contribute only their presence at this stage.
#[derive(Default)]
pub(crate) struct HeaderFields<'ctx> {
    declarations: FxHashMap<DefinitionID, Rc<[(hir::Type, bool)]>>,
    lowered: FxHashMap<hir::NodeID, Option<Ty<'ctx>>>,
}

impl HeaderFields<'_> {
    fn register<'a>(
        &mut self,
        id: DefinitionID,
        fields: impl Iterator<Item = &'a hir::FieldDefinition>,
    ) {
        self.declarations.insert(
            id,
            fields
                .map(|field| ((*field.ty).clone(), field.default_value.is_some()))
                .collect(),
        );
    }
}

/// Normal layout collection and derivation selection must agree even if a
/// component contains another associated constant. Detect recursion per field.
pub(super) fn lower_field<'ctx>(
    gcx: GlobalContext<'ctx>,
    owner: DefinitionID,
    field: &hir::Type,
) -> Ty<'ctx> {
    let mut fields = gcx.store.header_fields.borrow_mut();
    if let Some(cached) = fields.lowered.get(&field.id) {
        return cached.unwrap_or_else(|| {
            gcx.dcx()
                .emit_error("cycle in stored field type".into(), Some(field.span));
            gcx.types.error
        });
    }
    let cache = fields.declarations.contains_key(&owner);
    if cache {
        fields.lowered.insert(field.id, None);
    }
    drop(fields);
    let ty = DefTyLoweringCtx::new(owner, gcx)
        .lowerer()
        .lower_type(field);
    if cache {
        gcx.store
            .header_fields
            .borrow_mut()
            .lowered
            .insert(field.id, Some(ty));
    }
    ty
}

pub(crate) fn derived_fields<'ctx>(
    gcx: GlobalContext<'ctx>,
    owner: DefinitionID,
    capability: StdItem,
) -> Option<Vec<Ty<'ctx>>> {
    use crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args;
    let mut current = gcx.get_type(owner);
    let mut fields = Vec::new();
    let mut visited = rustc_hash::FxHashSet::default();
    while let TyKind::Adt(adt, args) = current.kind() {
        if !visited.insert(adt.id) {
            break;
        }
        let declared = gcx
            .store
            .header_fields
            .borrow()
            .declarations
            .get(&adt.id)
            .cloned();
        let Some(declared) = declared else {
            if adt.id == owner {
                return None;
            }
            // An imported base already has a flattened layout.
            let base = gcx.get_struct_definition(adt.id);
            fields.extend(
                base.fields
                    .iter()
                    .filter(|field| {
                        capability != StdItem::Default || field.default_provider.is_none()
                    })
                    .map(|field| instantiate_ty_with_args(gcx, field.ty, args)),
            );
            break;
        };
        fields.extend(
            declared
                .iter()
                .filter(|(_, has_default)| capability != StdItem::Default || !has_default)
                .map(|(field, _)| {
                    instantiate_ty_with_args(gcx, lower_field(gcx, adt.id, field), args)
                }),
        );
        if matches!(capability, StdItem::Encodable | StdItem::Decodable) {
            break;
        }
        let Some(base) = gcx.class_base(current) else {
            break;
        };
        current = base;
    }
    Some(fields)
}

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        match &node.kind {
            hir::DeclarationKind::Struct(value) => {
                self.cache_adt_type(node.id, AdtKind::Struct);
                if value.class_header.is_some()
                    || (value.generics.type_parameters.is_some() && value.conformances.is_some())
                {
                    self.context
                        .store
                        .header_fields
                        .borrow_mut()
                        .register(node.id, value.fields.iter());
                }
                if let Some(header) = value.class_header {
                    let TyKind::Adt(adt_def, _) = self.context.get_type(node.id).kind() else {
                        unreachable!()
                    };
                    self.context.cache_struct_definition(
                        node.id,
                        crate::sema::models::StructDefinition {
                            adt_def,
                            class_info: Some(crate::sema::models::ClassInfo {
                                initializers: &[],
                                base: None,
                                methods: &[],
                                payload: None,
                                is_final: header.is_final,
                            }),
                            positional: false,
                            has_initializer: false,
                            repr: crate::sema::models::StructRepr::Taro,
                            fields: &[],
                        },
                    );
                }
            }
            hir::DeclarationKind::Enum(value) => {
                self.cache_adt_type(node.id, AdtKind::Enum);
                if value.generics.type_parameters.is_some() && value.conformances.is_some() {
                    let fields = value
                        .variants
                        .iter()
                        .flat_map(|variant| match &variant.kind {
                            hir::VariantKind::Unit => [].iter(),
                            hir::VariantKind::Tuple(fields) | hir::VariantKind::Struct(fields) => {
                                fields.iter()
                            }
                        });
                    self.context
                        .store
                        .header_fields
                        .borrow_mut()
                        .register(node.id, fields);
                }
            }
            hir::DeclarationKind::OpaqueType => {
                self.cache_opaque_type(node.id);
            }
            _ => {}
        }
        hir::walk_declaration(self, node)
    }
}

impl<'ctx> Actor<'ctx> {
    fn cache_adt_type(&self, id: hir::DefinitionID, kind: AdtKind) {
        let adt_def = AdtDef { kind, id };
        let args = crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(
            self.context,
            id,
        );
        let ty = Ty::new(TyKind::Adt(adt_def, args), self.context);
        self.context.cache_type(id, ty);
    }

    fn cache_opaque_type(&self, id: hir::DefinitionID) {
        let ty = Ty::new(TyKind::Opaque(id), self.context);
        self.context.cache_type(id, ty);
    }
}
