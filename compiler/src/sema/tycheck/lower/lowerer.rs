use crate::{
    compile::context::GlobalContext,
    hir::{self, DefinitionKind, Resolution},
    sema::{
        models::{AdtDef, AdtKind, Ty, TyKind},
        resolve::models::{PrimaryType, TypeHead},
    },
};

pub trait TypeLowerer<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
    fn current_definition(&self) -> Option<hir::DefinitionID> {
        None
    }
    fn lowerer(&self) -> &dyn TypeLowerer<'ctx>
    where
        Self: Sized,
    {
        self
    }
}

impl<'ctx> dyn TypeLowerer<'ctx> + '_ {
    pub fn lower_type(&self, node: &hir::Type) -> Ty<'ctx> {
        let gcx = self.gcx();
        match &node.kind {
            hir::TypeKind::Nominal(path) => self.lower_nominal_type(node.id, path),
            hir::TypeKind::Pointer(node, mutability) => {
                let internal = self.lower_type(node);
                Ty::new(TyKind::Pointer(internal, *mutability), gcx)
            }
            hir::TypeKind::Reference(node, mutability) => {
                let internal = self.lower_type(node);
                Ty::new(TyKind::Reference(internal, *mutability), gcx)
            }
            hir::TypeKind::Tuple(elements) => {
                let mut lowered = Vec::with_capacity(elements.len());
                for elem in elements {
                    lowered.push(self.lower_type(elem));
                }
                Ty::new(
                    TyKind::Tuple(gcx.store.interners.intern_ty_list(lowered)),
                    gcx,
                )
            }
            hir::TypeKind::Array { .. } => todo!(),
            hir::TypeKind::Function { .. } => todo!(),
            hir::TypeKind::BoxedExistential { .. } => todo!(),
            hir::TypeKind::Infer => todo!(),
        }
    }

    fn lower_nominal_type(&self, node_id: hir::NodeID, path: &hir::ResolvedPath) -> Ty<'ctx> {
        match path {
            hir::ResolvedPath::Resolved(path) => self.lower_resolved_type_path(node_id, path),
            hir::ResolvedPath::Relative(..) => todo!(),
        }
    }

    fn lower_resolved_type_path(&self, _: hir::NodeID, path: &hir::Path) -> Ty<'ctx> {
        let resolution = path.resolution.clone();
        let gcx = self.gcx();
        match resolution {
            Resolution::PrimaryType(k) => match k {
                PrimaryType::Int(k) => Ty::new_int(gcx, k),
                PrimaryType::UInt(k) => Ty::new_uint(gcx, k),
                PrimaryType::Float(k) => Ty::new_float(gcx, k),
                PrimaryType::String => gcx.types.string,
                PrimaryType::Bool => gcx.types.bool,
                PrimaryType::Rune => gcx.types.rune,
            },
            Resolution::Definition(id, DefinitionKind::TypeParameter) => {
                // TODO: Prohibit Generics
                gcx.get_type(id)
            }
            Resolution::Definition(id, kind) => {
                if let Some(from) = self.current_definition() {
                    if !gcx.is_definition_visible(id, from) {
                        let name = gcx.definition_ident(id).symbol;
                        gcx.dcx().emit_error(
                            format!("type '{}' is not visible here", name).into(),
                            Some(path.span),
                        );
                        return gcx.types.error;
                    }
                }
                if gcx.is_std_gc_ptr(id) {
                    return Ty::new(TyKind::GcPtr, gcx);
                }
                match kind {
                    crate::sema::resolve::models::DefinitionKind::Struct
                    | crate::sema::resolve::models::DefinitionKind::Enum => {
                        let ident = gcx.definition_ident(id);
                        let def = AdtDef {
                            name: ident.symbol,
                            kind: match kind {
                                crate::sema::resolve::models::DefinitionKind::Enum => AdtKind::Enum,
                                _ => AdtKind::Struct,
                            },
                            id,
                        };
                        Ty::new(TyKind::Adt(def), gcx)
                    }
                    _ => todo!("nominal type lowering for {kind:?}"),
                }
            }
            Resolution::SelfTypeAlias(id) => match gcx.definition_kind(id) {
                crate::sema::resolve::models::DefinitionKind::Struct
                | crate::sema::resolve::models::DefinitionKind::Enum => gcx.get_type(id),
                crate::sema::resolve::models::DefinitionKind::Extension => {
                    let Some(head) = gcx.get_extension_type_head(id) else {
                        return gcx.types.error;
                    };
                    match head {
                        TypeHead::Nominal(target_id) => gcx.get_type(target_id),
                        TypeHead::GcPtr => Ty::new(TyKind::GcPtr, gcx),
                        TypeHead::Primary(p) => match p {
                            PrimaryType::Int(k) => Ty::new_int(gcx, k),
                            PrimaryType::UInt(k) => Ty::new_uint(gcx, k),
                            PrimaryType::Float(k) => Ty::new_float(gcx, k),
                            PrimaryType::String => gcx.types.string,
                            PrimaryType::Bool => gcx.types.bool,
                            PrimaryType::Rune => gcx.types.rune,
                        },
                        _ => todo!("Self type alias lowering for {head:?}"),
                    }
                }
                other => todo!("Self type alias lowering for {other:?}"),
            },
            Resolution::InterfaceSelfTypeParameter(..) => todo!(),
            Resolution::SelfConstructor(..) => todo!(),
            Resolution::Foundation(..) => todo!(),
            Resolution::Error => gcx.types.error,
            Resolution::FunctionSet(..) | Resolution::LocalVariable(_) => {
                unreachable!("value resolution")
            }
        }
    }
}
