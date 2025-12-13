use crate::{
    compile::context::GlobalContext,
    hir::{self, Resolution},
    sema::{
        models::{AdtDef, AdtKind, Ty, TyKind},
        resolve::models::PrimaryType,
    },
};

pub trait TypeLowerer<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
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
            hir::TypeKind::Tuple(..) => todo!(),
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
                PrimaryType::String => todo!(),
                PrimaryType::Bool => gcx.types.bool,
                PrimaryType::Rune => gcx.types.rune,
            },
            Resolution::Definition(id, kind) => match kind {
                crate::sema::resolve::models::DefinitionKind::Struct => {
                    let ident = gcx.definition_ident(id);
                    let def = AdtDef {
                        name: ident.symbol,
                        kind: AdtKind::Struct,
                        id,
                    };
                    Ty::new(TyKind::Adt(def), gcx)
                }
                _ => todo!("nominal type lowering for {kind:?}"),
            },
            Resolution::SelfTypeAlias(..) => todo!(),
            Resolution::InterfaceSelfTypeParameter(..) => todo!(),

            Resolution::SelfConstructor(..) => todo!(),
            Resolution::ImplicitSelfParameter => todo!(),
            Resolution::Foundation(..) => todo!(),
            Resolution::Error => gcx.types.error,

            Resolution::FunctionSet(..) | Resolution::LocalVariable(_) => {
                unreachable!("value resolution")
            }
        }
    }
}
