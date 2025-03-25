use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, Resolution};
use taroc_ty::{Ty, TyKind};

pub fn lower_type<'ctx>(
    ty: &taroc_hir::Type,
    context: GlobalContext<'ctx>,
    index: usize,
) -> taroc_ty::Ty<'ctx> {
    let actor = TypeLowerer { context, index };
    actor.lower(ty)
}

struct TypeLowerer<'ctx> {
    index: usize,
    context: GlobalContext<'ctx>,
}

impl<'ctx> TypeLowerer<'ctx> {
    pub fn lower(mut self, ty: &taroc_hir::Type) -> Ty<'ctx> {
        let mk = |k| self.context.store.interners.intern_ty(k);
        let ty = match &ty.kind {
            taroc_hir::TypeKind::Pointer(ty, mutability) => mk(TyKind::Pointer(
                lower_type(ty, self.context, self.index),
                *mutability,
            )),
            taroc_hir::TypeKind::Reference(_, mutability) => mk(TyKind::Reference(
                lower_type(ty, self.context, self.index),
                *mutability,
            )),
            taroc_hir::TypeKind::Tuple(items) => {
                let items: Vec<Ty<'ctx>> = items
                    .iter()
                    .map(|ty| lower_type(ty, self.context, self.index))
                    .collect();
                let items = self.context.store.interners.intern_ty_list(&items);
                mk(TyKind::Tuple(items))
            }
            taroc_hir::TypeKind::Path(path) => self.lower_unchecked_path(path, ty.id),
            taroc_hir::TypeKind::Array { size, element } => {
                let element = self.lower(element);
                todo!()
            }
            taroc_hir::TypeKind::AnonStruct { .. } => todo!("planned feature"),
            taroc_hir::TypeKind::Function {
                inputs,
                output,
                is_async,
            } => todo!(),
            taroc_hir::TypeKind::ImplicitSelf => todo!(),
            taroc_hir::TypeKind::InferedClosureParameter => todo!(),
            taroc_hir::TypeKind::SomeOrAny(kind, ty) => {
                let ty = self.lower(ty);
                todo!()
            }
            taroc_hir::TypeKind::Composite(items) => todo!(),
        };

        println!("Actually Worked!");
        ty
    }
}

impl<'ctx> TypeLowerer<'ctx> {
    fn lower_unchecked_path(&mut self, path: &taroc_hir::Path, id: NodeID) -> Ty<'ctx> {
        let res = self.context.resolution(id, self.index);
        self.lower_path(path, id, res)
    }

    fn lower_path(&mut self, path: &taroc_hir::Path, id: NodeID, res: Resolution) -> Ty<'ctx> {
        match res {
            Resolution::Definition(
                def_id,
                DefinitionKind::Enum | DefinitionKind::Struct | DefinitionKind::TypeAlias,
            ) => self.lower_path_segment(path.segments.last().unwrap(), def_id),
            Resolution::InterfaceSelfTypeAlias(definition_id) => todo!(),
            Resolution::SelfTypeAlias(definition_id) => todo!(),
            Resolution::ConformanceSelfTypeAlias {
                ty,
                interface,
                conformance,
            } => todo!(),
            Resolution::FunctionSet(hash_set) => {
                unreachable!("cannot resolve type to set of functions")
            }
            Resolution::Local(..) => unreachable!("cannot resolve type to local variable"),
            Resolution::Error => {
                unreachable!("prereported resolution error, this compiler pass should not happen")
            }
            _ => todo!("implement!"),
        }
    }

    fn lower_path_segment(
        &mut self,
        segment: &taroc_hir::PathSegment,
        id: DefinitionID,
    ) -> Ty<'ctx> {
        let generics = self.lower_generics_of_path_segment(id, segment);
        if let DefinitionKind::TypeAlias = self.context.def_kind(id) {
            todo!("alias")
        } else {
            let ty = self.context.type_of(id);
            println!("ty : {:?}", ty);
            todo!("instantiate with generic arguments")
        }

        todo!()
    }

    fn lower_generics_of_path_segment(
        &mut self,
        id: DefinitionID,
        segment: &taroc_hir::PathSegment,
    ) {
        self.context.diagnostics.warn(
            format!("Looking at {:?}", segment.identifier.symbol),
            segment.identifier.span,
        );
        let generics = self.context.generics_of(id);
        println!("{}", generics.parameters.len());
        check_generic_arg_count(&generics, segment);

        if generics.is_empty() {
            return;
        }
        todo!()
    }
}

fn check_generic_arg_count(generics: &taroc_ty::Generics, segment: &taroc_hir::PathSegment) {
    let defaults_count = generics.default_count();
    let total_count = generics.total_count();

    let min = total_count - defaults_count;
    let provided = segment
        .arguments
        .as_ref()
        .map(|v| v.arguments.len())
        .unwrap_or(0);

    if (min..=total_count).contains(&provided) {
        println!("correct number of arguments");
        return;
    }

    if provided > total_count {
        println!("excess number of generic arguments")
    } else {
        println!("misssing generics")
    }

    todo!()
}
