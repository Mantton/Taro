use crate::{
    sema::models::{
        AssociatedTypeBinding, Const, GenericArgument, InterfaceGoal, InterfaceReference, Ty,
        TyKind,
    },
    utils::intern::List,
};

/// Allocation-free structural queries. Returning true stops the traversal.
/// Aliases expose their arguments, not their definitions; the query decides
/// whether an alias itself is significant or needs semantic normalization.
pub(crate) trait TypeVisitor<'ctx> {
    fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
        ty.super_visit_with(self)
    }

    fn visit_const(&mut self, value: Const<'ctx>) -> bool {
        value.ty.visit_with(self)
    }
}

pub(crate) trait TypeVisitable<'ctx> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool;
}

pub(crate) trait TypeSuperVisitable<'ctx> {
    fn super_visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool;
}

impl<'ctx> TypeVisitable<'ctx> for Ty<'ctx> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        visitor.visit_ty(*self)
    }
}

impl<'ctx> TypeSuperVisitable<'ctx> for Ty<'ctx> {
    fn super_visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        match self.kind() {
            TyKind::Array { element, len } => {
                element.visit_with(visitor) || len.visit_with(visitor)
            }
            TyKind::Adt(_, args) | TyKind::Alias { args, .. } => args.visit_with(visitor),
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => inner.visit_with(visitor),
            TyKind::Tuple(items) => items.visit_with(visitor),
            TyKind::FnPointer { inputs, output } => {
                inputs.visit_with(visitor) || output.visit_with(visitor)
            }
            TyKind::Closure {
                captured_generics,
                inputs,
                output,
                ..
            } => {
                captured_generics.visit_with(visitor)
                    || inputs.visit_with(visitor)
                    || output.visit_with(visitor)
            }
            TyKind::BoxedExistential { interfaces } => interfaces.visit_with(visitor),
            TyKind::Bool
            | TyKind::Rune
            | TyKind::String
            | TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Infer(_)
            | TyKind::Parameter(_)
            | TyKind::Opaque(_)
            | TyKind::Error
            | TyKind::Never => false,
        }
    }
}

impl<'ctx> TypeVisitable<'ctx> for Const<'ctx> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        visitor.visit_const(*self)
    }
}

impl<'ctx> TypeVisitable<'ctx> for GenericArgument<'ctx> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        match self {
            GenericArgument::Type(ty) => ty.visit_with(visitor),
            GenericArgument::Const(value) => value.visit_with(visitor),
        }
    }
}

impl<'ctx> TypeVisitable<'ctx> for AssociatedTypeBinding<'ctx> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        self.ty.visit_with(visitor)
    }
}

impl<'ctx> TypeVisitable<'ctx> for InterfaceReference<'ctx> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        self.arguments.visit_with(visitor) || self.bindings.visit_with(visitor)
    }
}

impl<'ctx> TypeVisitable<'ctx> for InterfaceGoal<'ctx> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        // The parameter environment supplies assumptions, not goal arguments.
        self.self_ty.visit_with(visitor)
            || self.interface_args.visit_with(visitor)
            || self.bindings.visit_with(visitor)
    }
}

impl<'ctx, T: TypeVisitable<'ctx>> TypeVisitable<'ctx> for [T] {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        self.iter().any(|value| value.visit_with(visitor))
    }
}

impl<'ctx, T: TypeVisitable<'ctx>> TypeVisitable<'ctx> for List<'ctx, T> {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        self.iter().any(|value| value.visit_with(visitor))
    }
}

impl<'ctx, T: TypeVisitable<'ctx> + ?Sized> TypeVisitable<'ctx> for &T {
    fn visit_with<V: TypeVisitor<'ctx> + ?Sized>(&self, visitor: &mut V) -> bool {
        (**self).visit_with(visitor)
    }
}
