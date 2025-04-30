use index_vec::IndexVec;
use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, NodeID};
use taroc_span::Span;
use taroc_ty::{
    Adjustment, Constraint, FloatVid, GenericArgument, GenericArguments, GenericParameter, InferTy,
    IntVid, NilVid, Ty, TyKind, TyVid, VarBinding,
};

use crate::utils;

/// Maps Generic Parameter IDs to concrete Types.
#[derive(Debug, Clone, Default)]
pub struct SubstitutionMap<'ctx> {
    map: FxHashMap<GenericParameter, GenericArgument<'ctx>>,
}

impl<'ctx> SubstitutionMap<'ctx> {
    pub fn new() -> Self {
        Self {
            map: Default::default(),
        }
    }
    pub fn insert(&mut self, param: GenericParameter, concrete_ty: GenericArgument<'ctx>) {
        self.map.insert(param, concrete_ty);
    }
    pub fn get(&self, param: &GenericParameter) -> Option<&GenericArgument<'ctx>> {
        self.map.get(param)
    }

    /// Merge in all entries from `other`. Panic if any key already exists.
    pub fn extend(&mut self, other: Self) {
        for (param_id, arg) in other.map {
            let entry = self.map.entry(param_id);
            match entry {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    if entry.get() == &arg {
                        continue;
                    }

                    unreachable!("ICE: cannot overwrite substitution")
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(arg);
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CollectedConstraint<'ctx> {
    pub constraint: Constraint<'ctx>,
    pub span: Span,
    pub node: NodeID,
}

pub type TaggedAdjustments = FxHashMap<NodeID, Vec<Adjustment>>;

pub struct InferenceContext<'ctx> {
    pub gcx: GlobalContext<'ctx>,
    constraints: Vec<CollectedConstraint<'ctx>>,
    adjustments: Vec<(Adjustment, NodeID)>,
    pub env: FxHashMap<NodeID, Ty<'ctx>>,

    pub intvar_bindings: IndexVec<IntVid, VarBinding<'ctx, IntVid>>,
    pub tyvar_bindings: IndexVec<TyVid, VarBinding<'ctx, TyVid>>,
    pub floatvar_bindings: IndexVec<FloatVid, VarBinding<'ctx, FloatVid>>,
    pub nilvar_bindings: IndexVec<NilVid, VarBinding<'ctx, NilVid>>,
}

use std::ops::Deref;

impl<'ctx> Deref for InferenceContext<'ctx> {
    type Target = GlobalContext<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.gcx
    }
}

impl<'ctx> InferenceContext<'ctx> {
    pub fn new(context: GlobalContext<'ctx>) -> Self {
        Self {
            gcx: context,
            constraints: Vec::new(),
            env: FxHashMap::default(),
            adjustments: Vec::new(),
            //
            intvar_bindings: Default::default(),
            tyvar_bindings: Default::default(),
            floatvar_bindings: Default::default(),
            nilvar_bindings: Default::default(),
        }
    }

    /// Duplicate `sig.bounds` with the given arguments.
    pub fn instantiate_definition_constraints(
        &mut self,
        id: DefinitionID,
        args: GenericArguments<'ctx>,
    ) {
        let subst = utils::create_substitution_map(id, args, self.gcx);
        let definition = self.gcx.predicates_of(id);
        // for (constraint, span) in definition.constraints.iter() {
        //     let dup = utils::substitute_constraint(*constraint, &subst, self.gcx);
        //     self.constraints.push((dup, *span));
        // }
    }

    pub fn add_constraint(&mut self, constraint: Constraint<'ctx>, node: NodeID, span: Span) {
        let data = CollectedConstraint {
            constraint,
            span,
            node,
        };
        self.constraints.push(data);
    }

    pub fn take_constraints(&mut self) -> Vec<CollectedConstraint<'ctx>> {
        std::mem::take(&mut self.constraints)
    }

    pub fn set_constraints(&mut self, c: Vec<CollectedConstraint<'ctx>>) {
        self.constraints = c
    }

    pub fn add_adjustments(&mut self, items: Vec<Adjustment>, id: NodeID) {
        for adjustment in items {
            self.adjustments.push((adjustment, id));
        }
    }
}

impl<'ctx> InferenceContext<'ctx> {
    /// Create a fresh general type variable
    pub fn fresh_ty_var(&mut self) -> Ty<'ctx> {
        let vid = self.tyvar_bindings.push(VarBinding {
            parent: None,
            bound_ty: None,
        });
        let kind = TyKind::Infer(InferTy::TyVar(vid));
        self.gcx.store.interners.intern_ty(kind)
    }

    /// Create a fresh integer‐literal variable
    pub fn fresh_int_var(&mut self) -> Ty<'ctx> {
        let vid = self.intvar_bindings.push(VarBinding {
            parent: None,
            bound_ty: None,
        });
        let kind = TyKind::Infer(InferTy::IntVar(vid));
        self.gcx.store.interners.intern_ty(kind)
    }

    /// Create a fresh float‐literal variable
    pub fn fresh_float_var(&mut self) -> Ty<'ctx> {
        let vid = self.floatvar_bindings.push(VarBinding {
            parent: None,
            bound_ty: None,
        });
        let kind = TyKind::Infer(InferTy::FloatVar(vid));
        self.gcx.store.interners.intern_ty(kind)
    }

    pub fn fresh_nil_var(&mut self) -> Ty<'ctx> {
        let vid = self.nilvar_bindings.push(VarBinding {
            parent: None,
            bound_ty: None,
        });
        let kind = TyKind::Infer(InferTy::NilVar(vid));
        self.gcx.store.interners.intern_ty(kind)
    }
}

impl<'ctx> InferenceContext<'ctx> {
    pub fn find_intvar(&mut self, var: IntVid) -> IntVid {
        if let Some(parent) = self.intvar_bindings[var].parent {
            let root = self.find_intvar(parent);
            self.intvar_bindings[var].parent = Some(root);
            root
        } else {
            var
        }
    }

    pub fn find_tyvar(&mut self, var: TyVid) -> TyVid {
        if let Some(parent) = self.tyvar_bindings[var].parent {
            let root = self.find_tyvar(parent);
            self.tyvar_bindings[var].parent = Some(root);
            root
        } else {
            var
        }
    }

    pub fn find_floatvar(&mut self, var: FloatVid) -> FloatVid {
        if let Some(parent) = self.floatvar_bindings[var].parent {
            let root = self.find_floatvar(parent);
            self.floatvar_bindings[var].parent = Some(root);
            root
        } else {
            var
        }
    }

    pub fn find_nilvar(&mut self, var: NilVid) -> NilVid {
        if let Some(parent) = self.nilvar_bindings[var].parent {
            let root = self.find_nilvar(parent);
            self.nilvar_bindings[var].parent = Some(root);
            root
        } else {
            var
        }
    }

    pub fn get_bound_int(&mut self, root: IntVid) -> Option<Ty<'ctx>> {
        self.intvar_bindings[root].bound_ty
    }

    pub fn snapshot(&mut self) -> ContextSnapshot<'ctx> {
        ContextSnapshot {
            constraints: std::mem::take(&mut self.constraints),
            adjustments: std::mem::take(&mut self.adjustments),
            intvar_bindings: std::mem::take(&mut self.intvar_bindings),
            tyvar_bindings: std::mem::take(&mut self.tyvar_bindings),
            floatvar_bindings: std::mem::take(&mut self.floatvar_bindings),
            nilvar_bindings: std::mem::take(&mut self.nilvar_bindings),
        }
    }
    pub fn restore(&mut self, snapshot: ContextSnapshot<'ctx>) {
        self.constraints = snapshot.constraints;
        self.adjustments = snapshot.adjustments;
        self.intvar_bindings = snapshot.intvar_bindings;
        self.tyvar_bindings = snapshot.tyvar_bindings;
        self.floatvar_bindings = snapshot.floatvar_bindings;
        self.nilvar_bindings = snapshot.nilvar_bindings;
    }
}
pub struct ContextSnapshot<'ctx> {
    constraints: Vec<CollectedConstraint<'ctx>>,
    adjustments: Vec<(Adjustment, NodeID)>,
    pub intvar_bindings: IndexVec<IntVid, VarBinding<'ctx, IntVid>>,
    pub tyvar_bindings: IndexVec<TyVid, VarBinding<'ctx, TyVid>>,
    pub floatvar_bindings: IndexVec<FloatVid, VarBinding<'ctx, FloatVid>>,
    pub nilvar_bindings: IndexVec<NilVid, VarBinding<'ctx, NilVid>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnificationError {
    /// Tried to bind a TyVar to a type that already contains that TyVar.
    OccursCheckFailed,
    /// Everything else: two concrete primitives that differ, etc.
    TypeMismatch,
}
