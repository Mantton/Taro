use crate::{
    GlobalContext,
    check::context::func::FnCtx,
    check::solver::{Goal, Obligation},
    lower::{LoweringRequest, TypeLowerer},
    ty::{GenericArgument, Ty, TyKind},
    utils::instantiate_constraint_with_args,
};
use rustc_hash::FxHashSet;
use taroc_hir::{DefinitionID, OperatorKind, Resolution};
use taroc_span::{FileID, Identifier, Span};

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn resolve_qualified_method_call(
        &self,
        method: Identifier,
        self_ty: Ty<'ctx>,
    ) -> Result<Resolution, ()> {
        let gcx = self.gcx;

        // Probe for associated function
        let candidates = associated_functions_for_ty(method, self_ty, gcx);
        if candidates.is_empty() {
            return Err(());
        }

        if let [candidate] = candidates.as_slice() {
            return Ok(Resolution::Definition(*candidate, gcx.def_kind(*candidate)));
        }

        let set: FxHashSet<_> = candidates.into_iter().collect();
        return Ok(Resolution::FunctionSet(set));
    }
}

pub fn associated_functions_for_ty<'ctx>(
    method: Identifier,
    self_ty: Ty<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> Vec<DefinitionID> {
    let file = method.span.file;
    let packages = gcx.packages_at_file(file);
    let simple_ty = self_ty.to_simple_type();
    let mut candidates = vec![];
    for package in packages {
        gcx.with_type_database(package, |db| {
            let Some(index) = db.function_table.methods.get(&simple_ty) else {
                return;
            };
            let Some(set) = index.functions.get(&method.symbol) else {
                return;
            };
            candidates.extend(set.members.iter().copied());
        });
    }

    candidates
}

pub fn associated_operators_for_ty<'ctx>(
    op: OperatorKind,
    self_ty: Ty<'ctx>,
    gcx: GlobalContext<'ctx>,
    file: FileID,
) -> Vec<DefinitionID> {
    let packages = gcx.packages_at_file(file);

    let simple_ty = gcx.try_simple_type(self_ty);
    let Some(simple_ty) = simple_ty else {
        return vec![];
    };
    let mut candidates = vec![];
    for package in packages {
        gcx.with_type_database(package, |db| {
            let Some(index) = db.function_table.methods.get(&simple_ty) else {
                return;
            };
            let Some(set) = index.operators.get(&op) else {
                return;
            };
            candidates.extend(set.members.iter().copied());
        });
    }

    candidates
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn lower_ty(&self, ast_ty: &taroc_hir::Type) -> Ty<'ctx> {
        let ty = self
            .lowerer()
            .lower_type(ast_ty, &LoweringRequest::default());

        // Add well‑formedness obligations for any instantiated generics
        self.add_well_formed_obligations_for_type(ty, ast_ty.span);
        ty
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn add_well_formed_obligations_for_type(&self, ty: Ty<'ctx>, location: Span) {
        // Recurse through the type, and for any ADT or function definition
        // with generic arguments, instantiate its canonical predicates and
        // add them as obligations at this location.
        self.recurse_wf(ty, location);
    }

    fn recurse_wf(&self, ty: Ty<'ctx>, location: Span) {
        let gcx = self.gcx;
        match ty.kind() {
            TyKind::Adt(def, args) => {
                // 1) Enforce the ADT’s own canonical predicates with these args
                let preds = gcx.canon_predicates_of(def.id);
                for sp in preds.iter() {
                    let instantiated = instantiate_constraint_with_args(gcx, sp.value, args);
                    self.add_obligation(Obligation {
                        location,
                        goal: Goal::Constraint(instantiated),
                    });
                }

                // 2) Recurse into type arguments
                for ga in args.iter() {
                    if let GenericArgument::Type(arg_ty) = *ga {
                        self.recurse_wf(arg_ty, location);
                    }
                }
            }
            TyKind::FnDef(_id, args) => {
                // Function definitions can also have predicates; enforce them.
                // We treat them similarly to ADTs if used as types.
                if let Some(def_id) = gcx.ty_to_def(ty) {
                    let preds = gcx.canon_predicates_of(def_id);
                    for sp in preds.iter() {
                        let instantiated = instantiate_constraint_with_args(gcx, sp.value, args);
                        self.add_obligation(Obligation {
                            location,
                            goal: Goal::Constraint(instantiated),
                        });
                    }
                }
                for ga in args.iter() {
                    if let GenericArgument::Type(arg_ty) = *ga {
                        self.recurse_wf(arg_ty, location);
                    }
                }
            }
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                self.recurse_wf(inner, location);
            }
            TyKind::Array(elem, _) => {
                self.recurse_wf(elem, location);
            }
            TyKind::Tuple(elems) => {
                for &e in elems.iter() {
                    self.recurse_wf(e, location);
                }
            }
            TyKind::Function { inputs, output } => {
                for &i in inputs.iter() {
                    self.recurse_wf(i, location);
                }
                self.recurse_wf(output, location);
            }
            // Associated types, existentials, parameters, primitives, etc.:
            // no direct well‑formed checks to add here.
            _ => {}
        }
    }
}
