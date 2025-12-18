use super::{
    Adjustment, BindOverloadGoalData, ConstraintSolver, DisjunctionBranch, Goal, MemberGoalData,
    Obligation, SolverResult,
};
use crate::{
    hir::NodeID,
    sema::{
        error::TypeError,
        models::{Ty, TyKind},
        resolve::models::{DefinitionID, DefinitionKind, PrimaryType, TypeHead},
        tycheck::utils::autoderef::Autoderef,
    },
    span::{Spanned, Symbol},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_member(&mut self, data: MemberGoalData<'ctx>) -> SolverResult<'ctx> {
        let MemberGoalData {
            node_id,
            receiver_node,
            receiver,
            name,
            result,
            span,
        } = data;

        let mut adjustments = Vec::new();
        let mut prev: Option<Ty<'ctx>> = None;
        for ty in self.autoderef(receiver) {
            let ty = self.structurally_resolve(ty);
            if let Some(_) = prev {
                adjustments.push(Adjustment::Dereference);
            }
            prev = Some(ty);

            // Field lookup (structs only for now).
            if let Some((field_ty, index)) = self.lookup_field_ty(ty, name.symbol) {
                self.record_adjustments(receiver_node, adjustments);
                self.record_field_index(node_id, index);
                return self.solve_equality(span, result, field_ty);
            }

            // Instance methods.
            let candidates = self.lookup_instance_candidates(ty, name.symbol);
            if !candidates.is_empty() {
                self.record_adjustments(receiver_node, adjustments);
                let mut branches = Vec::with_capacity(candidates.len());
                for candidate in candidates {
                    let candidate_ty = self.gcx().get_type(candidate);
                    branches.push(DisjunctionBranch {
                        goal: Goal::BindOverload(BindOverloadGoalData {
                            node_id,
                            var_ty: result,
                            candidate_ty,
                            source: candidate,
                        }),
                        source: Some(candidate),
                    });
                }
                return SolverResult::Solved(vec![Obligation {
                    location: span,
                    goal: Goal::Disjunction(branches),
                }]);
            }
        }

        // Nothing matched; use last seen type for diagnostics.
        let final_ty = prev.unwrap_or_else(|| self.structurally_resolve(receiver));
        let error = Spanned::new(
            TypeError::NoSuchMember {
                name: name.symbol,
                on: final_ty,
            },
            span,
        );
        SolverResult::Error(vec![error])
    }

    pub fn autoderef(&self, base: Ty<'ctx>) -> Autoderef<'ctx> {
        Autoderef::new(&self.icx, base)
    }

    pub fn record_adjustments(&mut self, node_id: NodeID, adjustments: Vec<Adjustment<'ctx>>) {
        if adjustments.is_empty() {
            return;
        }
        self.adjustments.insert(node_id, adjustments);
    }

    fn lookup_field_ty(&self, ty: Ty<'ctx>, name: Symbol) -> Option<(Ty<'ctx>, usize)> {
        let TyKind::Adt(def) = ty.kind() else {
            return None;
        };

        if self.gcx().definition_kind(def.id) != DefinitionKind::Struct {
            return None;
        }

        let struct_def = self.gcx().get_struct_definition(def.id);
        for (idx, field) in struct_def.fields.iter().enumerate() {
            if field.name == name {
                return Some((field.ty, idx));
            }
        }
        None
    }

    fn lookup_instance_candidates(&self, ty: Ty<'ctx>, name: Symbol) -> Vec<DefinitionID> {
        let Some(head) = self.type_head_from_type(ty) else {
            return vec![];
        };

        self.gcx().with_session_type_database(|db| {
            db.type_head_to_members
                .get(&head)
                .and_then(|idx| idx.instance_functions.get(&name))
                .map(|set| set.members.clone())
                .unwrap_or_default()
        })
    }

    pub fn type_head_from_type(&self, ty: Ty<'ctx>) -> Option<TypeHead> {
        match ty.kind() {
            TyKind::Bool => Some(TypeHead::Primary(PrimaryType::Bool)),
            TyKind::Rune => Some(TypeHead::Primary(PrimaryType::Rune)),
            TyKind::String => Some(TypeHead::Primary(PrimaryType::String)),
            TyKind::Int(k) => Some(TypeHead::Primary(PrimaryType::Int(k))),
            TyKind::UInt(k) => Some(TypeHead::Primary(PrimaryType::UInt(k))),
            TyKind::Float(k) => Some(TypeHead::Primary(PrimaryType::Float(k))),
            TyKind::Adt(def) => Some(TypeHead::Nominal(def.id)),
            TyKind::Reference(_, mutbl) => Some(TypeHead::Reference(mutbl)),
            TyKind::Pointer(_, mutbl) => Some(TypeHead::Pointer(mutbl)),
            TyKind::Tuple(items) => Some(TypeHead::Tuple(items.len() as u16)),
            TyKind::Infer(_) | TyKind::FnPointer { .. } | TyKind::Error => None,
        }
    }
}
