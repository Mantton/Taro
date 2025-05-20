use crate::GlobalContext;
use crate::ty::{Constraint, InterfaceReference, SpannedConstraints, Ty};
use crate::utils::{constraint2str, def_id_of_ty, ty_from_simple};
use petgraph::unionfind::UnionFind;
use rustc_hash::{FxHashMap, FxHashSet};
use taroc_hir::{DefinitionID, DefinitionKind};
use taroc_span::Spanned;

type Slot = usize;
type ConstraintId = usize;
#[derive(Debug)]
struct Conflict {
    lhs: ConstraintId, // constraint that fixed concrete #1
    rhs: ConstraintId, // constraint that fixed concrete #2
}

struct UFState<'ctx> {
    gcx: GlobalContext<'ctx>,
    uf: UnionFind<Slot>,                              // the Tarjan forest
    bounds: Vec<FxHashSet<InterfaceReference<'ctx>>>, // closed set
    conflicts: Vec<Conflict>,                         // buffered “Int vs String”
    kept: FxHashSet<ConstraintId>,
    ty2slot: FxHashMap<Ty<'ctx>, Slot>, // Ty  → dense index
}

pub fn canon_predicates_of<'ctx>(
    id: DefinitionID,
    gcx: GlobalContext<'ctx>,
) -> SpannedConstraints<'ctx> {
    normalize(id, gcx)
}

fn normalize<'ctx>(id: DefinitionID, gcx: GlobalContext<'ctx>) -> SpannedConstraints<'ctx> {
    let predicates = gcx.predicates_of(id);
    let mut state = build(gcx, predicates);
    seed_parent(&mut state, id);
    saturate(&mut state, predicates);

    let result = analyse_and_prune(&mut state, predicates);
    return result;
}

/*─────────────────────────────────────────────────────────────────────*
 * 2.  PASS 0 – collect every Ty term and give it a slot idx          *
 *─────────────────────────────────────────────────────────────────────*/
fn collect_slots<'ctx>(constraints: &[Spanned<Constraint<'ctx>>]) -> FxHashMap<Ty<'ctx>, Slot> {
    let mut map: FxHashMap<Ty<'ctx>, Slot> = FxHashMap::default();
    let mut next_slot: usize = 0;
    let mut intern = |t: Ty<'ctx>| -> usize {
        *map.entry(t).or_insert_with(|| {
            let s = next_slot;
            next_slot += 1;
            s
        })
    };

    for c in constraints {
        match c.value {
            Constraint::TypeEquality(a, b) => {
                intern(a);
                intern(b);
            }
            Constraint::Bound { ty, .. } => {
                intern(ty);
            }
        }
    }

    map
}

/*─────────────────────────────────────────────────────────────────────*
 * 3.  PASS 1 – build & saturate (hot α(n) loop, borrow‑safe)         *
 *─────────────────────────────────────────────────────────────────────*/
fn build<'ctx>(
    gcx: GlobalContext<'ctx>,
    constraints: &[Spanned<Constraint<'ctx>>],
) -> UFState<'ctx> {
    /* allocate a dense slot for every Ty the first time we meet it */
    let ty2slot = collect_slots(constraints);
    let class_count = ty2slot.len().max(1);
    /* Allocate UF and side arrays once, with fixed length */
    let uf: UnionFind<usize> = UnionFind::new(class_count);

    let conflicts = Vec::<Conflict>::new();
    let kept = FxHashSet::default();
    let bounds = vec![FxHashSet::default(); class_count];
    UFState {
        uf,
        conflicts,
        ty2slot,
        gcx,
        kept,
        bounds,
    }
}

fn saturate<'ctx>(state: &mut UFState<'ctx>, constraints: &[Spanned<Constraint<'ctx>>]) {
    let class_count = state.ty2slot.len().max(1); // avoid zero‑len Vecs

    let mut concrete = vec![None; class_count];
    let mut concrete_src = vec![None; class_count];
    /* Single streaming pass over every constraint */
    for (cid, c) in constraints.iter().enumerate() {
        match c.value {
            Constraint::TypeEquality(lhs, rhs) => {
                /* map Ty → slot (safe, map is immutable) */
                let sl = state.ty2slot[&lhs];
                let sr = state.ty2slot[&rhs];

                /* reps before union (path compression) */
                let mut rl = state.uf.find(sl);
                let mut rr = state.uf.find(sr);

                /* attach concrete witness for EACH side if we haven't yet */
                if lhs.is_concrete() && concrete[rl].is_none() {
                    concrete[rl] = Some(lhs);
                    concrete_src[rl] = Some(cid);
                }
                if rhs.is_concrete() && concrete[rr].is_none() {
                    concrete[rr] = Some(rhs);
                    concrete_src[rr] = Some(cid);
                }

                /* refresh reps (no harm; very cheap) */
                rl = state.uf.find(sl);
                rr = state.uf.find(sr);

                /* if already same class, nothing left to do */
                if rl == rr {
                    continue;
                }

                /* if both reps now concrete and DIFFER, buffer conflict */
                if let (Some(tl), Some(tr)) = (concrete[rl], concrete[rr]) {
                    if tl.kind() != tr.kind() {
                        state.conflicts.push(Conflict {
                            lhs: concrete_src[rl].unwrap(),
                            rhs: concrete_src[rr].unwrap(),
                        });
                    }
                }

                /* union‑by‑rank merges the two classes */
                state.uf.union(rl, rr);

                /* root/child after union */
                let root = state.uf.find(rl);
                let child = if root == rl { rr } else { rl };

                /* propagate witness if root lacked one */
                if concrete[root].is_none() && concrete[child].is_some() {
                    concrete[root] = concrete[child];
                    concrete_src[root] = concrete_src[child];
                }

                // move smaller bound set into larger (log n total moves)
                //--- decide which set is smaller (optional heuristic) -----------------
                let (keep, move_from) = if state.bounds[root].len() >= state.bounds[child].len() {
                    (root, child) // drain child into root
                } else {
                    (child, root) // drain root into child, then swap slots
                };
                let moved: FxHashSet<InterfaceReference<'ctx>> =
                    std::mem::take(&mut state.bounds[move_from]); // ← leaves empty set behind
                state.bounds[keep].extend(moved.into_iter());
                if keep == child {
                    state.bounds.swap(root, child);
                }

                state.kept.insert(cid);
            }

            Constraint::Bound { ty, interface } => {
                let rep = state.uf.find(state.ty2slot[&ty]);
                if insert_with_closure(&mut state.bounds[rep], interface, state.gcx) {
                    state.kept.insert(cid);
                }
            }
        }
    }
}

fn seed_parent<'ctx>(state: &mut UFState<'ctx>, id: DefinitionID) {
    let gcx = state.gcx;
    if let DefinitionKind::Extension = gcx.def_kind(id) {
        let target = gcx.with_type_database(id.package(), |db| db.extension_ty_map[&id]);
        let parent = def_id_of_ty(gcx, ty_from_simple(gcx, target));
        if let Some(parent) = parent {
            // seed bounds from parent
            for c in gcx.canon_predicates_of(parent) {
                if let Constraint::Bound { ty, interface } = c.value {
                    let rep = state.uf.find(state.ty2slot[&ty]);
                    state.bounds[rep].insert(interface);
                }
            }
        };
    }
}
fn analyse_and_prune<'ctx>(
    state: &mut UFState<'ctx>,
    constraints: &[Spanned<Constraint<'ctx>>],
) -> SpannedConstraints<'ctx> {
    let mut redundancies = vec![];
    for (cid, c) in constraints.iter().enumerate() {
        match c.value {
            Constraint::Bound { ty, interface } => {
                let rep = state.uf.find(state.ty2slot[&ty]);
                if state.bounds[rep].contains(&interface) && !state.kept.contains(&cid) {
                    redundancies.push(cid);
                }
            }
            Constraint::TypeEquality(a, b) => {
                let sa = state.ty2slot[&a];
                let sb = state.ty2slot[&b];
                if state.uf.equiv(sa, sb) && !state.kept.contains(&cid) {
                    redundancies.push(cid);
                }
            }
        }
    }

    // println!(
    //     "Constraints ({}) - ({}) Redundant",
    //     constraints.len(),
    //     redundancies.len()
    // );
    for r in redundancies.into_iter() {
        let c = constraints[r];
        let message = format!(
            "redundant constraint '{}'",
            constraint2str(c.value, state.gcx)
        );
        state.gcx.diagnostics.warn(message, c.span);
    }

    /* print or store the buffered conflicts */
    for conf in &state.conflicts {
        let c1 = constraint2str(constraints[conf.lhs].value, state.gcx);
        let c2 = constraint2str(constraints[conf.rhs].value, state.gcx);
        let message = format!(
            "cannot satisfy constraints '{}' & '{}' simultaneously",
            c1, c2
        );
        state
            .gcx
            .diagnostics
            .error(message, constraints[conf.rhs].span);
    }

    return constraints
        .iter()
        .enumerate()
        .filter_map(|(cid, c)| {
            if state.kept.contains(&cid) {
                Some(*c)
            } else {
                None
            }
        })
        .collect();
}

fn insert_with_closure<'ctx>(
    set: &mut FxHashSet<InterfaceReference<'ctx>>,
    iface: InterfaceReference<'ctx>,
    _: GlobalContext<'ctx>,
) -> bool {
    let mut stack = vec![iface];
    let mut changed = false;
    while let Some(ir) = stack.pop() {
        if set.insert(ir) {
            changed = true;
            // for &sup in direct_supers(ir.id) {
            //     stack.push(InterfaceReference {
            //         id: sup,
            //         arguments: ir.arguments,
            //     });
            // }
        }
    }
    changed
}
