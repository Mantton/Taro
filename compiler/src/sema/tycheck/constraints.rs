use crate::{
    compile::context::GlobalContext,
    sema::{
        impl_engine::ref_ops::collect_interface_with_superfaces,
        models::{Constraint, InterfaceReference, Ty, TyKind},
        resolve::models::DefinitionID,
        tycheck::utils::normalize_aliases,
    },
    span::Spanned,
};
use petgraph::unionfind::UnionFind;
use rustc_hash::{FxHashMap, FxHashSet};

type Slot = usize;
type ConstraintId = usize;

#[derive(Debug)]
struct Conflict {
    lhs: ConstraintId,
    rhs: ConstraintId,
}

struct UFState<'ctx> {
    gcx: GlobalContext<'ctx>,
    uf: UnionFind<Slot>,
    bounds: Vec<FxHashSet<InterfaceReference<'ctx>>>,
    conflicts: Vec<Conflict>,
    kept: FxHashSet<ConstraintId>,
    ty2slot: FxHashMap<Ty<'ctx>, Slot>,
}

pub fn canonical_constraints_of<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: DefinitionID,
) -> Vec<Spanned<Constraint<'ctx>>> {
    if let Some(cached) = gcx.with_type_database(id.package(), |db| {
        db.def_to_canon_constraints.get(&id).cloned()
    }) {
        return cached;
    }

    let mut constraints = gcx.constraints_of(id);
    if let Some(parent) = gcx.definition_parent(id) {
        constraints.extend(canonical_constraints_of(gcx, parent));
    }

    let normalized = normalize_constraints(gcx, &constraints);
    gcx.cache_canonical_constraints(id, normalized.clone());
    normalized
}

fn normalize_constraints<'ctx>(
    gcx: GlobalContext<'ctx>,
    constraints: &[Spanned<Constraint<'ctx>>],
) -> Vec<Spanned<Constraint<'ctx>>> {
    let constraints = constraints
        .iter()
        .map(|c| {
            let normalized = normalize_aliases(gcx, c.value);
            Spanned::new(normalized, c.span)
        })
        .collect::<Vec<_>>();

    let mut state = build(gcx, &constraints);
    saturate(&mut state, &constraints);
    analyze_and_prune(&mut state, &constraints)
}

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

fn build<'ctx>(
    gcx: GlobalContext<'ctx>,
    constraints: &[Spanned<Constraint<'ctx>>],
) -> UFState<'ctx> {
    let ty2slot = collect_slots(constraints);
    let class_count = ty2slot.len().max(1);
    let uf: UnionFind<usize> = UnionFind::new(class_count);

    UFState {
        uf,
        conflicts: Vec::new(),
        kept: FxHashSet::default(),
        bounds: vec![FxHashSet::default(); class_count],
        ty2slot,
        gcx,
    }
}

fn saturate<'ctx>(state: &mut UFState<'ctx>, constraints: &[Spanned<Constraint<'ctx>>]) {
    let class_count = state.ty2slot.len().max(1);
    let mut concrete = vec![None; class_count];
    let mut concrete_src = vec![None; class_count];

    for (cid, c) in constraints.iter().enumerate() {
        match c.value {
            Constraint::TypeEquality(lhs, rhs) => {
                let sl = state.ty2slot[&lhs];
                let sr = state.ty2slot[&rhs];

                let mut rl = state.uf.find(sl);
                let mut rr = state.uf.find(sr);

                if is_concrete(lhs) && concrete[rl].is_none() {
                    concrete[rl] = Some(lhs);
                    concrete_src[rl] = Some(cid);
                }
                if is_concrete(rhs) && concrete[rr].is_none() {
                    concrete[rr] = Some(rhs);
                    concrete_src[rr] = Some(cid);
                }

                rl = state.uf.find(sl);
                rr = state.uf.find(sr);
                if rl == rr {
                    continue;
                }

                if let (Some(tl), Some(tr)) = (concrete[rl], concrete[rr]) {
                    if tl != tr {
                        state.conflicts.push(Conflict {
                            lhs: concrete_src[rl].unwrap(),
                            rhs: concrete_src[rr].unwrap(),
                        });
                    }
                }

                state.uf.union(rl, rr);

                let root = state.uf.find(rl);
                let child = if root == rl { rr } else { rl };

                if concrete[root].is_none() && concrete[child].is_some() {
                    concrete[root] = concrete[child];
                    concrete_src[root] = concrete_src[child];
                }

                let (keep, move_from) = if state.bounds[root].len() >= state.bounds[child].len() {
                    (root, child)
                } else {
                    (child, root)
                };
                let moved: FxHashSet<InterfaceReference<'ctx>> =
                    std::mem::take(&mut state.bounds[move_from]);
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

fn analyze_and_prune<'ctx>(
    state: &mut UFState<'ctx>,
    constraints: &[Spanned<Constraint<'ctx>>],
) -> Vec<Spanned<Constraint<'ctx>>> {
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

    for r in redundancies.into_iter() {
        let c = constraints[r];
        let message = match c.value {
            Constraint::TypeEquality(lhs, rhs) => format!(
                "redundant constraint '{} == {}'",
                lhs.format(state.gcx),
                rhs.format(state.gcx)
            ),
            Constraint::Bound { ty, interface } => format!(
                "redundant constraint '{}: {}'",
                ty.format(state.gcx),
                interface.format(state.gcx)
            ),
        };
        state.gcx.dcx().emit_warning(message, Some(c.span));
    }

    for conf in &state.conflicts {
        let c1 = match constraints[conf.lhs].value {
            Constraint::TypeEquality(lhs, rhs) => {
                format!("{} == {}", lhs.format(state.gcx), rhs.format(state.gcx))
            }
            Constraint::Bound { ty, interface } => {
                format!("{}: {}", ty.format(state.gcx), interface.format(state.gcx))
            }
        };
        let c2 = match constraints[conf.rhs].value {
            Constraint::TypeEquality(lhs, rhs) => {
                format!("{} == {}", lhs.format(state.gcx), rhs.format(state.gcx))
            }
            Constraint::Bound { ty, interface } => {
                format!("{}: {}", ty.format(state.gcx), interface.format(state.gcx))
            }
        };
        let message = format!(
            "cannot satisfy constraints '{}' & '{}' simultaneously",
            c1, c2
        );
        state
            .gcx
            .dcx()
            .emit_error(message, Some(constraints[conf.lhs].span));
    }

    constraints
        .iter()
        .enumerate()
        .filter_map(|(cid, c)| {
            if state.kept.contains(&cid) {
                Some(*c)
            } else {
                None
            }
        })
        .collect()
}

fn insert_with_closure<'ctx>(
    set: &mut FxHashSet<InterfaceReference<'ctx>>,
    iface: InterfaceReference<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> bool {
    let mut changed = false;
    for iface in collect_interface_with_superfaces(gcx, iface) {
        if set.insert(iface) {
            changed = true;
        }
    }
    changed
}

fn is_concrete(ty: Ty<'_>) -> bool {
    !matches!(
        ty.kind(),
        TyKind::Parameter(_) | TyKind::Infer(_) | TyKind::Alias { .. } | TyKind::Error
    )
}
