//! Shared evaluator for compiler-produced GC layout graphs.

use std::collections::HashSet;

pub(crate) const GC_LAYOUT_POINTER: u8 = 1;
pub(crate) const GC_LAYOUT_REFERENCE: u8 = 2;
pub(crate) const GC_LAYOUT_AGGREGATE: u8 = 3;
pub(crate) const GC_LAYOUT_REPEAT: u8 = 4;
pub(crate) const GC_LAYOUT_TAGGED: u8 = 5;

const MAX_LAYOUT_DEPTH: usize = 64;
const MAX_LAYOUT_VISITS: usize = 1 << 20;

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GcLayoutNode {
    pub offset: u64,
    pub stride: u64,
    pub first_child: u32,
    pub child_count: u32,
    pub kind: u8,
    pub width: u8,
    pub reserved: [u8; 6],
}

unsafe impl Send for GcLayoutNode {}
unsafe impl Sync for GcLayoutNode {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TraceMode {
    /// References are emitted as managed candidates and their targets are
    /// scanned later using the target allocation's descriptor.
    Heap,
    /// References may point into another stack object, so follow their typed
    /// child graph in addition to emitting the reference itself.
    Stack,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LayoutError {
    InvalidNode {
        index: usize,
        reason: &'static str,
    },
    InvalidTag {
        address: usize,
        tag: u64,
        variants: u32,
    },
    LimitExceeded,
}

impl std::fmt::Display for LayoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidNode { index, reason } => {
                write!(f, "GC layout node {index} is invalid: {reason}")
            }
            Self::InvalidTag {
                address,
                tag,
                variants,
            } => write!(
                f,
                "invalid live enum tag {tag} at {address:#x} (descriptor has {variants} variants)"
            ),
            Self::LimitExceeded => write!(f, "GC layout traversal exceeded its safety limit"),
        }
    }
}

const INLINE_VISITED_CAPACITY: usize = 16;

/// Most root layouts are small. Avoid a heap allocation for each of them while
/// retaining hash-set lookup for large arrays and recursive reference graphs.
#[derive(Default)]
struct Visited {
    inline: [(usize, usize); INLINE_VISITED_CAPACITY],
    len: usize,
    overflow: Option<HashSet<(usize, usize)>>,
}

impl Visited {
    fn insert(&mut self, key: (usize, usize)) -> bool {
        if let Some(overflow) = &mut self.overflow {
            return overflow.insert(key);
        }
        if self.inline[..self.len].contains(&key) {
            return false;
        }
        if self.len < INLINE_VISITED_CAPACITY {
            self.inline[self.len] = key;
            self.len += 1;
        } else {
            let mut overflow = HashSet::with_capacity(INLINE_VISITED_CAPACITY * 2);
            overflow.extend(self.inline);
            overflow.insert(key);
            self.overflow = Some(overflow);
        }
        true
    }
}

struct Evaluator<'a, F> {
    nodes: &'a [GcLayoutNode],
    mode: TraceMode,
    emit: F,
    visited: Visited,
    visits: usize,
}

impl<F: FnMut(*const u8)> Evaluator<'_, F> {
    unsafe fn visit(
        &mut self,
        index: usize,
        base: usize,
        limit: usize,
        depth: usize,
    ) -> Result<(), LayoutError> {
        if depth > MAX_LAYOUT_DEPTH || self.visits >= MAX_LAYOUT_VISITS {
            return Err(LayoutError::LimitExceeded);
        }
        if !self.visited.insert((base, index)) {
            return Ok(());
        }
        self.visits += 1;
        let node = *self.nodes.get(index).ok_or(LayoutError::InvalidNode {
            index,
            reason: "index is out of bounds",
        })?;
        let offset = usize::try_from(node.offset).map_err(|_| LayoutError::InvalidNode {
            index,
            reason: "offset exceeds address width",
        })?;
        let node_base = base.checked_add(offset).ok_or(LayoutError::InvalidNode {
            index,
            reason: "address overflow",
        })?;
        let remaining = limit.saturating_sub(offset);

        match node.kind {
            GC_LAYOUT_POINTER | GC_LAYOUT_REFERENCE => {
                if remaining < std::mem::size_of::<usize>() {
                    return Ok(());
                }
                let candidate = unsafe { std::ptr::read_unaligned(node_base as *const usize) };
                if candidate == 0 {
                    return Ok(());
                }
                (self.emit)(candidate as *const u8);
                if node.kind == GC_LAYOUT_REFERENCE
                    && self.mode == TraceMode::Stack
                    && node.child_count != 0
                {
                    unsafe {
                        self.visit(node.first_child as usize, candidate, usize::MAX, depth + 1)?
                    };
                }
            }
            GC_LAYOUT_AGGREGATE => {
                let end = node.first_child.checked_add(node.child_count).ok_or(
                    LayoutError::InvalidNode {
                        index,
                        reason: "child range overflow",
                    },
                )?;
                for child in node.first_child..end {
                    unsafe { self.visit(child as usize, node_base, remaining, depth + 1)? };
                }
            }
            GC_LAYOUT_REPEAT => {
                if node.child_count != 0 && node.first_child as usize >= self.nodes.len() {
                    return Err(LayoutError::InvalidNode {
                        index,
                        reason: "repeat child is out of bounds",
                    });
                }
                let stride =
                    usize::try_from(node.stride).map_err(|_| LayoutError::InvalidNode {
                        index,
                        reason: "stride exceeds address width",
                    })?;
                for element in 0..node.child_count as usize {
                    let element_offset =
                        element
                            .checked_mul(stride)
                            .ok_or(LayoutError::InvalidNode {
                                index,
                                reason: "repeat offset overflow",
                            })?;
                    if element_offset >= remaining {
                        break;
                    }
                    unsafe {
                        self.visit(
                            node.first_child as usize,
                            node_base + element_offset,
                            remaining - element_offset,
                            depth + 1,
                        )?
                    };
                }
            }
            GC_LAYOUT_TAGGED => {
                let tag = match node.width {
                    1 if remaining >= 1 => unsafe {
                        std::ptr::read_unaligned(node_base as *const u8) as u64
                    },
                    2 if remaining >= 2 => unsafe {
                        std::ptr::read_unaligned(node_base as *const u16) as u64
                    },
                    4 if remaining >= 4 => unsafe {
                        std::ptr::read_unaligned(node_base as *const u32) as u64
                    },
                    8 if remaining >= 8 => unsafe {
                        std::ptr::read_unaligned(node_base as *const u64)
                    },
                    1 | 2 | 4 | 8 => return Ok(()),
                    _ => {
                        return Err(LayoutError::InvalidNode {
                            index,
                            reason: "tag width is not 1, 2, 4, or 8",
                        });
                    }
                };
                if tag >= u64::from(node.child_count) {
                    return Err(LayoutError::InvalidTag {
                        address: node_base,
                        tag,
                        variants: node.child_count,
                    });
                }
                unsafe {
                    self.visit(
                        node.first_child as usize + tag as usize,
                        node_base,
                        remaining,
                        depth + 1,
                    )?
                };
            }
            _ => {
                return Err(LayoutError::InvalidNode {
                    index,
                    reason: "unknown node kind",
                });
            }
        }
        Ok(())
    }
}

pub(crate) unsafe fn trace_layout(
    base: *const u8,
    nodes: &[GcLayoutNode],
    limit: usize,
    mode: TraceMode,
    emit: impl FnMut(*const u8),
) -> Result<(), LayoutError> {
    if base.is_null() || nodes.is_empty() {
        return Ok(());
    }
    let mut evaluator = Evaluator {
        nodes,
        mode,
        emit,
        visited: Visited::default(),
        visits: 0,
    };
    unsafe { evaluator.visit(0, base as usize, limit, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn visited_preserves_both_key_components_across_overflow() {
        let mut visited = Visited::default();
        let mut expected = HashSet::new();
        // Include zero, equal addresses with different nodes, and equal nodes
        // with different addresses. Revisit old keys after spilling, too.
        for key in (0..(INLINE_VISITED_CAPACITY / 4 + 2))
            .flat_map(|base| (0..4).map(move |node| (base, node)))
        {
            assert_eq!(visited.insert(key), expected.insert(key));
            if expected.len() <= INLINE_VISITED_CAPACITY {
                assert!(visited.overflow.is_none());
            } else {
                assert!(visited.overflow.is_some());
            }
            for old in &expected {
                assert!(!visited.insert(*old));
            }
        }
    }

    #[test]
    fn recursive_reference_cycle_survives_visited_overflow() {
        let nodes = [
            node(0, 0, 1, 2, GC_LAYOUT_AGGREGATE, 0),
            node(0, 0, 0, 1, GC_LAYOUT_REFERENCE, 0),
            node(8, 0, 0, 0, GC_LAYOUT_POINTER, 0),
        ];
        let payloads = [0_u64; 24];
        let mut values: Vec<_> = payloads
            .iter()
            .map(|payload| RecursiveValue {
                next: std::ptr::null(),
                payload,
            })
            .collect();
        for index in 0..values.len() {
            values[index].next = &values[(index + 1) % values.len()];
        }
        let mut roots = Vec::new();
        unsafe {
            trace_layout(
                values.as_ptr().cast(),
                &nodes,
                std::mem::size_of::<RecursiveValue>(),
                TraceMode::Stack,
                |root| roots.push(root),
            )
            .unwrap();
        }
        assert_eq!(roots.len(), values.len() * 2);
        for value in &values {
            assert!(roots.contains(&(value as *const RecursiveValue).cast()));
            assert!(roots.contains(&value.payload.cast()));
        }
    }

    const fn node(
        offset: u64,
        stride: u64,
        first_child: u32,
        child_count: u32,
        kind: u8,
        width: u8,
    ) -> GcLayoutNode {
        GcLayoutNode {
            offset,
            stride,
            first_child,
            child_count,
            kind,
            width,
            reserved: [0; 6],
        }
    }

    #[test]
    fn tagged_layout_visits_only_the_active_variant() {
        let nodes = [
            node(0, 0, 1, 2, GC_LAYOUT_TAGGED, 1),
            node(0, 0, 0, 0, GC_LAYOUT_AGGREGATE, 0),
            node(0, 0, 3, 1, GC_LAYOUT_AGGREGATE, 0),
            node(8, 0, 0, 0, GC_LAYOUT_POINTER, 0),
        ];
        let candidate = Box::new(17_u64);
        let mut storage = [0usize; 2];
        storage[1] = (&*candidate as *const u64) as usize;

        let mut roots = Vec::new();
        unsafe {
            trace_layout(
                storage.as_ptr().cast(),
                &nodes,
                std::mem::size_of_val(&storage),
                TraceMode::Heap,
                |root| roots.push(root),
            )
            .unwrap();
        }
        assert!(roots.is_empty(), "inactive payload must not be traced");

        storage[0] = 1;
        unsafe {
            trace_layout(
                storage.as_ptr().cast(),
                &nodes,
                std::mem::size_of_val(&storage),
                TraceMode::Heap,
                |root| roots.push(root),
            )
            .unwrap();
        }
        assert_eq!(roots, vec![(&*candidate as *const u64).cast::<u8>()]);
    }

    #[test]
    fn repeat_layout_uses_the_declared_stride_and_count() {
        let nodes = [
            node(0, 8, 1, 3, GC_LAYOUT_REPEAT, 0),
            node(0, 0, 0, 0, GC_LAYOUT_POINTER, 0),
        ];
        let values = [Box::new(1_u64), Box::new(2_u64), Box::new(3_u64)];
        let storage = [
            (&*values[0] as *const u64) as usize,
            (&*values[1] as *const u64) as usize,
            (&*values[2] as *const u64) as usize,
        ];
        let mut roots = Vec::new();
        unsafe {
            trace_layout(
                storage.as_ptr().cast(),
                &nodes,
                std::mem::size_of_val(&storage),
                TraceMode::Heap,
                |root| roots.push(root),
            )
            .unwrap();
        }
        assert_eq!(roots.len(), 3);
    }

    #[repr(C)]
    struct RecursiveValue {
        next: *const RecursiveValue,
        payload: *const u64,
    }

    #[test]
    fn recursive_reference_graphs_terminate_without_losing_inner_roots() {
        let nodes = [
            node(0, 0, 1, 2, GC_LAYOUT_AGGREGATE, 0),
            node(0, 0, 0, 1, GC_LAYOUT_REFERENCE, 0),
            node(8, 0, 0, 0, GC_LAYOUT_POINTER, 0),
        ];
        let first_payload = Box::new(1_u64);
        let second_payload = Box::new(2_u64);
        let mut first = RecursiveValue {
            next: std::ptr::null(),
            payload: &*first_payload,
        };
        let mut second = RecursiveValue {
            next: std::ptr::null(),
            payload: &*second_payload,
        };
        first.next = &second;
        second.next = &first;

        let mut roots = Vec::new();
        unsafe {
            trace_layout(
                (&first as *const RecursiveValue).cast(),
                &nodes,
                std::mem::size_of::<RecursiveValue>(),
                TraceMode::Stack,
                |root| roots.push(root),
            )
            .unwrap();
        }
        assert!(roots.contains(&(&second as *const RecursiveValue).cast()));
        assert!(roots.contains(&(&first as *const RecursiveValue).cast()));
        assert!(roots.contains(&(&*first_payload as *const u64).cast()));
        assert!(roots.contains(&(&*second_payload as *const u64).cast()));
    }

    #[test]
    fn invalid_live_tag_reports_its_value_and_address() {
        let nodes = [
            node(0, 0, 1, 1, GC_LAYOUT_TAGGED, 1),
            node(0, 0, 0, 0, GC_LAYOUT_AGGREGATE, 0),
        ];
        let storage = [9_u8];
        let error = unsafe {
            trace_layout(
                storage.as_ptr(),
                &nodes,
                storage.len(),
                TraceMode::Heap,
                |_| {},
            )
            .unwrap_err()
        };
        assert_eq!(
            error,
            LayoutError::InvalidTag {
                address: storage.as_ptr() as usize,
                tag: 9,
                variants: 1,
            }
        );
    }
}
