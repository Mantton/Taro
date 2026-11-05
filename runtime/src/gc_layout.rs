//! Shared evaluator for compiler-produced and runtime-built GC layout graphs.

use rustc_hash::FxHashSet;

pub(crate) const GC_LAYOUT_POINTER: u8 = 1;
pub(crate) const GC_LAYOUT_REFERENCE: u8 = 2;
pub(crate) const GC_LAYOUT_AGGREGATE: u8 = 3;
pub(crate) const GC_LAYOUT_REPEAT: u8 = 4;
pub(crate) const GC_LAYOUT_TAGGED: u8 = 5;
/// Runtime-built sequence allocation only; never emitted in compiler PC root
/// graphs. `child_count` is the header-relative initialized-count byte offset,
/// `offset` begins element storage, and `first_child` is its element graph.
pub(crate) const GC_LAYOUT_INITIALIZED_REPEAT: u8 = 6;
/// Traced like `GC_LAYOUT_POINTER`, but an unsafe raw pointer may dangle or
/// point one past its object, so heap verification skips its target.
pub(crate) const GC_LAYOUT_RAW_POINTER: u8 = 7;
/// Runtime-built dictionary group only. `child_count` locates its control word,
/// `offset` starts eight raw entry slots, and `stride` is the entry size. Each
/// logical control byte with its high bit clear publishes one initialized slot.
/// Unlike typed arrays, empty/deleted slots must never be interpreted as values.
pub(crate) const GC_LAYOUT_SWISS_GROUP: u8 = 8;

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
struct Visited {
    // Value copies build one of these each, so only `len` entries are initialized.
    inline: [std::mem::MaybeUninit<(usize, usize)>; INLINE_VISITED_CAPACITY],
    len: usize,
    // Keys are internal storage addresses and layout-node indices. Equality
    // still checks both components; keyed hashing of user input is unnecessary.
    overflow: Option<FxHashSet<(usize, usize)>>,
}

impl Default for Visited {
    fn default() -> Self {
        Self {
            inline: [std::mem::MaybeUninit::uninit(); INLINE_VISITED_CAPACITY],
            len: 0,
            overflow: None,
        }
    }
}

impl Visited {
    fn insert(&mut self, key: (usize, usize)) -> bool {
        if let Some(overflow) = &mut self.overflow {
            return overflow.insert(key);
        }
        if self.inline[..self.len]
            .iter()
            .any(|entry| unsafe { entry.assume_init() } == key)
        {
            return false;
        }
        if self.len < INLINE_VISITED_CAPACITY {
            self.inline[self.len].write(key);
            self.len += 1;
        } else {
            let mut overflow = FxHashSet::with_capacity_and_hasher(
                INLINE_VISITED_CAPACITY * 2,
                Default::default(),
            );
            overflow.extend(
                self.inline
                    .iter()
                    .map(|entry| unsafe { entry.assume_init() }),
            );
            overflow.insert(key);
            self.overflow = Some(overflow);
        }
        true
    }
}

// Bounds and address checks are identical for leaf and composite nodes.
#[inline]
fn project_node(
    index: usize,
    node: &GcLayoutNode,
    base: usize,
    limit: usize,
) -> Result<(usize, usize, usize), LayoutError> {
    let offset = usize::try_from(node.offset).map_err(|_| LayoutError::InvalidNode {
        index,
        reason: "offset exceeds address width",
    })?;
    let node_base = base.checked_add(offset).ok_or(LayoutError::InvalidNode {
        index,
        reason: "address overflow",
    })?;
    let remaining = limit.saturating_sub(offset);
    Ok((offset, node_base, remaining))
}

struct Evaluator<'a, F, const FOLLOW: bool, const SLOTS: bool, const MANAGED: bool> {
    nodes: &'a [GcLayoutNode],
    emit: F,
    visited: Option<Visited>,
    visits: usize,
}

impl<F: FnMut(*const u8), const FOLLOW: bool, const SLOTS: bool, const MANAGED: bool>
    Evaluator<'_, F, FOLLOW, SLOTS, MANAGED>
{
    #[inline(always)]
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
        // Heap tracing only walks inline aggregate/array/tag storage. Reference
        // targets are emitted for the collector's allocation mark set, never
        // followed here, so valid heap layouts cannot form reference cycles.
        // A visited entry per inline node wastes O(buffer length) scratch space
        // and hashing on every collection. Depth/visit limits still bound bad
        // inline descriptor cycles. Stack walks can follow cyclic references;
        // value-copy slot walks retain deduplication before rewriting payloads.
        if (FOLLOW || SLOTS)
            && let Some(visited) = &mut self.visited
        {
            if !visited.insert((base, index)) {
                return Ok(());
            }
        }
        self.visits += 1;
        let nodes = self.nodes;
        let node = nodes.get(index).ok_or(LayoutError::InvalidNode {
            index,
            reason: "index is out of bounds",
        })?;
        if matches!(
            node.kind,
            GC_LAYOUT_POINTER | GC_LAYOUT_RAW_POINTER | GC_LAYOUT_REFERENCE
        ) {
            let (_, node_base, remaining) = project_node(index, node, base, limit)?;

            if remaining < std::mem::size_of::<usize>() {
                return Ok(());
            }
            // Managed pointer slots may be atomically published while another
            // mutator prepares its root snapshot. Match whole-word stores;
            // packed unsafe layouts retain their unaligned contract.
            let candidate = if node_base.is_multiple_of(std::mem::align_of::<usize>()) {
                unsafe { std::sync::atomic::AtomicUsize::from_ptr(node_base as *mut usize) }
                    .load(std::sync::atomic::Ordering::Relaxed)
            } else {
                unsafe { std::ptr::read_unaligned(node_base as *const usize) }
            };
            if candidate == 0 || MANAGED && node.kind == GC_LAYOUT_RAW_POINTER {
                return Ok(());
            }
            (self.emit)(if SLOTS {
                node_base as *const u8
            } else {
                candidate as *const u8
            });
            if node.kind == GC_LAYOUT_REFERENCE && FOLLOW && node.child_count != 0 {
                return unsafe {
                    self.visit(node.first_child as usize, candidate, usize::MAX, depth + 1)
                };
            }
            return Ok(());
        }
        unsafe { self.visit_non_pointer(index, node, base, limit, depth) }
    }

    // Keep recursive container work out of the inlined pointer-leaf path.
    // Every child re-enters visit, preserving visit/depth/cycle limits.
    unsafe fn visit_non_pointer(
        &mut self,
        index: usize,
        node: &GcLayoutNode,
        base: usize,
        limit: usize,
        depth: usize,
    ) -> Result<(), LayoutError> {
        let (offset, node_base, remaining) = project_node(index, node, base, limit)?;
        match node.kind {
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
            GC_LAYOUT_INITIALIZED_REPEAT => {
                if FOLLOW {
                    return Err(LayoutError::InvalidNode {
                        index,
                        reason: "initialized sequence nodes require heap allocation bounds",
                    });
                }
                let count_offset = node.child_count as usize;
                let word = std::mem::size_of::<usize>();
                let stride =
                    usize::try_from(node.stride).map_err(|_| LayoutError::InvalidNode {
                        index,
                        reason: "sequence stride exceeds address width",
                    })?;
                if stride == 0
                    || count_offset.checked_add(word).is_none_or(|end| end > limit)
                    || offset > limit
                    || node.first_child as usize >= self.nodes.len()
                {
                    return Err(LayoutError::InvalidNode {
                        index,
                        reason: "invalid initialized sequence header or stride",
                    });
                }
                // All mutators are parked before heap scanning. Publication
                // uses Release and the mutator handshake publishes prior slot
                // writes, so this unaligned read has no concurrent writer.
                let count =
                    unsafe { std::ptr::read_unaligned((base + count_offset) as *const usize) };
                if count > remaining / stride {
                    return Err(LayoutError::InvalidNode {
                        index,
                        reason: "initialized sequence extent exceeds allocation",
                    });
                }
                for element in 0..count {
                    unsafe {
                        self.visit(
                            node.first_child as usize,
                            node_base + element * stride,
                            stride,
                            depth + 1,
                        )?
                    };
                }
            }
            GC_LAYOUT_SWISS_GROUP => {
                let control_offset = node.child_count as usize;
                let stride =
                    usize::try_from(node.stride).map_err(|_| LayoutError::InvalidNode {
                        index,
                        reason: "dictionary entry stride exceeds address width",
                    })?;
                if FOLLOW
                    || stride == 0
                    || control_offset.checked_add(8).is_none_or(|end| end > limit)
                    || offset > limit
                    || stride.checked_mul(8).is_none_or(|bytes| bytes > remaining)
                    || node.first_child as usize >= self.nodes.len()
                {
                    return Err(LayoutError::InvalidNode {
                        index,
                        reason: "invalid dictionary group bounds or child",
                    });
                }
                // Controls are a logical u64 in the stdlib, not a native-order
                // byte array. Reading/shifting the same word preserves slot
                // numbering on either endianness. The world is stopped here.
                let controls =
                    unsafe { std::ptr::read_unaligned((base + control_offset) as *const u64) };
                let mut full = !controls & 0x8080_8080_8080_8080;
                while full != 0 {
                    let slot = full.trailing_zeros() as usize / 8;
                    unsafe {
                        self.visit(
                            node.first_child as usize,
                            node_base + slot * stride,
                            stride,
                            depth + 1,
                        )?
                    };
                    full &= full - 1;
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
                // A selected variant has no siblings to resume after its child.
                return unsafe {
                    self.visit(
                        node.first_child as usize + tag as usize,
                        node_base,
                        remaining,
                        depth + 1,
                    )
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
    match mode {
        TraceMode::Heap => unsafe { evaluate::<false, false, false>(base, nodes, limit, emit) },
        TraceMode::Stack => unsafe { evaluate::<true, false, false>(base, nodes, limit, emit) },
    }
}

// The traversal mode is fixed for a complete walk, including recursive calls.
// Specializing it removes stack-cycle and copy-slot bookkeeping from heap
// tracing without weakening the depth, visit, tag or address checks.
unsafe fn evaluate<const FOLLOW: bool, const SLOTS: bool, const MANAGED: bool>(
    base: *const u8,
    nodes: &[GcLayoutNode],
    limit: usize,
    emit: impl FnMut(*const u8),
) -> Result<(), LayoutError> {
    if base.is_null() || nodes.is_empty() {
        return Ok(());
    }
    let mut evaluator = Evaluator::<_, FOLLOW, SLOTS, MANAGED> {
        nodes,
        emit,
        visited: (FOLLOW || SLOTS).then(Visited::default),
        visits: 0,
    };
    unsafe { evaluator.visit(0, base as usize, limit, 0) }
}

/// Like `trace_layout` in heap mode, but emits only managed edges: raw pointer
/// targets are excluded because unsafe code may keep them dangling.
pub(crate) unsafe fn trace_managed_edges(
    base: *const u8,
    nodes: &[GcLayoutNode],
    limit: usize,
    emit: impl FnMut(*const u8),
) -> Result<(), LayoutError> {
    unsafe { evaluate::<false, false, true>(base, nodes, limit, emit) }
}

/// Walk only inline value storage and report nonnull pointer *slots*. Copy
/// layouts use pointer nodes for erased payload headers, with the same physical
/// aggregate/array/tag interpretation as tracing. Reference targets are never
/// visited: copying a value preserves its reference and class identities.
pub(crate) unsafe fn visit_pointer_slots(
    base: *const u8,
    nodes: &[GcLayoutNode],
    limit: usize,
    emit: impl FnMut(*const u8),
) -> Result<(), LayoutError> {
    unsafe { evaluate::<false, true, false>(base, nodes, limit, emit) }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    #[test]
    fn leaf_projection_checks_packed_slots_and_overflow() {
        let mut storage = [0_usize; 2];
        let base = storage.as_mut_ptr().cast::<u8>();
        let word = std::mem::size_of::<usize>();
        let node = GcLayoutNode {
            offset: 1,
            kind: GC_LAYOUT_POINTER,
            stride: 0,
            first_child: 0,
            child_count: 0,
            width: 0,
            reserved: [0; 6],
        };
        unsafe { std::ptr::write_unaligned(base.add(1).cast::<usize>(), 0x1234) };
        for mode in [TraceMode::Heap, TraceMode::Stack] {
            let mut edges = Vec::new();
            unsafe {
                trace_layout(base, &[node], word, mode, |p| edges.push(p)).unwrap();
            }
            assert!(edges.is_empty(), "truncated packed slots are not read");
            unsafe {
                trace_layout(base, &[node], word + 1, mode, |p| edges.push(p)).unwrap();
            }
            assert_eq!(edges, [0x1234 as *const u8]);
        }
        let mut slots = Vec::new();
        unsafe {
            visit_pointer_slots(base, &[node], word + 1, |p| slots.push(p)).unwrap();
        }
        assert_eq!(slots, [unsafe { base.add(1) } as *const u8]);
        let error = unsafe {
            trace_layout(
                usize::MAX as *const u8,
                &[node],
                usize::MAX,
                TraceMode::Heap,
                |_| panic!("overflow must not emit"),
            )
        };
        assert!(matches!(
            error,
            Err(LayoutError::InvalidNode {
                index: 0,
                reason: "address overflow"
            })
        ));
    }

    #[test]
    fn initialized_sequence_nodes_check_extent_and_require_heap_bounds() {
        #[repr(C)]
        struct Buffer {
            initialized: usize,
            capacity: usize,
            values: [usize; 2],
        }
        let mut buffer = Buffer {
            initialized: 1,
            capacity: 2,
            values: [0x11, 0x22],
        };
        let nodes = [
            GcLayoutNode {
                offset: std::mem::offset_of!(Buffer, values) as u64,
                stride: std::mem::size_of::<usize>() as u64,
                first_child: 1,
                child_count: 0,
                kind: GC_LAYOUT_INITIALIZED_REPEAT,
                width: 0,
                reserved: [0; 6],
            },
            GcLayoutNode {
                offset: 0,
                stride: 0,
                first_child: 0,
                child_count: 0,
                kind: GC_LAYOUT_POINTER,
                width: 0,
                reserved: [0; 6],
            },
        ];
        let mut pointers = Vec::new();
        unsafe {
            trace_layout(
                (&buffer as *const Buffer).cast(),
                &nodes,
                std::mem::size_of::<Buffer>(),
                TraceMode::Heap,
                |ptr| pointers.push(ptr as usize),
            )
        }
        .unwrap();
        assert_eq!(pointers, [0x11]);
        assert!(
            unsafe {
                trace_layout(
                    (&buffer as *const Buffer).cast(),
                    &nodes,
                    std::mem::size_of::<Buffer>(),
                    TraceMode::Stack,
                    |_| {},
                )
            }
            .is_err()
        );
        buffer.initialized = 3;
        assert!(
            unsafe {
                trace_layout(
                    (&buffer as *const Buffer).cast(),
                    &nodes,
                    std::mem::size_of::<Buffer>(),
                    TraceMode::Heap,
                    |_| {},
                )
            }
            .is_err()
        );
    }

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
    fn heap_inline_descriptor_cycle_is_bounded() {
        let nodes = [node(0, 0, 0, 1, GC_LAYOUT_AGGREGATE, 0)];
        let storage = [0usize];
        assert_eq!(
            unsafe {
                trace_layout(
                    storage.as_ptr().cast(),
                    &nodes,
                    std::mem::size_of_val(&storage),
                    TraceMode::Heap,
                    |_| {},
                )
            },
            Err(LayoutError::LimitExceeded),
        );
    }

    #[test]
    fn heap_repeat_emits_active_edges_without_following_reference_targets() {
        let count = 4096;
        let nodes = [
            node(0, 16, 1, count, GC_LAYOUT_REPEAT, 0),
            node(0, 0, 2, 2, GC_LAYOUT_TAGGED, 8),
            node(0, 0, 0, 0, GC_LAYOUT_AGGREGATE, 0),
            // This child points back to the tag graph. Heap mode emits the
            // candidate only; following it would dereference a sentinel.
            node(8, 0, 1, 1, GC_LAYOUT_REFERENCE, 0),
        ];
        let storage: Vec<_> = (0..count)
            .map(|i| [u64::from(i % 2), 0x1000 + u64::from(i) * 16])
            .collect();
        let mut roots = Vec::new();
        unsafe {
            trace_layout(
                storage.as_ptr().cast(),
                &nodes,
                std::mem::size_of_val(storage.as_slice()),
                TraceMode::Heap,
                |root| roots.push(root as usize),
            )
        }
        .unwrap();
        let expected: Vec<_> = (0..count)
            .filter(|i| i % 2 == 1)
            .map(|i| 0x1000 + i as usize * 16)
            .collect();
        assert_eq!(roots, expected);
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
