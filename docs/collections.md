# Collections

Taro's standard collections provide shared, growable storage for sequences,
keyed values, unique elements, and ordered work queues.

| Collection | Use |
| --- | --- |
| `List[Element]` | Indexed sequences, stacks, sorting, and binary search |
| `Dictionary[Key, Value]` | Values looked up by a hashable key |
| `Set[Element]` | Unique hashable elements and membership checks |
| `Counter[Key]` | Counts associated with hashable keys |
| `Deque[Element]` | Efficient insertion and removal at both ends |
| `PriorityQueue[Element]` | Retrieval according to a priority ordering |
| `BTreeMap[Key, Value]` | Sorted key-value entries with O(log n) ordered queries |
| `BTreeSet[Element]` | Sorted unique elements with O(log n) ordered queries |
| `BitSet` | Compact word-packed dynamic set of `usize` bit indices |

This guide covers list initialization, membership tests, sorting, reversing
and search, and the behavior of deques and priority queues, including sharing,
iteration, and callback failures.

## Lists and initialization

Lists are shared handles. Assignment and argument passing share their contents.
`copy()` creates independent outer storage with ordinary element copies;
`clone()` recursively invokes element cloning when supported. References,
classes, or nested lists inside an ordinary copy still share their targets.

```taro
counts := List[int32]::repeating(0, count: 100)
grid := List[List[int32]]::generate(count: 3, by: (_) => {
    List[int32]::repeating(0, count: 4)
})
grid[0][0] = 1 // The other rows remain zero.
snapshot := counts.copy()
```

Every collection except `PriorityQueue` conforms to `Default`, whose
`default()` is a new empty collection, so a derived `Default` struct can hold
one without a field default.

`repeating(value, count:)` copies the same value. Repeating a list therefore
shares one row. `generate(count:, by:)` invokes the factory exactly once per
index, in ascending order, and never invokes it for zero elements. Both take
O(n) time and storage, excluding factory work.

Lists support ordered, element-wise equality when their elements implement
`PartialEq`. Lengths must match; nested lists compare recursively. Equality
does not detect cycles. This also enables `assertEqual(actual, expected, ...)`
for list and matrix results.

Collections are not synchronized. Mutating a list, dictionary, set, counter,
deque or priority queue from two threads at once, or reading one while
another thread mutates it, is unsupported: it may panic, for example when a
cursor or sort sees a structural change, or it may leave the collection
corrupted. Confine a collection to one task or guard it with a
`std::sync::Mutex`.

## Membership

`element in collection` tests whether a collection holds an element, and
`element !in collection` tests that it does not. Both call `contains` through
`Contains[Element]`, which passes the element by reference.

```taro
var seen = Set[string]::new()
for word in ["to", "be", "or", "not", "to", "be"] {
    if word !in seen { seen.insert(word) }
}
code := 201
assert(code in [200, 201, 204])
```

| Container | Tests |
| --- | --- |
| `List`, `[T; N]`, `Span`, `Deque` | an element, by `==`; a linear scan |
| `Set` | an element, by hash |
| `Dictionary`, `Counter` | a key, by hash |
| `BTreeMap`, `BTreeSet` | a key or element, by `Ord` in O(log n) |
| `BitSet` | a `usize` bit index in O(1) |
| `Range`, `ClosedRange` | `start <= value < end` or `start <= value <= end` |
| `string` | a `rune` or a substring |

Scanning containers need elements that conform to `PartialEq`. `Optional` is
not a container: unwrap it first. Each container also keeps its `contains`
method, so `seen.contains(&word)` still works.

## Sorting

```taro
var numbers: [int32] = [3, 1, 2]
ascending := numbers.sorted()
descending := numbers.sorted(by: (a, b) => a > b)
numbers.sort(by: (a, b) => a < b)
```

`sort()` mutates the shared list and returns unit. `sorted()` returns an
independent shallow list copy. Both have a `by:` overload, and both are stable:
elements equivalent under the ordering retain their original relative order.
Default ordering requires `Ord`; a custom comparator does not require it.

The integer types, `rune` and `string` are `Ord`. Strings order bytewise by
their UTF-8 encoding, which is Unicode scalar value order, not a locale's
collation. `float` and `double` are only `PartialOrd`, because NaN is
unordered, so `sorted()` does not accept them. Sort floating-point values with
a comparator when they contain no NaN:

```taro
var reals: [double] = [2.5, -1.0, 0.25]
reals.sort(by: (a, b) => a < b)
```

A struct or enum can derive its ordering by listing `Comparable` (or
`PartialEq, PartialOrd, Ord`): fields compare in declaration order, enum cases
in declaration order and then by payload. See *Derived Conformances* in the
declarations guide.

```taro
struct Version: Comparable {
    major: int32
    minor: int32
}

func main() {
    var versions: [Version] = [Version { major: 2, minor: 0 }, Version { major: 1, minor: 9 }]
    versions.sort()
    assert(versions[0].major == 1)
}
```

`Ordering`, `PartialOrd`, `Ord` and `Comparable` are in the prelude, so `<` on
strings and conformances for your own types need no import.

The comparator returns true if its first argument precedes its second. It must
define a strict weak ordering: no value precedes itself, ordering is transitive,
and ordering-equivalence is transitive. Use `<`, not `<=`. A comparator may
capture state, but it must not modify the sorted list or fields used to order
its elements. Comparators receive ordinary values; object handles still share
their objects. NaNs require an explicitly defined ordering; ordinary floating
point `<` is not a valid ordering over a mixture containing NaNs.

The implementation is a stable merge sort with O(n log n) comparisons and O(n)
auxiliary storage. These bounds exclude comparator cost. It binary-insertion
sorts runs of 32 elements while copying them into a scratch list, then merges
runs bottom-up. A list of up to 32 elements needs one scratch list; longer
lists need two. `sorted()` returns the scratch list itself. All comparisons
finish before `sort()` writes into the existing list buffer, so a comparator
panic leaves the original order intact unless the callback itself changed the
list or elements.
Structural callback mutation, including another sort, is detected and panics.
Mutation through escaped references is not detected; concurrent unsynchronized
mutation is unsupported.

A sort of two or more elements invalidates existing list cursors, even when
already sorted or when comparison panics. Empty and single-element sorts do
not call the comparator or invalidate cursors. Element references and spans
continue to address the original buffer and observe the committed values.

## Reversing

```taro
var items: [int32] = [1, 2, 3]
items.reverse()            // [3, 2, 1], seen through every handle
copy := items.reversed()   // [1, 2, 3]; items is unchanged
```

`reverse()` reverses the shared list in place and returns unit; it takes O(n)
time and allocates nothing. `reversed()` returns an independent shallow copy
in reverse order, like `sorted()`. Like a sort, reversing two or more elements
invalidates existing cursors, while empty and single-element lists keep them.
Element references and spans keep addressing the buffer and observe the new
order. To visit indices from high to low without copying, iterate
`(0..items.len()).reversed()`.

## Binary search

```taro
var values: [int32] = [1, 2, 2, 4]
first := values.lowerBound(2)        // 1
after := values.upperBound(2)        // 3
found := values.binarySearch(2)     // .some(1)
missing := values.binarySearch(3)   // .none
```

These methods use O(log n) comparisons and require input sorted under the same
ordering. All three accept a `by:` comparator for custom or descending orders.
`lowerBound` returns the first position not preceding the target; `upperBound`
returns the first position following it. Both may return `len()` and return
zero for an empty list. `binarySearch` returns the first ordering-equivalent
element, which need not be `PartialEq`-equal to the target. Callbacks must not
mutate the searched list or change ordering during the search.

## Deque

```taro
queue := Deque[int32]::new()
queue.pushBack(10)
queue.pushFront(5)
first := queue.popFront() // .some(5)
last := queue.popBack()   // .some(10)
empty := queue.front()   // .none
```

`Deque` uses a ring buffer. Pushes at either end are amortized O(1); pops,
`front`, `back`, indexing, and `get` are O(1). `get` and end operations return
ordinary optional values, not references into the ring. Indexing panics when
out of bounds. `deque[i] = value` replaces an element in place. Removed slots
are cleared so the deque stops retaining them. `reserve(n)` reserves at least
n slots and costs O(n + current length). Deques compare element-wise, front to
back, when their elements implement `PartialEq`.

Assignment shares the deque, while `copy()` makes a shallow independent copy.
`clear()` releases its backing slots and resets capacity to zero. Iteration
visits front to back; iterator copies share cursor position. Push, pop, and
clear invalidate cursors. Element writes and reserving capacity preserve
logical iteration order and do not invalidate them. Exhausted cursors remain
exhausted.

Use a deque for BFS and sliding windows. Repeatedly removing list index zero
shifts the remaining elements and can make an otherwise linear algorithm
quadratic.

## Priority queue

```taro
minimum := PriorityQueue[int32]::new()
maximum := PriorityQueue[int32]::new(by: (a, b) => a > b)
minimum.push(7)
minimum.push(3)
next := minimum.peek() // .some(3), does not remove
item := minimum.pop()  // .some(3)
```

The default is a min heap and requires `Ord`. The custom comparator uses the
same convention as sorting: true means the first element has higher priority
and should be returned earlier. Equal priorities have no FIFO guarantee. Add
an explicit sequence-number tie break when deterministic arrival order matters.

`peek` is O(1), `push` is amortized O(log n), and `pop` is O(log n), excluding
comparator cost. `pop` completes all comparisons before changing the heap and
allocates nothing. It walks to a leaf with one comparison per level and then
climbs to the replacement's position, which takes about log2(n) comparisons
for distinct priorities and two when the priorities at the top are equal.
`reserve(n)` reserves room for at least n elements.

Comparator panics leave its contents intact. Reentrant push, pop, or clear
from a comparator panics. Do not mutate ordering fields while an element is
queued. For Dijkstra-style updates, insert a new entry and discard stale
entries when popped.

Deques and priority queues store each element as an optional so that a
removed slot can be cleared for the collector. A slot therefore takes the size
of `Element?`: 8 bytes for an `int32`, not 4.

The queue stores a callable interface, keeping the public type
`PriorityQueue[Element]` independent of the closure type. Assignment shares the
heap. `copy()` copies the elements into independent outer storage but retains
the same comparator, including its captured state. No heap iteration API is
provided because internal heap order is not sorted order.

## Ordered collections (`BTreeMap` and `BTreeSet`)

```taro
events := BTreeMap[int32, string]::new()
events.insert(key: 10, value: "start")
events.insert(key: 25, value: "end")
assert(events.first() == .some((10, "start")))
assert(events.lowerBound(&15) == .some((25, "end")))
```

`BTreeMap[Key: Ord, Value]` stores entries in a B-tree with branching factor
`B = 6` (5 to 11 keys per non-root node). Lookup, insertion, removal, `first`,
`last`, `popFirst`, `popLast`, `lowerBound`, `upperBound`, `lastBefore`, and
`lastAtOrBefore` run in O(log n) time. `entries()`, `keys()`, and `values()`
iterate in ascending key order, and `range` seeks in O(log n) and yields each
matching entry in amortized O(1) (`O(log n + k)` total).

`BTreeSet[Element: Ord]` wraps `BTreeMap[Element, ()]` with set operations
(`insert`, `remove`, `contains`, `union`, `intersection`, `difference`,
`symmetricDifference`, `isSubset`, `isSuperset`) and the same ordered queries
and ascending range iteration.

Assignment shares the backing tree storage, while `copy()` creates an
independent shallow copy and `clone()` deep-clones keys and values. Structural
mutation during iteration or comparator callbacks panics. Vacated node slots are
cleared to `.none` on removal, pop, split, and merge so removed references are
not retained by the collector.

## BitSet

```taro
seen := BitSet::new(withCapacity: 256)
seen.insert(42)
assert(42 in seen && seen.countOnes() == 1)
```

`BitSet` stores a dynamic `uint64`-word bit vector. `insert`, `set`, and
`toggle` grow storage on demand; `contains` and `remove` return `false` without
growing past the current word count. `len()`, `countOnes()`, and `isEmpty()` are
O(1) via a cached popcount. Bulk set operations (`unionWith`, `intersectWith`,
`differenceWith`, `symmetricDifferenceWith`, plus non-mutating variants,
`isSubset`, and `isDisjoint`) operate word-at-a-time in O(words), and iteration
skips zero words and steps set bits in O(words + set bits).

Assignment shares the bit set, while `copy()` and `clone()` make independent
copies. Structural changes invalidate active cursors. Equality (`==`) is
canonical and ignores trailing zero words, so a grown bit set whose bits are
later removed equals `BitSet::new()`.

## Testing

Run the standard library tests using an SDK built from the current sources:

```sh
taro test std --std-path std
taro test std --std-path std --release
```

Collection tests cover ordering, sharing, wrapped deque growth, callback
panics, iterator invalidation, and garbage collection during comparisons.
Integration tests exercise the collections together in graph traversal,
scheduling, sliding windows, dynamic programming, and other algorithms.
Large-input tests and comparison budgets check complexity without depending on
machine speed. See [Testing](testing.md) for the test harness and filtering
options.
