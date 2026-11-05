# Existentials

An `any Interface` value stores a data pointer, a concrete-type metadata
pointer, and one witness-table pointer for each interface in the existential
type: a 2+N-word header. The data pointer reaches GC-managed payload storage.
Interface aliases are expanded and exact duplicate interface references
are removed, preserving first-occurrence order.

The metadata identifies the concrete type and its known conformances, including
compiler-provided callable conformances for closures and their inherited
interfaces, and supported primitive operator conformances. Runtime type tests and checked casts use it to test a concrete type
or find a witness table for an interface outside the existential's declared
interface list.

The runtime metadata header contains a conformance-entry pointer, its length,
and a canonical concrete-type identity token (runtime ABI revision 29). Exact
type tests compare identity tokens. Dispatch metadata is separate: checked and
unchecked arithmetic implementations must not be coalesced when a checked
application links against a release-built standard library. Primitive operator
helpers are specialized in the consuming package, using its overflow policy;
an erased value carries the tables selected when it was boxed.

## Payload storage and copies

Boxing allocates initialized, typed GC storage for the concrete payload.
Ordinary value copies give inline payloads independent storage; class, List,
reference and other handles inside a payload retain their ordinary sharing.
Neither copying nor casting calls user Clone. Explicit recursive cloning is a
separate library operation.

Payload references retain the selected box even if an alias replaces the
container. There is no native erased-owner word, retain/release path, cleanup
witness or consuming receiver mode. The collector traces the payload's exact
layout; unreachable cycles can be reclaimed without running a language
finalizer. Safe programs synchronize shared mutation themselves.

## Witness Tables

Each concrete implementation has one table per interface containing:

- method pointers for dispatchable requirements, in requirement order;
- pointers to tables for directly inherited interfaces, after the method slots.

Only methods with a `self` receiver and no method-owned generic parameters
occupy dispatch slots. Static methods have no slot, and calls to generic
methods directly through existential values are rejected. A supported generic
call may implicitly open the container to its actual concrete type; that generic
body can then specialize its method normally. This is concrete opening, not an
existential self-conformance or a generic witness-table slot.

The container stores only its declared interface tables. Upcasting to a subset
projects the corresponding table. Upcasting to an inherited interface follows
the parent table pointer.

## Resolution

The type checker applies normal autodereference and autoreference while looking
up methods. For an existential receiver it searches every declared interface
and its inherited interfaces, substitutes `Self` with the existential type, and
records the selected requirement.

MIR represents the result as an ordinary call whose callee identifies the
requirement. Instance resolution classifies it as either:

- a direct monomorphized item; or
- a virtual call with its interface, method slot, and table index.

Virtual calls do not produce a separate function body. LLVM loads the selected
witness table, follows an inherited-interface pointer when required, and calls
the method slot indirectly. Witness entries point to adapter functions that
bridge the erased data pointer to the concrete implementation's calling
convention. When MIR establishes the concrete receiver, code generation can
instead emit a direct call using its devirtualization hint.

## Direct Self results

A requirement declared directly as `func duplicate() -> Self` can be called
through an existential. Its result is re-erased into the receiver's static
existential type, including all interfaces in an intersection. This does not
make two independently erased payloads interchangeable as Self arguments.
Methods taking payload-dependent arguments, or returning borrowed/nested Self,
remain unavailable through erased dispatch. Independently bound associated-type
results still use their known concrete ABI.

Direct Self adapters call the concrete implementation using its concrete
calling convention and box its result in fresh GC storage. The caller rebuilds
the declared witness pointers from the result metadata. No payload Clone or
native ownership transfer is inserted.

Witness adapters and closure-to-function-pointer bridges remain unwindable even
when LLVM proves their results constant. A collection inside a non-leaf adapter
must still reach the caller's stack maps. Boxing, extraction and adapter spills
use function-entry storage so repeated operations in loops do not grow the stack.

Specialization repeats the payload-signature check when a generic receiver
becomes erased only after substitution. A `T: P` bound does not justify passing
a second independently erased container as the witness's concrete `&Self`.
Inherited table checks use the receiver's stored hidden defaults. Independently
known argument types, such as `PartialEq[Counter]`, keep their ordinary ABI.
Invalid specializations stop before LLVM emits abstract placeholder functions.

## Callable Existentials

Calling a value such as `any Fn(int32) -> int32` with `value(42)` selects the
callable interface's `call` requirement. Arguments are
packed into its `Args` tuple, and the call uses the same witness-table dispatch
as an explicitly named interface method. Closure adapters bridge that tuple
to the closure's parameters. Async callable requirements use async method
dispatch and require an enclosing `await` expression.

Callable signatures and sync/async categories must agree after erasure. Mixed
callable interfaces require an explicit conversion before invocation.

## Checked conversions and payload references

`value is T` inspects the value. `value as? T` returns an optional copied value.
Ordinary struct payload copies are independent; handle values share their targets.
`takeAs[T]()` returns the typed payload on success and the original existential
on mismatch.

`asRef[T]()` returns an optional writable `&T` to the exact stored payload type.
The reference keeps that payload storage alive. Class inspection also requires
an exact stored type: a writable handle slot cannot be reinterpreted as a base
or derived handle slot. `asMut` has been removed; `asRef` supplies write access.

The compiler represents hidden Self with a bound type distinct from ordinary
generic parameters, including nested binder depth. Defaults such as `Rhs = Self`
therefore remain receiver-relative when a surrounding generic function is
instantiated. Metadata includes receiver-relative lookup keys alongside concrete
keys, sharing the same witness table. An explicitly different generic argument
does not satisfy such a default. Methods whose arguments or results still expose
an unresolved hidden type are rejected rather than assigned a guessed layout.
Boxing proves complete conditional conformances using the normal solver.

Unbound associated result types also require an explicit existential binding
when a generic helper specializes to an erased receiver. A discarded result
still needs a concrete storage ABI. The compiler diagnoses this before
inlining or layout; supplying a known binding such as `any Producer[Output = int32]`
preserves ordinary generic and inherited-interface calls.
