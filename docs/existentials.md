Existentials and Interface Method Resolution
===========================================

Overview
--------
Taro uses Swift-style existentials: an existential value carries one witness table
per interface in the type. Method dispatch on `any Interface` uses those tables
instead of a concrete type.

Existential container
---------------------
- Layout: `data_ptr` + `witness_tables[]`
- `witness_tables` order: source order from the type, e.g. `any A & B` stores
  `[table(A), table(B)]`.
- No implicit superfaces are stored in the container.

Witness table layout
--------------------
Each interface has its own witness table for a given concrete type:
- Method slots: ordered by that interface's own requirements.
- Superface pointers: the table also contains references to superface tables so
  `any P` can be upcast to `any Q` when `P: Q`, and so superface methods can be
  dispatched on `any P`.

Method resolution (typechecker)
-------------------------------
For method calls, the typechecker runs the usual autoderef + autoref search.
When the receiver is an existential:
- Treat each interface in the existential as an "object candidate".
- Collect method requirements for that interface + superfaces.
- Match by name, substitute `Self := any Interface` plus interface args, then
  unify with the expected method type.
- Record the overload source (the selected interface method `def_id`) so later
  stages can resolve direct vs virtual calls.

Call lowering (THIR/MIR)
------------------------
Method calls on `any Interface` lower the same way as other method calls:
- The call callee is a ZST function item (`def_id` + instantiated args).
- The call args start with the receiver, followed by explicit arguments.
- There is no special MIR terminator for virtual calls.

This mirrors rustc: the callee identity (def_id + args) is the "memory" of which
method is being called, and later stages decide whether the call is direct or
virtual.

Instance resolution (mono/codegen)
----------------------------------
A shared resolver maps a call's callee identity (`def_id` + args) to an
`Instance`:
- `InstanceKind::Item(def_id)` for direct, monomorphized calls.
- `InstanceKind::Virtual { method_id, method_interface, slot, table_index }`
  when `Self` is an existential.

Resolution rules:
- Detect interface methods by checking the item's parent is an `interface`.
- Read `Self` from the instantiated args and require it to be a boxed
  existential.
- Pick the root interface by scanning the existential's interface list (order
  matters) and checking for a direct match or a superface match.
- Compute the method slot from the interface requirements list.

Monomorphization only enqueues `Item` instances. `Virtual` instances do not
produce a monomorphized body; they rely on witness tables to point at the
concrete implementations for each conformance.

Upcasting
---------
Two forms are supported:
- Subset: `any A & B -> any A` projects the witness table list.
- Superface: `any P -> any Q` when `P: Q`, by projecting `Q`'s table from `P`'s
  witness table.

Virtual dispatch (codegen)
--------------------------
Codegen resolves calls to interface methods using the callee's `def_id` and
generic args:
- If `def_id` is an interface method and `Self` is an existential, treat the call
  as virtual.
- Determine the root interface table index from `Self`'s interface list.
- Determine the method slot index within the method's interface requirements.
- If the method belongs to a superface, follow the superface pointer in the root
  witness table to find the correct table before indexing the slot.

The call still looks like a normal MIR `Call`; the codegen backend decides
whether to emit a direct call or an indirect call through a witness table.
