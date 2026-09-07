# Existentials

An `any Interface` value stores a data pointer, a concrete-type metadata
pointer, and one witness-table pointer for each interface in the existential
type. Interface aliases are expanded and exact duplicate interface references
are removed, preserving first-occurrence order.

The metadata identifies the concrete type and its known conformances. Runtime
type tests and checked casts use it to test a concrete type or find a witness
table for an interface outside the existential's declared interface list.

## Witness Tables

Each concrete implementation has one table per interface containing:

- method pointers for dispatchable requirements, in requirement order;
- pointers to tables for directly inherited interfaces, after the method slots.

Only methods with a `self` receiver and no method-owned generic parameters
occupy dispatch slots. Static methods have no slot, and calls to generic
methods through existential values are rejected, including calls reached by
instantiating a generic bound with an existential type.

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
