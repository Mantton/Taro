# Existentials

An `any Interface` value stores a data pointer and one witness table for each
interface named by the existential type. Tables appear in source order.

## Witness Tables

Each concrete implementation has one table per interface containing:

- method pointers in requirement order;
- pointers to tables for inherited interfaces.

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
the method slot indirectly.
