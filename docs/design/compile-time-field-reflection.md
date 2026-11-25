# Compile-Time Field Reflection (`#for` / `#fields` / `#if` / `#typeName`)

This document specifies the compile-time field reflection rules for library-defined derivations in Taro (TAR-54), building on the `@key("...")` and `@skip` field metadata introduced in TAR-53.

## 1. Provisional Syntax

```taro
// Unqualified nominal type name as a string literal (e.g. "Pair").
name := #typeName(T)

// Unroll a block once per stored field of T in declaration order.
#for field in #fields(T) {
    // Compile-time constant metadata properties on `field`:
    //   field.name: string      — source field identifier
    //   field.key: string       — effective coding key (`@key("...")` if present, else `field.name`)
    //   field.skipped: bool     — true if annotated with `@skip`, else false
    //   field.index: uint       — 0-based declaration index
    //   field.isPublic: bool    — true iff field visibility is `public`
    //   field.isVisible: bool   — true iff field is visible from the expansion site
    //
    // Typed value projection (with generic parameters substituted):
    //   field.get(value)        — lowers to `value.<field.name>` at the field's instantiated type
    #if !field.skipped && field.isVisible {
        process(field.key, field.get(value))
    }
}
```

## 2. Field Ordering

- `#fields(T)` iterates over the **stored fields** of a struct or class `T` in **strict declaration order** (`0..N`).
- For classes with inheritance, inherited base-class stored fields precede subclass stored fields in flattened layout order (matching derived `Debug` and payload layout).
- Computed properties, static variables, and methods are not stored fields and are excluded from `#fields(T)`.

## 3. Cross-Package Visibility & Private-Field Access Rules

1. **Metadata visibility**:
   - All stored fields of an exported struct or class are serialized in `StructFieldWire` (including `name`, `ty`, `visibility`, `coding_key`, and `coding_skip`) so cold builds and warm cached package imports observe identical field lists and declaration indices.
   - `field.isPublic` (`bool`) reports whether the field was declared `public`.
   - `field.isVisible` (`bool`) reports whether the field is accessible from the module expanding `#for` (`gcx.is_definition_visible(field.def_id, current_def)`).
2. **Value access (`field.get(expr)`)**:
   - `field.get(expr)` desugars to a direct member access `expr.<field_name>` on the target value or reference, and is subject to Taro's standard visibility check relative to the expanding function's defining scope:
     - **Inside `extend T` / `conform T`**: `private`, `internal`, and `public` fields of `T` are all visible (`field.isVisible == true`) and can be read via `field.get(expr)`.
     - **Same package, outside `T`**: `internal` and `public` fields are visible (`field.isVisible == true`); `private` fields have `field.isVisible == false` and reading them via `field.get(expr)` is a compile-time error.
     - **Cross-package**: only `public` fields are visible (`field.isVisible == true`); an unguarded `field.get(expr)` on an imported `private` or `internal` field is rejected at compile time.
   - A library derivation that intentionally skips non-visible fields can guard value access with `#if field.isVisible { ... }`; because `#if` prunes the untaken branch before typechecking, skipped private/internal fields never trigger visibility errors.

## 4. Generic Parameter Substitution

- `#fields(T)` and `#typeName(T)` operate on a nominal struct or class type `T` (including concrete generic instantiations such as `Pair[int32, string]` or `Pair[bool, int32]`, as well as parameterized nominal types such as `Pair[A, B]` or `Self` inside a generic function or `impl` block).
- When `T` is a parameterized or instantiated generic nominal type `Adt(def, generic_args)`, each field's declared type is substituted with `T`'s generic arguments via `instantiate_ty_with_args(gcx, field.ty, generic_args)`.
- In each unrolled iteration `i` of `#for field in #fields(T)`, `field.get(value)` lowers to `value.<field_name>` with the substituted field type `T_i`, and overload/interface selection (e.g. `Debug::debug`, `Encodable::encode`) resolves independently per field at `T_i`.
- Applying `#fields(T)` to a non-struct/non-class type (such as an enum, interface, primitive, tuple, or unconstrained opaque type parameter) is rejected with a compile-time diagnostic.
