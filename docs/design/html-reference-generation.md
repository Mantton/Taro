# HTML Reference Generation (`taro doc`) — Design Brief & Scope (TAR-55)

This document defines the scope, metadata inventory, inclusion rules, page structure, example-linking contract, CLI interface, and acceptance fixture for HTML API reference generation (`taro doc`), following the executable documentation test harness (`taro test --doc`) introduced in TAR-40.

---

## 1. Goals and Separation from `taro test --doc`

- **TAR-40 (`taro test --doc`)** extracts fenced ```` ```taro ```` blocks from `///` comments and Markdown files, wraps snippets without `func main()`, compiles them against the enclosing package, and executes them with source-line remapping.
- **TAR-55 (`taro doc <package>`)** scopes the static HTML reference generator that renders browsable package, module, type, interface, and function documentation from compiler semantic metadata and `///` Markdown prose, cross-linking every rendered code example to its corresponding `taro test --doc` test identity.

---

## 2. Representative Public Generic Type Trace: `std::optional::Optional[Wrapped]`

We trace `std::optional::Optional[Wrapped]` (defined in [std/src/optional/optional.tr](../../std/src/optional/optional.tr#L6-L217) and re-exported in [std/src/prelude/prelude.tr](../../std/src/prelude/prelude.tr#L3)) and its generic transformation method `Optional::map`:

```taro
/// An optional value that may or may not contain a wrapped value.
///
/// `Optional[T]` represents either `.some(value)` containing a value of type T,
/// or `.none` representing the absence of a value.
///
/// The shorthand syntax `T?` is equivalent to `Optional[T]`.
@lang("Optional")
public enum Optional[Wrapped] {
    case some(Wrapped)
    case none
}

extend[Wrapped] Optional[Wrapped] {
    /// Transforms the contained value using a function.
    ///
    /// Returns `.none` if the optional is none, otherwise returns
    /// `.some(f(value))`.
    ///
    /// ```taro
    /// x: int32? = .some(21)
    /// doubled := x.map((v) => v * 2)
    /// assert(doubled == .some(42))
    /// ```
    public func map[U, F: Fn[Wrapped, U]](_ f: F) -> Optional[U] {
        match self {
            case .some(v) => .some(f(v))
            case .none => .none
        }
    }
}
```

### 2.1 Metadata Currently Available to the CLI

When `compiler` runs through semantic collection and type-database construction (`compiler/src/compile/context.rs`, `compiler/src/metadata/declarations.rs`, `compiler/src/metadata/wire.rs`), the following facts are already available in `GlobalContext` (`Gcx`) and serialized in `SemanticPayloadWire`:

| Fact | Compiler / Metadata Source | Value for `Optional[Wrapped]` & `Optional::map` |
| --- | --- | --- |
| Package & file table | `SemanticPayloadWire::package_identifier`, `MetadataPayloadWire::file_table` | Package `"github.com/taro/std"`, file `"src/optional/optional.tr"` |
| Definition identity & kind | `ResolutionOutput::definition_to_kind` (`DefinitionID -> DefinitionKind`) | `Optional` -> `DefinitionKind::Enum`; `some`, `none` -> `DefinitionKind::Variant`; `map` -> `DefinitionKind::AssociatedFunction` |
| Parent hierarchy | `ResolutionOutput::definition_to_parent` | `Optional` parent -> module `std::optional`; `map` parent -> `Impl` block (`DefinitionKind::Impl`) |
| Declaration identifier & span | `ResolutionOutput::definition_to_ident` | `Identifier { symbol: "Optional", span: optional.tr:13:13..21 }`, `Identifier { symbol: "map", span: optional.tr:136:17..20 }` |
| Visibility | `ResolutionOutput::definition_to_visibility` | `Visibility::Public` on `Optional`, `some`, `none`, and `map` |
| Generic parameters | `TypeDatabase::def_to_generics` (`Generics`) | `Optional`: `[Wrapped (index 0)]`; `map`: `parent_count = 1`, own `[U (index 1), F (index 2)]` |
| Generic constraints (`where` & bounds) | `TypeDatabase::def_to_canonical_constraints` | `map`: `[Constraint::Bound { ty: F, interface: Fn[(Wrapped,), U] }]`; `Clone` conformance: `[Constraint::Bound { ty: Wrapped, interface: Clone }]` |
| Enum variants & payloads | `TypeDatabase::def_to_enum_def` (`EnumDefinition`) | `variants[0]`: `some`, `EnumVariantKind::Tuple([Wrapped])`; `variants[1]`: `none`, `EnumVariantKind::Unit` |
| Struct fields & metadata | `TypeDatabase::def_to_struct_def` (`StructDefinition`) | `StructField { name, ty, mutability, def_id, visibility, coding_key, coding_skip, default_provider }` |
| Function signature | `TypeDatabase::def_to_fn_sig` (`LabeledFunctionSignature`) | `inputs: [LabeledFunctionParameter { name: Some("self"), ty: Optional[Wrapped] }, LabeledFunctionParameter { name: None, ty: F }]`, `output: Optional[U]` |
| Inherent & specialized receivers | `TypeDatabase::def_to_ty` on `Impl` target | Distinguishes `extend[Wrapped] Optional[Wrapped]`, `extend[Wrapped: Clone] Optional[&Wrapped]`, and `extend[Wrapped] &Optional[Wrapped]` |
| Interface conformances | `TypeDatabase::conformance_records` (`ConformanceRecord`) | `Optional[Wrapped]: Default`, `Optional[Wrapped]: Clone where Wrapped: Clone` |
| Module exports & re-exports | `ScopeData::entries`, `ScopeData::glob_exports` | `std/src/prelude/prelude.tr` has `export std::optional::*` (`UsageKind::Export`) |

### 2.2 Missing Metadata (Gaps to Close for Implementation)

Tracing `compiler-cli/src/lib.rs`, `compiler/src/parse/lexer.rs`, `compiler/src/ast.rs`, and `compiler/src/metadata/wire.rs` identifies five concrete metadata gaps:

1. **Doc-comment attachment on AST, HIR, and `TypeDatabaseWire`**:
   - *Current state*: The lexer (`compiler/src/parse/lexer.rs`) skips line comments (`//` and `///`) without emitting tokens. `taro test --doc` (`compiler-cli/src/command/doctest.rs`) scans `.tr` files directly by line for contiguous `///` blocks.
   - *Required change*: Capture contiguous leading `///` lines (and their 1-based starting line numbers for doctest correlation) on `ast::Declaration`, `ast::AssociatedDeclaration`, `ast::FieldDefinition`, and `ast::Variant`, lower them into `TypeDatabase::def_to_doc_comment: FxHashMap<DefinitionID, DocComment>`, and persist them in `TypeDatabaseWire` so cross-package links and cached builds retain documentation.
2. **Internal parameter names for unlabeled (`_`) parameters**:
   - *Current state*: In `public func map[U, F: Fn[Wrapped, U]](_ f: F) -> Optional[U]`, `LabeledFunctionParameter.name` stores only the *external call label* (`None` because of `_`), while the internal parameter name `f` exists only in `ast::FunctionParameter.name` / `hir::FunctionParameter.name` and is dropped from `LabeledFunctionParameter`.
   - *Required change*: Add `internal_name: Symbol` (or `display_name: Option<Symbol>`) to `LabeledFunctionParameter` and `LabeledFunctionParameterWire` so rendered signatures show `(_ f: F)` instead of `(_ arg0: F)`.
3. **Preserving surface type-alias and sugar spellings in signatures**:
   - *Current state*: `TypeDatabase` stores lowered `Ty` values (e.g. `Optional[T]` for `T?`, and `Fn[(Wrapped,), U]` for `Fn(Wrapped) -> U` or `Fn[Wrapped, U]`).
   - *Required change*: Either format `Ty` using a doc-aware pretty-printer that renders `Fn[(A,), R]` as `Fn(A) -> R` and links nominal `DefinitionID`s to their HTML routes, or retain surface type trees from HIR for local package rendering.
4. **Attributes (`@deprecated`, `@NoCopy`) in `TypeDatabaseWire`**:
   - *Current state*: `gcx.attributes_of(def_id)` is populated in `Gcx` during source compilation (enabling `@deprecated` warnings in TAR-41), but `def_to_attributes` is not serialized in `TypeDatabaseWire`.
   - *Required change*: Serialize `@deprecated(message, replace)` and `@NoCopy` markers in `TypeDatabaseWire` so HTML reference pages render deprecation banners and badges for imported types as well as local declarations.
5. **Source declaration span (full item range) in `ResolutionOutput`**:
   - *Current state*: `definition_to_ident` stores the identifier span (`optional.tr:13:13..21`).
   - *Required change*: Record the full declaration span (e.g. `optional.tr:13:1..16:2`) in `TypeDatabase::def_to_span` so `[src]` links highlight the entire item in source view pages.

---

## 3. Worked HTML Page Outline (`std/optional/enum.Optional.html`)

Below is the worked page outline for `std::optional::Optional[Wrapped]`, showing the exact sections, signatures, member groupings, conformance listings, and executable example links that `taro doc std` will emit.

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>Optional in std::optional — Taro Standard Library Reference</title>
  <link rel="stylesheet" href="../../static/taro-doc.css">
</head>
<body>
  <nav class="sidebar">
    <div class="package-header">
      <a href="../../index.html">std</a>
      <span class="version">0.1.0</span>
    </div>
    <div class="module-nav">
      <h3>Module <a href="index.html">std::optional</a></h3>
      <h4>Enums</h4>
      <ul>
        <li class="current"><a href="enum.Optional.html">Optional</a></li>
      </ul>
      <h4>Functions</h4>
      <ul>
        <li><a href="fn.Some.html">Some</a></li>
        <li><a href="fn.None.html">None</a></li>
      </ul>
    </div>
  </nav>

  <main class="content">
    <!-- 1. Breadcrumb & Re-export Badges -->
    <header class="item-header">
      <div class="breadcrumbs">
        <a href="../../index.html">std</a> ::
        <a href="index.html">optional</a> ::
        <span>Optional</span>
      </div>
      <div class="badges">
        <span class="badge badge-prelude" title="Re-exported by std::prelude::*">
          Prelude
        </span>
      </div>
      <h1>Enum <span class="type-name">Optional</span>[<span class="type-param">Wrapped</span>]</h1>
      <a class="src-link" href="../../src/std/optional/optional.tr.html#L13-L16">[src]</a>
    </header>

    <!-- 2. Canonical Declaration Signature -->
    <pre class="item-decl"><code class="language-taro">public enum Optional[Wrapped] {
    case some(Wrapped)
    case none
}</code></pre>

    <!-- 3. Top-Level Prose Summary -->
    <section class="docblock">
      <p>An optional value that may or may not contain a wrapped value.</p>
      <p><code>Optional[T]</code> represents either <code>.some(value)</code> containing a value of type <code>T</code>,
      or <code>.none</code> representing the absence of a value.</p>
      <p>The shorthand syntax <code>T?</code> is equivalent to <code>Optional[T]</code>.</p>
    </section>

    <!-- 4. Enum Variants -->
    <section id="variants" class="variants-section">
      <h2>Variants</h2>
      <div id="variant.some" class="member-card">
        <div class="member-header">
          <code>case <a href="#variant.some" class="anchor">some</a>(<span class="type-param">Wrapped</span>)</code>
          <a class="src-link" href="../../src/std/optional/optional.tr.html#L14">[src]</a>
        </div>
      </div>
      <div id="variant.none" class="member-card">
        <div class="member-header">
          <code>case <a href="#variant.none" class="anchor">none</a></code>
          <a class="src-link" href="../../src/std/optional/optional.tr.html#L15">[src]</a>
        </div>
      </div>
    </section>

    <!-- 5. Inherent Methods (Grouped by Receiver / Extension Target & Constraints) -->
    <section id="methods" class="methods-section">
      <h2>Methods</h2>

      <!-- Group 5A: extend[Wrapped] Optional[Wrapped] -->
      <div class="impl-group" id="impl-Optional-Wrapped">
        <h3 class="impl-header">
          <code>extend[Wrapped] <a href="enum.Optional.html">Optional</a>[Wrapped]</code>
        </h3>

        <article id="method.new" class="member-card">
          <div class="member-header">
            <code>public static func <a href="#method.new">new</a>(_ wrapped: Wrapped) -&gt; Self</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L21-L23">[src]</a>
          </div>
          <div class="docblock"><p>Create an Optional containing the given value.</p></div>
        </article>

        <article id="method.isSome" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.isSome">isSome</a>() -&gt; bool</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L27-L32">[src]</a>
          </div>
          <div class="docblock"><p>Returns true if the optional contains a value.</p></div>
        </article>

        <article id="method.isNone" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.isNone">isNone</a>() -&gt; bool</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L36-L41">[src]</a>
          </div>
          <div class="docblock"><p>Returns true if the optional is empty.</p></div>
        </article>

        <article id="method.unwrap" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.unwrap">unwrap</a>() -&gt; Wrapped</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L89-L98">[src]</a>
          </div>
          <div class="docblock">
            <p>Returns the contained value, panicking if none.</p>
            <p>Panics with a generic message if the optional is none. Prefer <code>expect</code> if you want a custom panic message.</p>
          </div>
        </article>

        <article id="method.expect" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.expect">expect</a>(_ message: string) -&gt; Wrapped</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L101-L110">[src]</a>
          </div>
          <div class="docblock"><p>Returns the contained value, panicking with the given message if none.</p></div>
        </article>

        <article id="method.unwrapOr" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.unwrapOr">unwrapOr</a>(_ default: Wrapped) -&gt; Wrapped</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L114-L119">[src]</a>
          </div>
          <div class="docblock"><p>Returns the contained value or a default.</p></div>
        </article>

        <article id="method.unwrapOrElse" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.unwrapOrElse">unwrapOrElse</a>[F: <a href="../ops/interface.Fn.html">Fn</a>[(), Wrapped]](_ f: F) -&gt; Wrapped</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L122-L127">[src]</a>
          </div>
          <div class="docblock"><p>Returns the contained value or computes it from a closure.</p></div>
        </article>

        <!-- Worked Method with Linked Executable Example -->
        <article id="method.map" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.map">map</a>[U, F: <a href="../ops/interface.Fn.html">Fn</a>[Wrapped, U]](_ f: F) -&gt; <a href="enum.Optional.html">Optional</a>[U]</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L136-L141">[src]</a>
          </div>
          <div class="docblock">
            <p>Transforms the contained value using a function.</p>
            <p>Returns <code>.none</code> if the optional is none, otherwise returns <code>.some(f(value))</code>.</p>
            <div class="example-block" id="example-method.map-1"
                 data-doctest-id="std::optional::Optional::map#1"
                 data-doctest-source="src/optional/optional.tr:136">
              <div class="example-toolbar">
                <a class="example-anchor" href="#example-method.map-1">Example 1</a>
                <span class="doctest-cmd" title="Verify with taro test --doc">
                  <code>taro test std --doc --filter "optional.tr (line 136)"</code>
                </span>
              </div>
              <pre><code class="language-taro">x: int32? = .some(21)
doubled := x.map((v) =&gt; v * 2)
assert(doubled == .some(42))</code></pre>
            </div>
          </div>
        </article>

        <article id="method.flatMap" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.flatMap">flatMap</a>[U, F: <a href="../ops/interface.Fn.html">Fn</a>[Wrapped, <a href="enum.Optional.html">Optional</a>[U]]](_ f: F) -&gt; <a href="enum.Optional.html">Optional</a>[U]</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L146-L151">[src]</a>
          </div>
          <div class="docblock"><p>Transforms the contained value using a function that returns an Optional.</p></div>
        </article>

        <article id="method.filter" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.filter">filter</a>[F: <a href="../ops/interface.Fn.html">Fn</a>[&amp;Wrapped, bool]](_ predicate: F) -&gt; <a href="enum.Optional.html">Optional</a>[Wrapped]</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L154-L165">[src]</a>
          </div>
          <div class="docblock"><p>Returns the optional if it contains a value matching the predicate.</p></div>
        </article>

        <article id="method.and" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.and">and</a>[U](_ other: <a href="enum.Optional.html">Optional</a>[U]) -&gt; <a href="enum.Optional.html">Optional</a>[U]</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L172-L177">[src]</a>
          </div>
          <div class="docblock"><p>Returns <code>.none</code> if self is <code>.none</code>, otherwise returns <code>other</code>.</p></div>
        </article>

        <article id="method.or" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.or">or</a>(_ other: Self) -&gt; Self</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L183-L188">[src]</a>
          </div>
          <div class="docblock"><p>Returns the option if it contains a value, otherwise returns <code>other</code>.</p></div>
        </article>

        <article id="method.orElse" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.orElse">orElse</a>[F: <a href="../ops/interface.Fn.html">Fn</a>[(), Self]](_ f: F) -&gt; Self</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L192-L197">[src]</a>
          </div>
          <div class="docblock"><p>Returns the option if it contains a value, otherwise calls <code>f</code> and returns the result.</p></div>
        </article>
      </div>

      <!-- Group 5B: Specialized / Borrowed-Payload Extensions -->
      <div class="impl-group" id="impl-Optional-Ref-Wrapped-Clone">
        <h3 class="impl-header">
          <code>extend[Wrapped: <a href="../marker/interface.Clone.html">Clone</a>] <a href="enum.Optional.html">Optional</a>[&amp;Wrapped]</code>
        </h3>
        <article id="method.cloned" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.cloned">cloned</a>() -&gt; <a href="enum.Optional.html">Optional</a>[Wrapped]</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L64-L69">[src]</a>
          </div>
          <div class="docblock"><p>Converts an <code>Optional[&amp;Wrapped]</code> into an <code>Optional[Wrapped]</code> by cloning the referenced value.</p></div>
        </article>
      </div>

      <div class="impl-group" id="impl-Optional-Ref-Wrapped">
        <h3 class="impl-header">
          <code>extend[Wrapped] <a href="enum.Optional.html">Optional</a>[&amp;Wrapped]</code>
        </h3>
        <article id="method.copied" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.copied">copied</a>() -&gt; <a href="enum.Optional.html">Optional</a>[Wrapped]</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L75-L80">[src]</a>
          </div>
          <div class="docblock"><p>Converts an <code>Optional[&amp;Wrapped]</code> into an <code>Optional[Wrapped]</code> by copying the referenced value.</p></div>
        </article>
      </div>

      <!-- Group 5C: Reference Receiver Extension (`extend &T`) -->
      <div class="impl-group" id="impl-Ref-Optional-Wrapped">
        <h3 class="impl-header">
          <code>extend[Wrapped] &amp;<a href="enum.Optional.html">Optional</a>[Wrapped]</code>
        </h3>
        <article id="method.take" class="member-card">
          <div class="member-header">
            <code>public func <a href="#method.take">take</a>() -&gt; <a href="enum.Optional.html">Optional</a>[Wrapped]</code>
            <a class="src-link" href="../../src/std/optional/optional.tr.html#L212-L216">[src]</a>
          </div>
          <div class="docblock"><p>Takes the value out of the optional, leaving a <code>.none</code> in its place.</p></div>
        </article>
      </div>
    </section>

    <!-- 6. Interface Conformances -->
    <section id="conformances" class="conformances-section">
      <h2>Interface Conformances</h2>

      <div class="impl-group" id="conform-Default">
        <h3 class="impl-header">
          <code>conform[Wrapped] <a href="enum.Optional.html">Optional</a>[Wrapped] to <a href="../default/interface.Default.html">Default</a></code>
          <a class="src-link" href="../../src/std/optional/optional.tr.html#L44-L48">[src]</a>
        </h3>
        <article id="method.default" class="member-card">
          <code>public static func <a href="#method.default">default</a>() -&gt; Self</code>
        </article>
      </div>

      <div class="impl-group" id="conform-Clone">
        <h3 class="impl-header">
          <code>conform[Wrapped] <a href="enum.Optional.html">Optional</a>[Wrapped] to <a href="../marker/interface.Clone.html">Clone</a> where Wrapped: <a href="../marker/interface.Clone.html">Clone</a></code>
          <a class="src-link" href="../../src/std/optional/optional.tr.html#L52-L59">[src]</a>
        </h3>
        <article id="method.clone" class="member-card">
          <code>public func <a href="#method.clone">clone</a>() -&gt; Self</code>
        </article>
      </div>
    </section>
  </main>
</body>
</html>
```

---

## 4. Explicit Inclusion Rules

### 4.1 Top-Level and Namespace Declarations

| Declaration Visibility | Default Mode (`taro doc`) | Private Mode (`taro doc --document-private-items`) |
| --- | --- | --- |
| `public` | **Included** (own page or module section entry) | **Included** |
| `internal` (package-default on declarations) | **Excluded** unless publicly re-exported | **Included** with `<span class="badge">internal</span>` |
| `private` | **Excluded** | **Included** with `<span class="badge">private</span>` |
| Compiler synthetic definitions (`$field_default`, adapters, test/fuzz harnesses) | **Excluded** (filtered by `gcx.is_synthetic_definition(id)`) | **Excluded** |
| Internal `@lang(...)` runtime hooks without `public` (e.g. `assertFail`, `debugValueAt`) | **Excluded** | **Included** with `@lang` badge |
| `@test`, `@bench`, and `@fuzz` functions | **Excluded** from API reference | **Excluded** |

### 4.2 Re-exports (`export`)

1. **Public re-export of a public declaration (`export std::optional::Optional` or `export std::optional::*`)**:
   - The canonical HTML page lives at the defining module path (`std/optional/enum.Optional.html`) when the defining module is itself public.
   - The re-exporting module (`std/index.html` or `std/prelude/index.html`) lists the item under a **"Re-exports"** section (`pub export std::optional::Optional`) linking to the canonical page.
   - If the re-export uses an alias (`export std::collections::Dictionary as Map`), the re-exporting module lists `Map` as an alias re-export linking to `std/collections/struct.Dictionary.html`.
   - Any item re-exported by `std::prelude` receives a **`Prelude`** badge on its canonical page.
2. **Public re-export of an `internal` or private-module declaration (Facade Pattern)**:
   - When an item is defined inside a non-public module or namespace and exposed publicly via `export internal_mod::PublicType`, `taro doc` **inlines** the full reference page at the public export path so the generated documentation has no broken links to hidden modules.
3. **Non-public imports (`import foo::bar`)**:
   - Ordinary `import` declarations are never rendered in reference output.

### 4.3 Members (Fields, Variants, Methods, Properties, Associated Types, Conformances)

1. **Struct and Class Stored Fields**:
   - In default mode, only `Visibility::Public` fields are rendered in the declaration block and **"Fields"** section.
   - If a public struct or class has one or more `internal` or `private` stored fields that are hidden in default mode, the rendered declaration block appends `/* private fields */` at the end of the brace body so readers can see that direct struct literal construction is restricted outside the defining scope.
   - Field-level `@key("...")` and `@skip` attributes (TAR-53) are rendered above the field in the declaration summary when present.
2. **Enum Variants and Payloads**:
   - All variants of a public enum are public and rendered in declaration order with their tuple or record payload types.
3. **Inherent Extension Members (`extend T` and `extend &T`)**:
   - An `extend` block on a documented type `T` is rendered if it contains at least one visible member (`public` in default mode; any visibility with `--document-private-items`).
   - Methods, computed properties (`var prop: Type { get }`), subscripts, and associated constants are grouped under their `extend` header (`extend[Wrapped: Clone] Optional[&Wrapped]`, `extend[Wrapped] &Optional[Wrapped]`), preserving generic bounds and receiver reference sigils (`&`).
4. **Interface Requirements and Conformances (`conform T to I`)**:
   - On an interface page (`interface.I.html`), all required methods, properties, subscripts, associated types, and default methods are listed, along with all known public **Implementors**.
   - On a type page (`struct.T.html` / `enum.T.html` / `class.T.html`), a `conform T to I` block is included if both `T` and `I` are visible in the current documentation mode, showing any `where` constraints (`where Wrapped: Clone`) and the implemented interface methods (even when individual conformance methods omit a redundant `public` keyword).
   - Compiler-synthesized inline derivations (`struct User: Debug, Codable, PartialEq`) are listed under **"Derived Conformances"** with their conditional bounds (`where A: Debug, B: Debug`).

---

## 5. Proposed CLI Command, Output Layout, and Example Linking Scheme

### 5.1 Proposed CLI Subcommand (`compiler-cli/src/lib.rs`)

Add `Doc(DocArgs)` to `CliCommand`:

```sh
taro doc [PATH] [OPTIONS]
```

| Flag / Argument | Default | Description |
| --- | --- | --- |
| `[PATH]` | `.` | Package directory, single `.tr` file, or `std` (resolved via `TARO_HOME` / `--std-path` just like `taro test std`) |
| `--output <DIR>` / `-o <DIR>` | `<package-root>/target/doc` | Output directory for generated HTML files |
| `--document-private-items` | `false` | Include `internal` and `private` modules, types, fields, and methods |
| `--no-deps` | `false` | Document only the target package without generating pages for `[require]` dependencies |
| `--open` | `false` | Open `<output>/<package>/index.html` in the system browser after generation |
| `--format <html\|json>` | `html` | Emit static HTML pages (`html`) or a machine-readable JSON documentation model (`json`) for tooling and acceptance tests |

### 5.2 Deterministic File & URL Layout

```text
<output>/
  static/
    taro-doc.css
    search.js
  search-index.json
  std/
    index.html                          # Package root overview & top-level functions/modules
    optional/
      index.html                        # Module std::optional overview
      enum.Optional.html                # enum Optional[Wrapped]
      fn.Some.html                      # func Some[T](_ value: T) -> T?
      fn.None.html                      # func None[T]() -> T?
    collections/
      index.html
      struct.List.html                  # struct List[T]
      struct.Dictionary.html            # struct Dictionary[K, V]
  src/
    std/
      optional/
        optional.tr.html                # Line-numbered source view (#L1-L217)
```

Kind prefixes in filenames follow a deterministic namespace-collision-free convention:
- `struct.<Name>.html`
- `class.<Name>.html`
- `enum.<Name>.html`
- `interface.<Name>.html`
- `type.<Name>.html` (type aliases)
- `fn.<Name>.html` (free functions; overloaded free functions share `fn.<Name>.html` with `#overload-<n>` anchors)
- `const.<Name>.html` (constants)

### 5.3 Linking Scheme Between HTML Pages and Executable Examples (`taro test --doc`)

Every fenced ```` ```taro ```` code block inside a `///` doc comment has two deterministic coordinates:
1. **Source coordinate** (used by `taro test --doc` today in `compiler-cli/src/command/doctest.rs`):
   - `<relative_file_path> (line <fence_line>)`, e.g., `src/optional/optional.tr (line 136)`.
2. **Semantic item coordinate** (assigned when `///` comments are attached to `DefinitionID`):
   - `<qualified_item_path>#<1-based_example_index>`, e.g., `std::optional::Optional::map#1`.

In the generated HTML page:
- The example container receives `id="example-method.map-1"` (or `id="example-type-1"` for type-level examples), `data-doctest-id="std::optional::Optional::map#1"`, and `data-doctest-source="src/optional/optional.tr:136"`.
- The example header links directly to the source line (`../../src/std/optional/optional.tr.html#L136`) and displays the exact `taro test --doc --filter` invocation that executes that example.
- Extending `taro test --doc --filter` to match both `<file> (line <N>)` and `<qualified_item_path>` lets users copy either `taro test std --doc --filter std::optional::Optional::map` or the line filter directly from the HTML page.

---

## 6. Acceptance Fixture Specification for Future Implementation

To validate the future `taro doc` implementation end-to-end without depending on the entire standard library in every unit test, add a dedicated fixture package `language_tests/doc_fixture/`:

```text
language_tests/doc_fixture/
  package.toml
  src/
    lib.tr
    internal_box.tr
```

### `language_tests/doc_fixture/package.toml`

```toml
[package]
name = "example.com/taro/doc_fixture"
version = "0.1.0"
kind = "library"
```

### `language_tests/doc_fixture/src/internal_box.tr`

```taro
/// A generic container defined in an internal file and re-exported at the root.
///
/// ```taro
/// b := doc_fixture::Box[int32]::new(7, "tag")
/// assert(b.map((x) => x + 1).get() == 8)
/// ```
public struct Box[T]: Debug, PartialEq {
    /// The wrapped public value.
    public value: T
    internal tag: string
    private secretNonce: int32 = 99
}

extend[T] Box[T] {
    /// Construct a new `Box[T]`.
    public static func new(_ value: T, _ tag: string) -> Box[T] {
        Box { value, tag, secretNonce: 99 }
    }

    /// Return a copy of the wrapped value.
    public func get() -> T {
        self.value
    }

    /// Transform the boxed value using `f`.
    ///
    /// ```taro
    /// b := doc_fixture::Box[int32]::new(20, "math")
    /// mapped := b.map((v) => v * 2)
    /// assert(mapped.get() == 40)
    /// ```
    public func map[U, F: Fn[T, U]](_ f: F) -> Box[U] {
        Box[U] { value: f(self.value), tag: self.tag, secretNonce: self.secretNonce }
    }

    internal func internalTag() -> string {
        self.tag
    }

    private func nonce() -> int32 {
        self.secretNonce
    }
}
```

### `language_tests/doc_fixture/src/lib.tr`

```taro
export doc_fixture::internal_box::Box

/// Internal helper that must NOT appear in default `taro doc` output.
internal func hiddenHelper() -> int32 { 42 }

@deprecated(message = "use Box::new instead", replace = "Box::new")
public func legacyMakeBox(_ v: int32) -> Box[int32] {
    Box[int32]::new(v, "legacy")
}
```

### Acceptance Assertions on `language_tests/doc_fixture`

1. `taro test language_tests/doc_fixture --doc` runs and passes both executable examples (`Box` type example and `Box::map` method example).
2. `taro doc language_tests/doc_fixture -o $TMPDIR/doc_out`:
   - Generates `doc_fixture/index.html`, `doc_fixture/struct.Box.html`, and `doc_fixture/fn.legacyMakeBox.html`.
   - `struct.Box.html` contains:
     - Declaration `public struct Box[T]` with `public value: T` and `/* private fields */` (omitting `internal tag` and `private secretNonce`).
     - Public methods `new`, `get`, and `map[U, F: Fn[T, U]](_ f: F) -> Box[U]`, while omitting `internalTag` and `nonce`.
     - Derived conformances `Debug` and `PartialEq`.
     - Both rendered example blocks with `id="example-type-1"` and `id="example-method.map-1"` and their `data-doctest-source` attributes.
   - `fn.legacyMakeBox.html` displays the `@deprecated` banner (`use Box::new instead`).
   - `hiddenHelper` does **not** appear in `index.html` or any generated page.
3. `taro doc language_tests/doc_fixture --document-private-items -o $TMPDIR/doc_priv_out`:
   - Includes `internal tag: string`, `private secretNonce: int32`, `internalTag()`, `nonce()`, and `fn.hiddenHelper.html` with `internal`/`private` badges.
