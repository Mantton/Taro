# Declarations

This chapter describes top-level and nested declarations in Taro. Declaration
examples without `main` can be checked with an empty `func main() {}` appended.
Examples that continue earlier definitions are identified in the surrounding text.

## Visibility

Declarations are public by default. Use `internal` for access throughout the
defining package, including sibling modules. Use `private` for the containing
scope; type-private fields are also accessible to the type's owned extensions.

```taro
public struct PublicType { }    // Accessible everywhere
internal struct PackageType { } // Accessible inside this package
private struct PrivateType { }  // Private to this module
struct DefaultPublicType { }    // Public when no modifier is present

public func publicFunction() { }
private func privateFunction() { }
```

## Attributes

Attributes provide metadata for declarations.

```taro
@inline
func fastFunction() { }

@noinline
func separateFunction() { }
```

`@discardableResult` lets callers ignore a function's `Result` without the
unused-Result warning (see
[Unused Results](expressions.md#unused-results)). It is allowed on functions,
methods and interface requirements that return `Result`, and takes no
arguments:

```taro
@discardableResult
func log(_ line: string) -> Result[(), Error] { ... }
```

`@NoCopy` marks a nominal type for the opt-in `taro vet` command:

```taro
@NoCopy
struct State { value: int32 }
```

Vet reports value copies and by-value parameters of annotated types, including
inline structs, tuples, arrays and enum payloads containing them. Share
references instead. Unmarked class and collection handles copy normally because
they share their targets. Fresh construction and returned values can initialize
new bindings. Store references to NoCopy values in collections.

This attribute adds no fields, runtime checks or language copy restriction.
Normal `check`, `build` and `run` preserve ordinary value semantics. Vet is an
advisory source check, not an ownership or synchronization guarantee; it does not
prove the safety of arbitrary generic or unsafe operations. Findings use warning
diagnostics and give `taro vet` a nonzero exit status. Vet also reports
shadowing that hides a later read; see [Local Bindings](#local-bindings).

`@deprecated` marks a declaration as deprecated and emits a warning at every use
site, including across package boundaries:

```taro
@deprecated("use computeV2", replace = "computeV2")
func computeV1(_ x: int64) -> int64 { x }

@deprecated("migrate manually", replace = "newApi", advisory)
func oldApi() -> int64 { 0 }

@deprecated("legacy only")
func legacyHelper() -> int64 { 0 }
```

When `replace = "newName"` is a simple identifier and `advisory` is omitted, the
compiler attaches a machine-applicable rename suggestion. Run `taro fix` (or
`taro fix --dry-run`) to apply machine-applicable suggestions in place while
leaving advisory and message-only warnings untouched.

---

## Local Bindings

Every local binding is mutable. `name := expression` declares an inferred
local, and `var name: Type = expression` (or `var name: Type`, assigned before
use) declares one with an explicit type; `var` also introduces tuple and
wildcard patterns. `let` was removed and reports an error suggesting the
replacement. A shorthand declaration creates a new binding, including when its
name shadows an earlier one. Use `=` to update an existing binding. Shorthand
is not available for globals or conditional bindings.

`_ := expression` evaluates and discards its result, like `var _ = expression`,
without declaring a name. It may be repeated in the same scope.

Because `:=` always declares, writing it where an assignment was meant
silently leaves the outer binding unchanged. `taro vet` reports a `:=` or
`var` declaration that shadows a local or parameter of the same function when
that outer binding is read after the declaration's scope ends:

```taro
func load(_ verbose: bool) -> int32 {
    config := 1
    if verbose {
        config := 2     // vet: 'config' shadows the variable declared on
    }                   // line 2, which is read after this scope ends
    return config       // still 1
}
```

Write `config = 2` to update the outer binding, or rename the inner one. Vet
does not report a redeclaration in the same scope, shadowing whose outer
binding is not read afterwards, the bindings of `if var`, `guard var`, `while
var`, `for` and `match` patterns, or a closure's declarations. Like the
`@NoCopy` checks, findings are warnings that give `taro vet` a nonzero exit
status; `check`, `build` and `run` do not report shadowing.

Optional conditions are written `if var`, `while var` and `guard var`. All
`case` bindings are writable value copies; `case var` has the same behavior. Conditions may join bindings with `&&`, making
earlier bindings available to later conditions. Write bindings directly in the
condition or its `&&` chain, without wrapping a binding in parentheses. Bindings under `||`,
negation, or ordinary function-call arguments are rejected.

```taro
func main() {
    count := 0 // inferred mutable int32
    var source: int32? = .some(2)
    if var value = source && value > 0 {
        value += 1
        count = value
    }
    guard var value = source else { return }
    assert(count == 3 && value == 2, "independent value bindings")
}
```

---

## Struct Declaration

Structs define nominal value types with named or positional fields.

```taro
// Basic struct
struct Point {
    x: int32;
    y: int32;
}

// With visibility on fields
struct User {
    public name: string;
    internal cacheKey: int32; // Accessible only inside this package.
    private password: string; // Accessible to the type and its owned extensions.
}

// Readonly fields (immutable after construction)
struct Config {
    readonly version: int32;
    readonly name: string;
}

// Generic struct
struct Box[T] {
    value: T;
}

// Multiple generics
struct Pair[A, B] {
    first: A;
    second: B;
}
```

### Struct Layout (`@repr`)

Struct layout representation can be selected with `@repr("...")`:

```taro
// Default if omitted: @repr("Taro")
@repr("Taro")
struct PackedPoint {
    x: int8;
    y: int64;
    z: int8;
}

// C-compatible declaration-order layout
@repr("C")
struct CHeader {
    tag: uint16;
    len: uint32;
}
```

- `@repr("Taro")`: optimization-oriented layout (field order is not source-stable).
- `@repr("C")`: standard C-style declaration-order layout for FFI-sensitive types.

---

### Positional structs

Give each field’s type in parentheses to declare a nominal struct with
positional fields. Use parentheses for construction and patterns. Fields
are writable through a mutable receiver and inherit the type’s visibility.

```taro
struct UserId(int64): PartialEq
struct OrderId(int64)
struct Pair[T](T, T)

id := UserId(42)
raw := id.0
var pair: Pair[int64] = Pair(2, 5)
pair.1 += 1
var Pair(first, second) = pair
```

A function accepting `UserId` requires that nominal type. The separate
`OrderId` and the underlying `int64` each require explicit construction to
produce a `UserId`. A one-field struct has its field’s size and alignment.
Derived conformances follow the same field requirements as named structs.
Declaring an explicit initializer replaces the synthesized positional
constructor. Its body can initialize fields by position, as in `self.0 = raw`.

### Nested types in extensions

An inherent extension can declare a struct, enum, class, or interface inside a
nominal type in the same package. Use the owner's name to qualify it. All
instantiations of a generic owner share the same nested declaration.

```taro
struct Queue[T] { value: T }
extend Queue {
    public enum State { case ready, closed }
    struct Entry[V](V)
}

func initial() -> Queue::State { .ready }
entry := Queue::Entry[int64](5000000000)
```

A nested type declares its own generic parameters. Extension parameters are
outside its scope. Sibling declarations can refer to each other by name. A
caller needs visibility of both the owner and the nested type. The same paths
work in package signatures and imports, such as `import dep::Queue::State`.

## Enum Declaration

Enums define sum types with multiple variants.

```taro
// Simple enum (unit variants)
enum Color {
    case red, green, blue;
}

// With explicit discriminants
enum Status {
    case ok = 0, err = 1;
}

// Associated values (tuple variants)
enum Result[T, E] {
    case ok(T), err(E);
}

// Mixed variants
enum Message {
    case quit;                     // Unit variant
    case move(x: int32, y: int32); // Named fields
    case write(string);            // Positional field
}

// Multiple case statements
enum Direction {
    case north;
    case south;
    case east, west;
}
```

Payload-free enums can opt into `CaseIterable` to enumerate their cases and
read each case's declared name. Each call to `iter()` starts at the first
case. An empty enum yields no cases.

```taro
enum Signal: CaseIterable, RawValue[uint8] { case stop = 90, go = 2 }

for signal in Signal::ALL_CASES { println(signal.name) } // stop, then go
raw := Signal::go.rawValue                              // 2
signal := Signal::from(rawValue: 90)                     // .some(.stop)
```

`RawValue` can be adopted separately. Its integer type must fit all declared
discriminants. Lookup of a missing raw value returns `.none`.

---

### Named Enum Payloads

A case may declare payload fields with braces. The field names become constructor
argument labels; matching uses declaration order, like labeled tuple payloads.
Fields may be separated by commas or newlines. Duplicate names are rejected.
Payload fields inherit their variant’s visibility; `public`, `private`, and
`internal` modifiers on individual payload fields are rejected.
`readonly` prevents direct assignment to the stored field. Pattern bindings are
writable value copies, including when the match target is a reference. Copied
class and reference values still share their targets.

```taro
enum Event {
    case click { readonly x: int32, y: int32 }
}

func main() {
    var event: Event = Event::click { y: 4, x: 2 }
    match &event {
        case .click { x, y } => {
            // x: int32; y: int32. These are local copies.
            assert(x == 2, "copied payload")
            y = 5
            assert(y == 5, "only the copy changes")
        }
    }
}
```

---

### Delegating through a stored field

Use `by self.field` on a conformance to forward instance requirements to a
stored value. An explicit method takes precedence for its matching signature.
Other overloads continue to forward through the field.

```taro
interface Gauge {
    func read() -> int32
    func offset() -> int32
}
struct Wrapper { inner: any Gauge }
conform Wrapper to Gauge by self.inner {
    func read() -> int32 { self.inner.read() + 1 }
}
```

Here `offset()` calls the implementation held in `inner`. Calls through
`any Gauge` and a generic `G: Gauge` use the same wrapper witnesses.
Use a reference conformance such as `conform &Counter to Meter by self.inner`
when a forwarded call must mutate storage inside a value type. Place a
conditional conformance’s `where` clause after the field. Implement a
requirement that returns the wrapper’s own `Self` explicitly when the
field’s method returns a different type.

## Derived Conformances

Listing one of these standard interfaces in a struct or enum's conformance
list, with no implementation, asks the compiler to synthesize it:

| Interface | Synthesized member | Recipe |
| --- | --- | --- |
| `Clone` | `clone()` | Clone each stored field or payload. |
| `CaseIterable` | `name`, `caseAt(_:)` | Return the case identifier and look up a case by its zero-based declaration index. `ALL_CASES` provides iteration. |
| `RawValue[Raw]` | `rawValue`, `from(rawValue:)` | Read and look up a payload-free enum's integer discriminants. |
| `PartialEq`, `Equatable` | `eq(_:)` | Fields equal in order; enum values need the same case and equal payloads. |
| `Hashable` | `hash(into:)` | Hash each field; enum values also hash their case. |
| `Encodable`, `Decodable` | `encode(into:)`, `decode(from:)` | Field-by-field codec; `Codable` lists both. |
| `PartialOrd` | `partialCmp(_:)` | Compare fields in declaration order with their own `partialCmp`; the first result that is not `.some(.equal)` is the answer, so a `.none` ends the comparison. |
| `Ord` | `cmp(_:)` | Compare fields in order with their own `cmp`; the first result that is not `.equal` is the answer. |
| `Default` | `static default()` | Each field's declared `= expression` default, or else its type's `Default::default()`. Structs only. |
| `Debug` | `debug(_:)` | A struct writes `Name { field: value }`, or `Name` without fields; an enum writes its case name and payload. Each field uses its own `debug`. |

Enums order their cases by declaration order. Two values of the same case
compare their payloads in order, positional or named; cases without payloads
equal themselves. `Comparable` is `PartialEq & PartialOrd & Ord`, and like
`Codable` it can be listed directly:

```taro
struct Version: Comparable {
    major: int32
    minor: int32
}

enum Priority: Comparable { case low, normal, high }

struct Settings: Default {
    retries: int32 = 3     // a declared default wins
    name: string           // otherwise string's default, ""
    tags: [string]         // and an empty list
}

func main() {
    var releases: [Version] = [Version { major: 2, minor: 0 }, Version { major: 1, minor: 4 }]
    releases.sort()                    // uses the derived Ord
    newer := releases[0] < releases[1] // operators use PartialOrd
    empty := Settings::default()
    println("${newer} ${empty.retries}")   // true 3
}
```

A derived `Debug` omits generic arguments, and an enum value writes its case
without the enum's name: `quit`, `key('a')`, `resize(width: 3, height: 4)` and
`click { x: 1, y: 2 }`. String and rune fields are quoted and escaped the way
a literal is written:

```taro
struct Person: Debug {
    name: string
    tags: [string]
    manager: string?
}

func main() {
    var tags: [string] = ["x", "y"]
    ada := Person { name: "Ada", tags, manager: .none }
    println("${ada}") // Person { name: "Ada", tags: ["x", "y"], manager: none }
}
```

Every stored field, or every enum payload, must conform to the interface being
derived; `Default` checks only the fields without a declared default. The
error names the type, the field and the missing interface. A `double` field
supports `PartialOrd` but not `Ord`, because NaN is unordered. Generic types
conform conditionally: `Pair[T]: Comparable` is `Ord` exactly when `T` is.

A derived interface never derives its super-interfaces. `Ord` needs
`PartialOrd` and `PartialEq`, and `Hashable` needs `PartialEq`, each either
listed as well or implemented in a `conform` block. A hand-written
`partialCmp` beside a derived `cmp`, or the reverse, is allowed; keeping the
two consistent is the author's job. To implement one of these interfaces by
hand, write a `conform` block instead of listing it.

`Clone`, `PartialEq` and `Hashable` are also derived for final classes, and the
codecs for classes. `PartialOrd`, `Ord`, `Default` and `Debug` are derived for
value types only: listing them on a class, or `Default` on an enum, is an error.
A class may reach itself through its fields, so its `Debug` text is written by
hand, where the author decides how to cut a cycle.

## Interface Declaration

Interfaces define contracts that types can implement.

```taro
// Basic interface
interface Drawable {
    func draw();
}

// With return types
interface Cloneable {
    func clone() -> Self;
}

// Interface inheritance
interface Equal {
    func equal(other: &Self) -> bool;
}

interface Comparable: Equal {
    func compare(other: &Self) -> int32;
}

// Associated types
interface Container {
    type Item;
    func get() -> Self::Item?;
}

// Associated constants
interface Named {
    const NAME: string;
}

// Multiple methods
interface Collection {
    type Element;
    func count() -> int32;
    func isEmpty() -> bool;
    func contains(element: Self::Element) -> bool;
}
```

Superinterfaces may be local or imported, including standard interfaces such
as `Clone` and `Equatable`. Cyclic superinterface requirements, including direct
self-inheritance, are rejected.

Interfaces may require computed properties and may provide default accessor
bodies. A conforming type can satisfy an accessor with a stored field, an
inherent computed property, or an accessor declared in the conformance:

```taro
interface Counted {
    var count: int32 {
        get
    };
}

interface DefaultCount {
    var count: int32 {
        get { 0 }
    };
}
```

If multiple interfaces expose the same property name, qualify the access with
the interface when the receiver type does not identify a unique candidate.

---

## Function Declaration

Functions are the primary units of code.

```taro
struct Point {
    x: int32;
    y: int32;
}

// Basic function
func greet() {
    print("Hello!")
}

// With parameters
func add(a: int32, b: int32) -> int32 {
    return a + b
}

// Labeled parameters
func move(from source: Point, to destination: Point) {
    // 'from' and 'to' are external labels
    // 'source' and 'destination' are internal names
}

// Default parameter values
func greetPerson(name: string = "World") {
    print("Hello, " + name)
}

// Variadic parameters
func sum(_ nums: int32...) -> int32 {
    // nums is a Span[int32]; iteration produces element values.
    var total = 0
    for n in nums { total += n }
    return total
}

// Generic functions
func identity[T](value: T) -> T {
    return value
}

// With where clause
func compare[T](a: T, b: T) -> bool where T: Equatable {
    return a == b
}

// Async functions place `async` after the parameter list
func loadCount() async -> int32 { 42 }

func fetchCount() async -> int32 {
    return await loadCount()
}

func main() {
    origin := Point { x: 0, y: 0 }
    move(from: origin, to: Point { x: 1, y: 2 })
    greetPerson()
    result := add(a: 1, b: sum(2, 3, 4))
    println("${result}")
}
```

Parameter names are also argument labels unless `_` suppresses the label.
A separate label, as in `from source: Point`, keeps the external and internal
names distinct. Variadic parameters must be last and cannot have defaults.

A parameter declared `@lazy T` receives a zero-argument closure. Supply an
ordinary expression at the call site. Each invocation in the function body
evaluates that expression, using the same capture rules as a handwritten
closure. An unused argument never runs. For example, `assert(ready, describe())`
calls `describe()` only if the assertion fails. The current compiler boxes the
closure at the call site, which can allocate even when the callee skips it.

```taro
func fallback(_ value: int32?, or other: @lazy int32) -> int32 {
    match value {
        case .some(number) => number
        case .none => other()
    }
}
```

A postfix `...` feeds an iterable's elements into a variadic parameter.
For example, `sum(1, values..., 4)` consumes `values` once between the two
scalar arguments. Each item receives the usual conversion to the parameter's
element type. A collection passed without `...` supplies one argument.

A sole spread whose static type is the matching `Span[T]` forwards its
storage to a `T...` parameter. A write through the callee's span is visible through the original
span. Mixed contributions, abstract `Iterable` parameters and sources requiring
element conversion produce a fresh pack. A function can return that pack's span.

Instance methods omit `self` from their parameter lists. The declaration
containing the method determines its receiver:

| Target | Implicit `self` |
| --- | --- |
| Struct `T` | A writable local copy of the value |
| `&T` | A reference to existing storage |
| Class `C` | A copied handle to the shared object |

```taro
interface Increment {
    func increment()
}

struct Counter { count: int32 }
extend Counter {
    static func zero() -> Counter { Counter { count: 0 } }
    func value() -> int32 { self.count }
    func changeCopy() { self.count += 1 }
}
conform &Counter to Increment {
    func increment() { self.count += 1 }
}

func update[T: Increment](_ value: T) { value.increment() }
func main() {
    counter := Counter::zero()
    counter.changeCopy() // changes the receiver copy
    counter.increment() // automatically takes &counter
    update(&counter)    // the reference itself satisfies Increment
}
```

A method declared on `T` takes priority over an automatic reference to `T`.
Automatic references require an addressable variable, stored field or element;
a call such as `makeCounter().increment()` does not invent writable storage.
A conformance of `&T` does not make `T` conform. For classes, `&C` refers to the
slot holding a handle and can replace that handle; methods on `C` act on the
shared object. `value.clone()` clones the value itself and requires its `Clone`
conformance. To copy a reference, write `(&value).clone()`; automatic referencing
does not silently change a value clone into a reference copy.

Applicable inherent methods take priority over visible interface methods. If
their inputs do not apply, interface requirements and defaults remain available.
Calls and saved method values follow the same lookup rules. Inherited instance
and static overloads remain visible; a subclass static declaration hides only
the inherited declaration with the same input signature.

Within a candidate group, the candidate whose arguments need the fewest
conversions, such as class upcasts, optional wrapping and interface boxing,
wins, so exact argument types take priority. A concrete declaration wins over a
generic declaration only when their conversion costs tie. If they still tie, the
candidate that boxes fewer arguments into an `any` existential wins, because it
keeps their concrete types. Any remaining tie is an ambiguity error. Overload
selection uses static argument types; virtual dispatch then picks the override
of the selected method. Return types alone cannot distinguish overloads, even
when the declarations are never called.

```taro
interface Show {}
conform usize to Show {}

func describe(_ value: usize?) -> string { "optional" }
func describe(_ value: any Show) -> string { "existential" }

func main() {
    var count: usize = 3
    println(describe(count))    // optional: one wrap, no boxing
}
```

Use `static func` for receiver-free factories and requirements. Explicit `self`
and `&self` function parameters are rejected. Free functions retain their normal
parameter lists. Methods that need their receiver's storage belong in
`extend &T` or `conform &T`. Unrelated members belong in `extend`, rather than
a `conform` body.

### Entry Point

An executable's `main` takes no parameters and has one of these forms, each of
which may be `async`:

- `func main()`: the program exits with status 0 when `main` returns.
- `func main() -> Result[(), E]`: returning `.ok(())` exits with status 0.
  Returning `.err(error)` writes `error: ` and the error's display form, and a
  newline, to standard error, and the program exits with status 1.

`E` must be printable the way string interpolation prints a value: it must
conform to `std::fmt::Display`, or be an existential such as
`any std::error::Error` whose interfaces include `Display`. Postfix `!` works in
`main` as in any other function returning `Result`, including boxing a concrete
error into `any std::error::Error`:

```taro
struct ConfigError {
    key: string
}

conform ConfigError to std::fmt::Display {
    func display(_ into: &std::fmt::Formatter) {
        into.writeString("missing setting '${self.key}'")
    }
}

conform ConfigError to std::error::Error {}

func setting(_ key: string) -> Result[int32, ConfigError] {
    if key == "workers" {
        return .ok(4)
    }
    return .err(ConfigError { key })
}

func main() -> Result[(), any std::error::Error] {
    workers := setting("workers")!
    print("workers: ${workers}\n")
    var _ = setting("timeout")! // prints `error: missing setting 'timeout'`, exits 1
    return .ok(())
}
```

The error is reported after `main` and its `defer` blocks have run, and after
everything `main` wrote to standard output. The program then exits as it does
when a unit `main` returns, with no backtrace. A panic in `main` is reported and
exits as it does for a unit `main`. `taro run` exits with the program's status.
Any other return type, or parameters on `main`, is a compile error.

---

## Implementation Declaration

Implementations add functionality to existing types.

```taro
struct Point {
    x: int32;
    y: int32;
}

interface Drawable {
    func draw();
}

struct Stack[T] {
    items: List[T];
}

// Basic implementation
extend Point {
    func magnitudeSquared() -> int32 {
        return self.x * self.x + self.y * self.y
    }
}

// Implementation of interface
conform Point to Drawable {
    func draw() {
        println("(${self.x}, ${self.y})")
    }
}

// Generic implementation
extend[T] Stack[T] {
    func first() -> Optional[&T] {
        return self.items.get(0)
    }
}

// Constrained implementation
extend[T] Stack[T] where T: PartialEq {
    func contains(item: &T) -> bool {
        for element in self.items {
            if element == *item { return true }
        }
        return false
    }
}
```

Inherent methods can only be added to types declared in the current package.
`extend[T] List[T] { ... }` is rejected outside std with *cannot add inherent
methods to type from another package without interface conformance*. A local
interface may instead be implemented for a foreign type, such as
`conform int32 to MyInterface`, subject to conformance coherence rules.

For a foreign interface, check the receiver first, followed by its interface
type arguments in declaration order. A conformance needs a local input type;
no uncovered type parameter may appear in earlier inputs. Thus a local `Vector`
argument can permit an implementation for `float64`, and an earlier foreign
`Container[T]` covers `T`. An earlier bare `T` or `&T` does not cover it.
`&Local` counts as local; raw pointers and foreign containers of `Local` do not.
Type aliases preserve these rules and do not establish new ownership.

Implementations with intersecting receiver/interface inputs conflict, including
across dependencies and aliases. Different associated outputs do not distinguish
implementations. A missing current conformance for a positive bound does not
prove that two generic implementations are disjoint.

### Value Initializers

A struct normally uses a field literal. Declaring any `init` in its owning
package requires initializer calls instead, including inside factories. This also
rejects update literals such as `Counter { value: 7, ..existing }`. Initializers
have no receiver parameter. Their private `self` storage must have every field
initialized on every successful return path. The implicit result is `Self`; an
explicit `Result[Self, E]` annotation makes construction fallible.

```taro
struct Counter {
    readonly origin: int32 = 1
    value: int32
}

extend Counter {
    init(_ value: int32) {
        self.value = value
        // self.origin = 2 // Error: its default already initialized this field.
    }
}

func main() {
    var counter: Counter = Counter(7)
    // Counter { origin: 1, value: 7 } // Error: use the initializer.
    println("${counter.value}")
}
```

Defaults run once, in declaration order, before the initializer body. They may
call synchronous helpers but cannot read `self` or other instance fields. A later
assignment to a mutable field does not suppress its default's evaluation.
Without an initializer, a field literal evaluates its explicit fields in written
order, then fills omitted defaults in declaration order; explicit fields skip
their defaults. Field visibility still applies to omitted fields. Synthesized
`clone()` copies/clones the stored fields without rerunning defaults or `init`.
A derived `default()` evaluates the declared defaults in declaration order but
does not call `init` either.

GC protects initialized reference-bearing fields during partial construction.
The result becomes usable after the body and its defers return successfully.
A panic leaves no constructed result for the caller. Use `defer` and explicit
close operations to release native resources.

During `init`, taking references to `self` or its own field storage is forbidden,
including references introduced by receiver autoref and captures. Copy an
initialized field to a local before taking a reference to that independent
storage. Existing reference values can still be copied, and their independent
pointees can be reborrowed, such as `&*self.pointer`.

A fallible initializer uses ordinary Result propagation. Successful completion
or a bare `return` produces `.ok(self)` after checking that all fields are
initialized. An error return discards partial storage without publishing it.

```taro
extend Counter {
    init(checked value: int32) -> Result[Self, string] {
        if value < 0 { return .err("negative counter") }
        self.value = value
    }
}
```

Fallible class construction preserves the same publication boundary: only a
complete successful payload becomes a GC object. Fallible delegation must use
`super.init(...)!` or `self.init(...)!` immediately; the superclass or delegated
self becomes initialized only on that success path. An overriding initializer
must preserve the base initializer's Result error type.

### Class Initializers

Classes use initializer calls rather than field literals. A designated
initializer constructs its base first with `super.init(...)`, then initializes
its own fields. Own field defaults run once, in declaration order, immediately
after base initialization (or before the body for a root class).

```taro
class Document { title: string }
extend Document {
    public init(_ title: string) { self.title = title }
    public convenience init() { self.init("Untitled") }
}
final class Draft: Document { revision: int32 = 0 }

func main() {
    var draft: Draft = Draft() // Inherited convenience constructs a Draft.
    assert(draft.title == "Untitled" && draft.revision == 0, "initialized")
}
```

A convenience initializer must delegate with `self.init(...)` exactly once on
every successful returning path. A fallible convenience initializer may return
an error before delegation using `return .err(error)`. Successful returns are
bare or implicit, so they always return the delegated self. Convenience-to-convenience calls select the declared body;
eventual designated delegation constructs the requested subclass. After that
delegation, field access is allowed, but instance-method calls, copying,
capturing, passing or replacing `self` are prohibited throughout initialization.
The restriction on references into self field storage also applies to convenience
initializers after delegation. References to copied values or independent
pointees remain allowed.
Cycles are rejected, including cycles introduced by subclass constructor overrides.

When all newly declared fields have defaults and a subclass declares no
designated initializer, it inherits base designated initializers.
Inherited signatures preserve argument labels, generic parameters, default
arguments and variadics. Construction publishes the requested subclass and runs
each level's field defaults once.

Providing all base designated signatures also permits inherited convenience initializers,
provided all new fields have defaults. Matching a base designated signature
requires `override init`, even when the replacement is a convenience initializer.
Matching only a convenience signature does not use `override`.

Initializers default to package visibility; use `public init` or
`public convenience init` for external construction. Inheritance preserves that
visibility. An inherited public convenience may internally reach an inaccessible
designated initializer without exposing that initializer to callers. All
initializers remain synchronous; fallible or asynchronous setup uses factories.

A `required init` establishes a constructor family every descendant must inherit
or implement. An explicit implementation repeats `required`; matching a base
designated signature also uses `override`. Required contracts must be at least
as visible as the non-final class, so public inheritable classes require public
required initializers. Final classes can keep private initializers.
The public requirement also applies when a class omits its default `public`
modifier; use `internal class` for a package-only constructor contract.

Inside an instance method, `Self(...)` selects an accessible required initializer
and constructs the receiver's runtime subclass, including that subclass's field
defaults. A final class can construct its exact `Self` without a required
contract. A non-final class cannot construct dynamic `Self` from a static method
without an initialized instance providing the runtime class.

### Explicit Factories

A static function named `new` is an ordinary associated factory. Select it
explicitly with `::new`; a type name does not implicitly select that function.
A type call requires an actual initializer, whose declaration is separate from
an ordinary factory.

```taro
struct Point {
    x: int32
    y: int32
}

extend Point {
    static func new(x: int32, y: int32) -> Self {
        return Point { x, y }
    }
}

func main() {
    point := Point::new(x: 10, y: 20)
    factory := Point::new
    another := factory(30, 40)
    println("${point.x} ${another.x}")
}
```

Factory calls and function values use ordinary overload resolution. Generic
arguments precede the member, for example `Box[int32]::new(42)`.

### Computed Properties

Computed properties use `get { ... }` and field-like reads. They are synchronous
and get-only. Their receiver follows ordinary method rules: `extend T` gets a
value copy, `extend &T` gets the original storage, and class targets share their
object. Explicit receiver parameters are not supported.

```taro
struct Counter { raw: int32 }

extend Counter {
    var value: int32 {
        get { self.raw }
    };
}

extend &Counter {
    func setValue(_ value: int32) {
        self.raw = value
    }
}

func main() {
    var counter: Counter = Counter { raw: 7 }
    var current: int32 = counter.value
    counter.setValue(current + 1)
}
```

A getter returns an ordinary value. Inline values are copied, while class and
reference values retain their normal sharing. A getter on `&T` can return a
reference into that storage. Automatic receiver referencing requires an existing
place; returned values do not acquire a hidden writable temporary. Getters do not
promise purity. Computed-property setters and direct assignment are rejected.

Interfaces may require the same getter or provide a default body. A matching
stored field can supply the getter without additional copy bounds. Matching
inherent properties or properties declared in a conformance can also supply it.
Qualified calls pass the declared receiver value, such as `Counted::count(value)`.

### Native Subscripts

Native subscripts declare their read, write and address capabilities directly:

```taro
struct Cell { value: int32 }
extend &Cell {
    subscript(index: usize) -> int32 {
        address {
            assert(index == 0, "cell index")
            &self.value
        }
    }
}
```

`address` supplies omitted getter and setter bodies. Explicit `get { ... }` and
`set(value) { ... }` replace their corresponding defaults. Accessors share one
implicit receiver category. A value target's escaping address points into its
receiver copy; use a reference target to access original struct storage.

Reads call `get` and copy the result. Whole-element assignment calls `set`.
Taking `&items[i]`, mutating a nested inline field, or calling a reference method
on an inline element requires `address`. These address operations bypass `set`.
A class or reference returned by a getter can mutate its shared target without
an element setter or address accessor.

Numeric compound assignment uses an address when available, otherwise one
get/modify/set operation. It evaluates RHS, receiver and indices once, in that
order. Custom value operators follow ordinary method semantics; a custom operator
needing `&Element` requires address access. Get/set-only subscripts do not invent
borrowed temporaries or nested struct writeback.

Indices have fixed arity. Multiple arguments (`matrix[row, column]`), one tuple
argument (`matrix[(row, column)]`), and range values are distinct. Bare parameter
names are unlabeled; explicit external labels are supported. Index types select
the overload; expected result types do not select a competing overload.

Interfaces declare capabilities with bodyless `get`, `set`, and `address`.
Associated element types must be fixed at generic or erased use sites:

```taro
interface Readable[Key] {
    type Element
    subscript(key: Key) -> Self::Element { get }
}
func read[Source: Readable[usize, Element = int32]](_ source: Source) -> int32 {
    source[0 as usize]
}
```

An implementation may expose extra capabilities to concrete callers. Generic
and erased callers see only the declared interface contract. Ordinary functions
with accessor-like names do not satisfy native requirements.

Class subscripts support `override` and `final`. Index labels/types and the element
type stay fixed. A partial override inherits omitted accessors; an address-only
override preserves an explicit inherited getter or setter. Inherited defaults
call the virtual address accessor, and a final partial override seals the entire
subscript. Added capabilities belong to the derived static view; the base view
retains its original contract. No accessor acquires an implicit writeback path.


---

## Type Alias Declaration

Type aliases create alternative names for types.

```taro
import std::hash::Hashable

// Simple alias
type Meters = int32
type UserId = string

// Generic alias
type StringMap[V] = Dictionary[string, V]
type Callback[T] = (T) -> ()

interface Readable[Value] {
    func read() -> Value;
}

interface Writable[Value] {
    func write(_ value: Value);
}

// Transparent interface-set aliases
type ReadWrite = Readable[int32] & Writable[int32]
type Resource[Value] = Readable[Value] & Writable[Value]
type ResourceAlias[Value] = Resource[Value]

// Associated type constraints belong to interfaces.
interface Indexed {
    type Key: Hashable;
    type Element: Equatable & Hashable;
}
```

Continuing those definitions, an interface-set alias expands wherever an
interface list is accepted:

```taro
func copy[Value: ReadWrite](_ value: Value) {}
func erase(_ value: any ReadWrite) {}

struct Cell { value: int32; }
conform Cell to Readable[int32] {
    func read() -> int32 { self.value }
}
conform Cell to Writable[int32] {
    func write(_ value: int32) { self.value = value }
}
func cell() -> some ReadWrite { Cell { value: 0 } }
```

Interface-set aliases may be generic, nested, and exported across package
boundaries. Expansion is transparent and duplicate constituents are removed.
They are not concrete types, so a bare field or parameter type must use
`any ReadWrite` when dynamic dispatch is intended.

An interface set is also not a single conformance declaration. Implement each
constituent explicitly; `conform File to ReadWrite` and `struct File: ReadWrite`
are rejected. Circular interface-set aliases are diagnosed.

The `any` spelling remains significant: `type Boxed = any ReadWrite` aliases
one concrete existential type, while `type ReadWrite = Readable[int32] &
Writable[int32]` aliases the interface requirements themselves.

---

## Namespace Declaration

Namespaces group related declarations.

```taro
namespace Math {
    const PI: double = 3.14159;
    const E: double = 2.71828;
    
    func abs(x: int32) -> int32 {
        if x < 0 { return -x }
        return x
    }
}

// Nested namespaces
namespace Graphics {
    namespace Colors {
        const RED: int32 = 0xFF0000;
    }
}
```

---

## Extern Block

Extern blocks declare foreign functions (FFI).

```taro
extern "C" {
    func puts(_ text: *const uint8) -> int32;
    func malloc(_ size: usize) -> *mut uint8;
    func free(_ ptr: *mut uint8);
}
```

Use the `blocking` ABI for foreign calls that may park indefinitely. It uses
the C calling convention and symbol name while identifying the blocking
boundary, so the collector can run while the call is blocked. A plain
`extern "C"` call that blocks stalls every collection until it returns.

```taro
extern "blocking" {
    func read(fd: int32, buffer: *mut uint8, count: usize) -> isize;
}
```

Managed values passed to a foreign call stay alive for the call. Foreign code
must not keep a managed pointer after it returns: the collector cannot see
foreign memory. Store a `std::runtime::Handle[T]` integer instead, which roots
its value until `delete()`, and use `std::runtime::keepAlive(value)` when
foreign code reads an address derived from `value` after Taro's last use of it.

A function passed directly as an argument to a foreign call, such as
`pthread_create(&thread, null, worker, arg)`, may be called back from any
thread, including threads the Taro runtime did not create and calls made while
a blocking call is in progress. The compiler wraps it so each callback
registers its thread with the collector on entry and parks it on return.
Function pointers that reach foreign code another way (stored in a struct
first, for example) are not wrapped and must only be called on threads that
are already running Taro code. A panic must not unwind out of a callback.

---

## Import Declaration

Imports bring items into scope.

```taro
// Import single item
import std::fs::File

// Import with alias
import std::fs::File as FsFile

// Import multiple items
import std::{io, fs, net}

// Glob import (all public items)
import std::io::*

// Nested path
import std::collections::{Dictionary, List, Set}
```

The standard prelude is available automatically unless a package sets
`no_std_prelude = true`. It provides common results, optionals, collections,
operators, marker interfaces, iteration interfaces, memory views, assertions,
and printing functions. Prefer their unqualified names in application code:

```taro
func copyAll[T](_ values: List[T]) -> Result[List[T], string] {
    return .ok(values)
}
```

The standard library itself disables the prelude and imports its dependencies
explicitly.

---

## Export Declaration

Exports re-export items from the current module.

```taro
export std::fs::File
export std::collections::*
```

---

## Constant Declaration

Constants define compile-time values.

```taro
const PI: double = 3.14159
const MAX_SIZE: int32 = 1024
const NAME: string = "Taro"

enum Direction { case north, south }
const START: Direction = Direction::north
const FINISH: Direction = .south
```

Constant initializers support literals, enum cases without payloads, references
to other constants, built-in unary and binary operators, primitive numeric and
rune casts, and `if` expressions.
Only the selected `if` branch is evaluated. Aggregate construction and general
function calls are not constant expressions.

An extension can declare a constant for a type or a particular specialization.
Use `Type::NAME` to read it, including in another constant or an array length.

```taro
struct Packet[T] { value: T }
extend Packet[uint8] { const SIZE: usize = 8; }
type Bytes = [uint8; Packet[uint8]::SIZE]
```

An interface can require a constant and provide a default. Reading that
constant through a generic type parameter selects the implementation for the
concrete type, including an override supplied by its conformance.

```taro
interface Labelled { const LABEL: string = "default"; }
struct Tag {}
conform Tag to Labelled { const LABEL: string = "tag"; }
func label[T: Labelled](_ value: T) -> string { T::LABEL }
```

A concrete type can use an interface constant in a declaration header. The
compiler selects the same visible conformance as it would in an expression,
including when the conformance is declared later. In this example the field
and the alias both have room for five bytes.

```taro
interface SizedPacket { const WIDTH: usize = 3; }
struct PacketKind {}
type Payload = [uint8; PacketKind::WIDTH]
struct PacketHeader { bytes: [uint8; PacketKind::WIDTH] }
conform PacketKind to SizedPacket { const WIDTH: usize = 5; }
```

---

## Static Variable Declaration

Module and namespace state must use explicit static declarations.

```taro
static var applicationName: string = "Taro"
static var counter: int32 = 0
```

---

## Operator Overloading

Operators are overloaded by implementing the corresponding standard library
interface, not with an `operator` declaration. `operator` is reserved but
unimplemented.

```taro
import std::ops::Add

struct Point {
    x: int32;
    y: int32;
}

conform Point to Add {
    func add(_ rhs: Point) -> Point {
        return Point { x: self.x + rhs.x, y: self.y + rhs.y }
    }
}

func main() {
    first := Point { x: 1, y: 2 }
    second := Point { x: 3, y: 4 }
    sum := first + second
    assert(sum.x == 4 && first.x == 1 && second.x == 3, "operands retain their values")
}
```

User-defined operators use the same receiver rules as named methods. Binary
requirements receive the declared RHS value. A value receiver copies its inline
value; a reference receiver is declared on `&T`. Compound assignment calls its
`…Assign` requirement without implicit writeback of a copied receiver. Use an
implementation on `&T` to edit inline destination storage. Programs synchronize
shared mutation themselves.

`std::ops` provides `Add`, `Sub`, `Mul`, `Div`, `Rem`, the bitwise operators, and
their `…Assign` counterparts for compound assignment. `Neg` and `Not` cover the
unary operators, and `PartialEq` / `Equatable` cover equality.


## Value Conversion Interfaces

Implement `From[Source]` on the destination type to supply both its static
`from(value)` constructor and the source's `into()` method:

```taro
struct Meters { value: int32 }
conform Meters to From[int32] {
    static func from(_ value: int32) -> Meters { Meters { value } }
}
var distance: Meters = 12_i32.into()
```

A static requirement implemented in a conformance is also callable on the
concrete type, as `Meters::from(12_i32)`, unless an inherent static of the same
name takes precedence.

`TryFrom[Source]` chooses an associated `Error` and returns
`Result[Self, Self::Error]`. Its blanket bridge supplies `TryInto[Target]`,
including the same error type:

```taro
conform Meters to TryFrom[string] {
    type Error = std::convert::ParseError
    static func tryFrom(_ input: string) -> Result[Meters, Self::Error] {
        return .ok(Meters { value: int32::parse(input)! })
    }
}
var parsed: Result[Meters, std::convert::ParseError] = "42".tryInto()
```

Give `into()` and `tryInto()` their destination through a type annotation,
argument context, or generic return type. Generic functions can use
`T: From[S]` or `T: TryFrom[S]` and call the corresponding bridge on an `S`.
Conversions use ordinary GC value/handle semantics. Implementing an overlapping
`Into` or `TryInto` for a pair already supplied by its bridge is an error.
Postfix Result propagation (`!`) continues to convert errors through `From`,
or boxes them when the enclosing error type is an existential.
