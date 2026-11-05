//! Source → MIR → LLVM → normalized root table → real collector regressions.
//! Each image links a matching runtime and keeps its metadata loaded.
use super::*;

#[test]
fn scalar_payload_enum_construction_does_not_need_a_temporary_clear() {
    use inkwell::values::AnyValue;
    let source = r#"
enum Value {
    case number(int64)
    case text(string)
    case pointer(&int32)
}
struct Wrapper { value: Value }
public func number(_ value: int64) -> Wrapper { Wrapper { value: .number(value) } }
func main() {}
"#;
    for explicit_lifetime in [false, true] {
        crate::test_support::analyze_native_class_fixture(
            source,
            &[],
            &[],
            |_, mut bodies, gcx| {
                if explicit_lifetime {
                    for body in &mut bodies {
                        for block in &mut body.basic_blocks {
                            let mut statements = Vec::new();
                            for statement in std::mem::take(&mut block.statements) {
                                if let mir::StatementKind::Assign(
                                    place,
                                    mir::Rvalue::Aggregate { kind, .. },
                                ) = &statement.kind
                                    && place.projection.is_empty()
                                    && body.locals[place.local].kind == mir::LocalKind::Temp
                                    && matches!(kind, mir::AggregateKind::Adt { def_id, .. } if gcx.definition_kind(*def_id) == hir::DefinitionKind::Enum)
                                {
                                    statements.push(mir::Statement {
                                        kind: mir::StatementKind::StorageLive(place.local),
                                        span: statement.span,
                                    });
                                }
                                statements.push(statement);
                            }
                            block.statements = statements;
                        }
                    }
                }
                let package = super::test_support::publish(
                    gcx,
                    bodies.into_iter().map(|body| (body.owner, body)).collect(),
                );
                let id = *package
                    .functions
                    .keys()
                    .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "number")
                    .unwrap();
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("scalar-enum-construction"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("emitter"));
                let (function, _) = emitter
                    .instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
                emitter
                    .lower_instances()
                    .unwrap_or_else(|_| panic!("lowering"));
                emitter.module.verify().unwrap();
                let ir = function.print_to_string().to_string();
                assert!(
                    !ir.lines()
                        .any(|line| line.contains("store volatile {") && line.contains("ptr %tmp")),
                    "complete enum values need no temporary entry clear: {ir}"
                );
                assert!(
                    ir.contains("store volatile { { i8"),
                    "caller-visible return initialization remains: {ir}"
                );
                assert!(
                    ir.contains("__gc__poll") && ir.contains("llvm.experimental.stackmap"),
                    "{ir}"
                );
            },
        );
    }
}

#[test]
fn repeated_unit_enum_array_does_not_need_partial_initialization() {
    use inkwell::values::AnyValue;
    let source = r#"
enum Entry {
    case live([&int32; 4])
    case empty
}
struct Group { entries: [Entry; 8] }
public func emptyGroup() -> Group { Group { entries: [.empty; 8] } }
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let id = *package
            .functions
            .keys()
            .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "emptyGroup")
            .unwrap();
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("array-temporary-initialization"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let (function, _) =
            emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        let ir = function.print_to_string().to_string();
        assert!(
            !ir.lines().any(
                |line| line.contains("store volatile [8 x") && line.contains("zeroinitializer")
            ),
            "{ir}"
        );
        // Unit constructors define the tag and every inactive payload word in
        // one value. They need neither a partial tag store nor an entry clear.
        assert!(!ir.contains("enum_discr_ptr"), "{ir}");
        assert!(!ir.contains("store volatile {"), "{ir}");
        // Caller-visible return storage and entry cooperation remain intact.
        assert!(ir.contains("llvm.memset.inline"), "{ir}");
        assert!(
            ir.contains("__gc__poll") && ir.contains("llvm.experimental.stackmap"),
            "{ir}"
        );
    });
}

#[test]
fn string_data_keeps_backing_provenance_without_heapifying_the_header() {
    use inkwell::values::AnyValue;
    let source = r#"
extern "taro_intrinsic" {
    func __intrinsic_string_data(_ text: &string) -> *const uint8
    unsafe func __intrinsic_string_from_parts(_ data: *const uint8, _ count: usize) -> string
    unsafe func __intrinsic_string_slice(_ text: &string, _ start: usize, _ count: usize) -> string
    func __intrinsic_ref_to_ptr[T](_ value: &T) -> *const T
}
public func bytes(_ text: string) -> *const uint8 {
    var snapshot = text
    __intrinsic_string_data(&snapshot)
}
public func header(_ text: string) -> &string {
    var snapshot = text
    &snapshot
}
public func slice(_ text: string) -> string {
    unsafe { __intrinsic_string_slice(&text, 1, 2) }
}
public func wrap(_ data: *const uint8) -> string {
    unsafe { __intrinsic_string_from_parts(data, 1) }
}
public func localBytes() -> string {
    var byte: uint8 = 97
    unsafe { __intrinsic_string_from_parts(__intrinsic_ref_to_ptr(&byte), 1) }
}
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("string-data-provenance"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let functions: Vec<_> = ["bytes", "header", "slice", "wrap", "localBytes"]
            .into_iter()
            .map(|name| {
                let id = *package
                    .functions
                    .keys()
                    .find(|&&id| gcx.definition_ident(id).symbol.as_str() == name)
                    .unwrap();
                let (function, _) = emitter
                    .instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
                (name, id, function)
            })
            .collect();
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        for (name, id, function) in functions {
            let ir = function.print_to_string().to_string();
            assert_eq!(
                ir.contains("call ptr @__gc__alloc"),
                matches!(name, "header" | "localBytes"),
                "{name}: {ir}"
            );
            let summaries = gcx.store.instance_escape_summaries.borrow();
            let summary = &summaries[&Instance::item(id, GenericArguments::empty())];
            // Every view retains the backing bytes. Only an explicit header
            // reference or returned local byte needs fresh heap storage.
            if name != "localBytes" {
                assert_eq!(summary.params[0].return_deref, Some(0), "{name}");
            }
        }
    });
}

#[test]
fn typed_pointer_intrinsics_preserve_whole_pointer_words() {
    let source = r#"
struct Handle { target: &int32 }
enum Choice {
    case empty
    case live(&int32)
    case raw([uint64; 2])
}
extern "taro_intrinsic" {
    unsafe func __intrinsic_ptr_read[T](_ p: *T) -> T
    unsafe func __intrinsic_ptr_write[T](_ p: *mut T, _ value: T)
    unsafe func __intrinsic_memmove[T](_ dst: *mut T, _ src: *T, _ bytes: usize)
}
public func rawRead(_ p: *Handle) -> Handle { unsafe { __intrinsic_ptr_read(p) } }
public func rawWrite(_ p: *mut Handle, _ value: Handle) { unsafe { __intrinsic_ptr_write(p, value) } }
public func rawCopy(_ dst: *mut Handle, _ src: *Handle) { unsafe { __intrinsic_memmove(dst, src, 128 as usize) } }
public func rawReadChoice(_ p: *Choice) -> Choice { unsafe { __intrinsic_ptr_read(p) } }
public func rawWriteChoice(_ p: *mut Choice, _ value: Choice) { unsafe { __intrinsic_ptr_write(p, value) } }
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("raw-shared-access"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        for &id in package.functions.keys() {
            if gcx.definition_ident(id).symbol.as_str().starts_with("raw") {
                emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
            }
        }
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().expect("valid pointer atomic IR");
        let ir = emitter.module.print_to_string().to_string();
        assert!(ir.contains("load atomic ptr"), "{ir}");
        assert!(ir.contains("store atomic ptr"), "{ir}");
        assert!(
            ir.contains("@llvm.memmove.element.unordered.atomic"),
            "{ir}"
        );
        use inkwell::values::AnyValue;
        let read_choice = emitter
            .module
            .get_functions()
            .find(|function| {
                function
                    .get_name()
                    .to_string_lossy()
                    .contains("__rawReadChoice__")
            })
            .unwrap();
        let choice_ir = read_choice.print_to_string().to_string();
        assert!(
            choice_ir.contains("load atomic i64"),
            "tagged pointer words: {choice_ir}"
        );
    });
}

#[test]
fn inlined_pointer_write_does_not_zero_fully_copied_arguments() {
    use inkwell::values::AnyValue;
    let source = r#"
enum Choice {
    case some([&int32; 4])
    case none
}
extern "taro_intrinsic" {
    unsafe func __intrinsic_ptr_write[T](_ p: *T, _ value: T)
}
@inline
unsafe func forward(_ destination: *mut Choice, _ value: Choice) {
    unsafe { __intrinsic_ptr_write(destination as *Choice, value) }
}
public func fill(_ destination: *mut Choice, _ value: Choice) {
    unsafe { forward(destination, value) }
}
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let id = *package
            .functions
            .keys()
            .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "fill")
            .unwrap();
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("interleaved-argument-copies"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let (function, _) =
            emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        emitter
            .module
            .run_passes(
                "default<O3>",
                &emitter.target_machine,
                PassBuilderOptions::create(),
            )
            .unwrap();
        let ir = function.print_to_string().to_string();
        // Both the caller's synthetic scratch and the cloned inline arguments
        // receive complete noncollecting copies before any observation.
        let clears = ir
            .lines()
            .filter(|line| line.contains("store volatile {") && line.contains("zeroinitializer"))
            .count();
        assert_eq!(
            clears, 0,
            "synthetic and lifetime-marked arguments need no clear before complete copies: {ir}"
        );
        assert!(
            ir.contains("store atomic i64"),
            "shared pointer words remain atomic: {ir}"
        );
        assert!(
            ir.contains("__gc__poll") && ir.contains("llvm.experimental.stackmap"),
            "entry cooperation and root publication remain: {ir}"
        );
    });
}

#[test]
fn fully_copied_gc_receiver_does_not_need_scanner_zeroing() {
    use inkwell::values::AnyValue;
    let source = r#"
struct Handle { target: &int32 }
@noinline
func inspect(_ value: &Handle) -> int32 { *value.target }
@inline
func forward(_ value: Handle) -> int32 { inspect(&value) }
public func consume(_ value: Handle) -> int32 { forward(value) }
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let mut bodies: Vec<_> = bodies.into_iter().map(|body| (body.owner, body)).collect();
        for (_, body) in &mut bodies {
            mir::optimize::run_local_passes(gcx, body).unwrap_or_else(|_| panic!("local MIR"));
        }
        let package = super::test_support::publish(gcx, bodies);
        let id = *package
            .functions
            .keys()
            .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "consume")
            .unwrap();
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("copied-gc-receiver"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let (function, _) =
            emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        emitter
            .module
            .run_passes(
                "default<O3>",
                &emitter.target_machine,
                PassBuilderOptions::create(),
            )
            .unwrap();
        let ir = function.print_to_string().to_string();
        assert!(
            !ir.lines().any(|line| line.contains("store volatile")
                && (line.contains("zeroinitializer") || line.contains("ptr null"))),
            "a whole copy before any collecting observation replaces scanner zeroing: {ir}"
        );
        assert!(
            ir.contains("__inspect__"),
            "the receiver is still addressed: {ir}"
        );
        assert!(
            ir.contains("llvm.experimental.stackmap") && ir.contains("__gc__poll"),
            "root publication and GC cooperation must remain: {ir}"
        );
    });
}

#[test]
fn recursive_wrapper_inlining_keeps_a_native_call_and_gc_poll() {
    use inkwell::values::AnyValue;
    let source = r#"
@inline
func step(_ depth: int32, _ value: &int32) -> int32 { recurse(depth - 1, value) + 1 }
@inline
public func recurse(_ depth: int32, _ value: &int32) -> int32 {
    if depth == 0 { return *value }
    step(depth, value)
}
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let mut bodies: Vec<_> = bodies.into_iter().map(|body| (body.owner, body)).collect();
        for (_, body) in &mut bodies {
            mir::optimize::run_local_passes(gcx, body).unwrap_or_else(|_| panic!("local MIR"));
        }
        let package = super::test_support::publish(gcx, bodies);
        let id = *package
            .functions
            .keys()
            .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "recurse")
            .unwrap();
        let body = package.functions[&id];
        assert!(
            body.basic_blocks.len() < 32,
            "recursive expansion must stay bounded"
        );
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("recursive-wrapper"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let (function, _) =
            emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        let ir = function.print_to_string().to_string();
        assert!(
            !ir.contains("__step__"),
            "the small wrapper should disappear: {ir}"
        );
        let symbol = function.get_name().to_str().unwrap();
        assert!(
            ir.lines()
                .any(|line| (line.contains("call ") || line.contains("invoke "))
                    && line.contains(&format!("@{symbol}("))),
            "a recursive native call must remain: {ir}"
        );
        assert!(
            ir.contains("call void @__gc__poll()"),
            "recursive entry must still cooperate: {ir}"
        );
    });
}

#[test]
fn loaded_reference_escape_preserves_the_target_without_boxing_its_header() {
    use inkwell::values::AnyValue;
    let source = r#"
public type Link = &int32
@noinline
func retain(_ output: &Link, _ input: &Link) { *output = *input }
@noinline
func load(_ input: &Link) -> Link { *input }
@noinline
public func caller(_ output: &Link, _ child: Link) {
    local := child
    retain(output, &local)
}
@noinline
public func produce(_ output: &Link) {
    var value: int32 = 41
    caller(output, &value)
}
@noinline
public func returned() -> Link {
    var value: int32 = 42
    local := &value
    load(&local)
}
@noinline
public func returnedHeader() -> &Link {
    var value: int32 = 43
    local := &value
    &local
}
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let mut bodies: Vec<_> = bodies.into_iter().map(|body| (body.owner, body)).collect();
        for (_, body) in &mut bodies {
            mir::optimize::run_local_passes(gcx, body).unwrap_or_else(|_| panic!("local MIR"));
        }
        let package = super::test_support::publish(gcx, bodies);
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("loaded-reference-escape"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let functions: Vec<_> = ["returned", "produce", "caller", "returnedHeader"]
            .into_iter()
            .map(|name| {
                let id = *package
                    .functions
                    .keys()
                    .find(|&&id| gcx.definition_ident(id).symbol.as_str() == name)
                    .unwrap();
                let (function, _) = emitter
                    .instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
                (name, function)
            })
            .collect();
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        for (name, function) in functions {
            let ir = function.print_to_string().to_string();
            let allocations = ir
                .lines()
                .filter(|line| line.contains("call") && line.contains("@__gc__alloc("))
                .count();
            assert_eq!(
                allocations,
                match name {
                    "caller" => 0,
                    "returnedHeader" => 2,
                    _ => 1,
                },
                "{name}: {ir}"
            );
        }
    });
}

/// Collector initialization belongs to a local's storage lifetime, so a cold
/// aggregate must not impose volatile zero stores on the function's hot entry.
#[test]
fn cold_gc_storage_is_initialized_only_when_its_lifetime_starts() {
    let source = r#"
struct Triple { first: &int32; second: &int32; third: &int32 }
@noinline
func inspect(_ value: &Triple) -> int32 { *value.first + *value.second + *value.third }
public func coldRoot(_ cold: bool, _ source: &int32) -> int32 {
    if cold {
        var temporary = Triple { first: source, second: source, third: source }
        return inspect(&temporary)
    }
    7
}
func main() {}
"#;
    assert_cold_root_initialization(source);
}

#[test]
fn cold_gc_compiler_temporary_is_not_zeroed_on_the_hot_entry() {
    assert_cold_root_initialization(
        r#"
struct Triple { first: &int32; second: &int32; third: &int32 }
@noinline
func inspect(_ value: Triple) -> int32 { *value.first + *value.second + *value.third }
public func coldRoot(_ cold: bool, _ source: &int32) -> int32 {
    if cold {
        return inspect(Triple { first: source, second: source, third: source })
    }
    7
}
func main() {}
"#,
    );
}

fn assert_cold_root_initialization(source: &str) {
    use inkwell::values::AnyValue;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let mut bodies: Vec<_> = bodies.into_iter().map(|body| (body.owner, body)).collect();
        for (_, body) in &mut bodies {
            mir::optimize::run_local_passes(gcx, body).unwrap_or_else(|_| panic!("local MIR"));
        }
        let package = super::test_support::publish(gcx, bodies);
        let id = *package
            .functions
            .keys()
            .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "coldRoot")
            .unwrap();
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("cold-roots"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let (function, _) =
            emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        let mut cold_zeros = 0;
        for block in function.get_basic_blocks() {
            let mut next = block.get_first_instruction();
            while let Some(instruction) = next {
                next = instruction.get_next_instruction();
                let text = instruction.print_to_string().to_string();
                if text.contains("store volatile") && text.contains("zeroinitializer") {
                    assert_ne!(
                        block,
                        function.get_first_basic_block().unwrap(),
                        "cold root initialization must not execute at function entry: {text}"
                    );
                    cold_zeros += 1;
                }
            }
        }
        assert!(
            cold_zeros > 0,
            "cold aggregate scanner bytes still need initialization"
        );
    });
}

#[test]
fn inlined_result_error_buffers_are_not_initialized_before_the_hot_lookup() {
    check_inlined_result_error_initialization(false);
}

#[test]
fn inlined_result_error_buffers_stay_cold_with_an_unrelated_loop() {
    check_inlined_result_error_initialization(true);
}

fn check_inlined_result_error_initialization(with_loop: bool) {
    use inkwell::values::AnyValue;
    let source = r#"
enum Value { case number(int64); case pointer(&int32); case text(string) }
enum Failure { case missing(string); case large(string, int64, int64) }
enum Signal { case failed(Failure); case produced(Value) }
enum Outcome { case ok(Value); case err(Signal) }
enum Found { case some(Value); case none }
@noinline
func lookup(_ hit: bool, _ value: &int32) -> Found {
    if hit { return .some(.pointer(value)) }
    return .none
}
@inline
func resolve(_ hit: bool, _ value: &int32) -> Outcome {
    match lookup(hit, value) {
        case .some(found) => return .ok(found)
        case .none => {}
    }
    return .err(.failed(.missing("unknown")))
}
public func caller(_ hit: bool, _ value: &int32) -> Outcome {
    return resolve(hit, value)
}
func main() {}
"#;
    let source = if with_loop {
        source.replace(
            "return resolve(hit, value)",
            "while *value < 0 { lookup(hit, value); *value += 1 }; return resolve(hit, value)",
        )
    } else {
        source.to_string()
    };
    crate::test_support::analyze_native_class_fixture(&source, &[], &[], |_, bodies, gcx| {
        let mut bodies: Vec<_> = bodies.into_iter().map(|body| (body.owner, body)).collect();
        for (_, body) in &mut bodies {
            mir::optimize::run_local_passes(gcx, body).unwrap_or_else(|_| panic!("local MIR"));
        }
        let package = super::test_support::publish(gcx, bodies);
        let id = *package
            .functions
            .keys()
            .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "caller")
            .unwrap();
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("inlined-result"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let (function, _) =
            emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        emitter
            .module
            .run_passes(
                "default<O3>",
                &emitter.target_machine,
                PassBuilderOptions::create(),
            )
            .unwrap();
        let ir = function.print_to_string().to_string();
        assert!(
            !ir.contains("__resolve__"),
            "fixture must inline resolve: {ir}"
        );
        let mut cold_zeros = 0;
        for block in function.get_basic_blocks() {
            let mut lines = Vec::new();
            let mut next = block.get_first_instruction();
            while let Some(instruction) = next {
                next = instruction.get_next_instruction();
                lines.push(instruction.print_to_string().to_string());
            }
            for line in &lines {
                if line.contains("store volatile")
                    && line.contains("zeroinitializer")
                    && (line.contains("[4 x i64]") || line.contains("[5 x i64]"))
                {
                    assert_ne!(
                        block,
                        function.get_first_basic_block().unwrap(),
                        "cold error initialization at entry: {ir}"
                    );
                    assert!(
                        !lines
                            .iter()
                            .any(|line| line.contains("call") && line.contains("__lookup__")),
                        "cold error initialization before hot lookup: {ir}"
                    );
                    cold_zeros += 1;
                }
            }
        }
        // The scalar Failure constructor now defines its complete value.
        // The enclosing partial Signal constructor still needs scanner bytes.
        assert!(
            cold_zeros >= 1,
            "partial cold-path scanner initialization must remain: {ir}"
        );
        assert!(
            ir.contains("llvm.experimental.stackmap") && ir.contains("__gc__poll"),
            "GC cooperation remains: {ir}"
        );
    });
}

fn gc_runtime_archive() -> std::path::PathBuf {
    let directory = std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned();
    let mut archives: Vec<_> = std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("libtaro_runtime-")
                && path.extension().is_some_and(|ext| ext == "a")
        })
        .collect();
    archives.sort_by_key(|path| std::cmp::Reverse(path.metadata().unwrap().modified().unwrap()));
    archives
        .into_iter()
        .find(|archive| {
            let output = std::process::Command::new("nm")
                .arg("-g")
                .arg(archive)
                .output()
                .unwrap();
            let symbols = String::from_utf8_lossy(&output.stdout);
            symbols.contains("__gc__test_collect_probe_is_live")
                && symbols.contains("__gc__pc_metadata_register")
                && symbols.contains("__gc__test_request_collection")
        })
        .expect("matching GC runtime from compiler dev dependency")
}

#[test]
fn source_roots_survive_collection_and_dead_values_are_reclaimed() {
    exercise_source_roots(AllocationFixture::Foreign);
}

#[test]
fn managed_mir_allocations_use_generated_descriptors_and_exact_roots() {
    exercise_source_roots(AllocationFixture::Managed);
}

#[test]
fn class_field_addresses_keep_generated_payloads_alive() {
    exercise_source_roots(AllocationFixture::ClassField);
}

#[test]
fn returned_local_references_are_heapified_and_survive_collection() {
    exercise_source_roots(AllocationFixture::ReturnedLocal);
}

#[test]
fn overlapping_bindings_preserve_the_previous_value_at_runtime() {
    exercise_source_roots(AllocationFixture::OverlappingBindings);
}

#[test]
fn partially_initialized_aggregates_keep_their_initialized_fields_alive() {
    exercise_source_roots(AllocationFixture::PartialAggregate);
}

/// Boxing, witness Self results (borrowed and consuming receivers), exact
/// downcasts and generic calls on erased values, with forced collections while
/// only erased headers reach their traced payloads.
#[test]
fn erased_payloads_survive_collection_and_self_results_rebox() {
    let _guard = super::test_support::GC_TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let runtime = gc_runtime_archive();
    for level in [0, 2, 3] {
        let entry = format!("exercise_gc_erased_o{level}");
        let source = format!(
            r#"
extern "C" {{
    unsafe func fixture_gc_detach()
    unsafe func fixture_gc_request() -> usize
    unsafe func fixture_gc_count() -> usize
    unsafe func fixture_gc_noop()
    unsafe func fixture_gc_probe(_ target: *const int32) -> *mut uint8
    unsafe func fixture_gc_live(_ probe: *mut uint8) -> bool
}}
interface Duplicate {{
    func duplicate() -> Self
}}
interface Label {{
    func number() -> int32
}}
interface Advance {{
    func advance() -> Self
}}
enum Optional[T] {{ case some(T); case none }}
struct Counter {{ value: int32 }}
conform Counter to Duplicate {{
    func duplicate() -> Self {{ Counter {{ value: self.value + 1_i32 }} }}
}}
conform Counter to Label {{
    func number() -> int32 {{ self.value }}
}}
conform Counter to Advance {{
    func advance() -> Self {{ Counter {{ value: self.value + 2_i32 }} }}
}}
struct Large {{ words: [int64; 16]; value: int32 }}
conform Large to Duplicate {{
    func duplicate() -> Self {{ Large {{ words: self.words, value: self.value + 1_i32 }} }}
}}
conform Large to Label {{
    func number() -> int32 {{ self.value + 3_i32 }}
}}
@noinline
func collectorPoll() {{ unsafe {{ fixture_gc_noop() }} }}
@noinline
func collect() -> bool {{
    before := unsafe {{ fixture_gc_request() }}
    collectorPoll()
    unsafe {{ fixture_gc_count() }} > before
}}
func payloadOf[T](_ value: &T) -> *const int32 {{
    var header: *const T = unsafe {{ value as *const T }}
    unsafe {{ *(header as *const *const int32) }}
}}
func readGeneric[T: Label](_ value: &T) -> int32 {{ value.number() }}
public func {entry}() -> int32 {{
    var original: any Duplicate & Label = Counter {{ value: 7_i32 }}
    var large: any Duplicate & Label = Large {{ words: [3_i64; 16], value: 38_i32 }}
    if !collect() {{ unsafe {{ fixture_gc_detach() }}; return -1 }}
    // The boxing allocation itself collects while only frame headers reach
    // the earlier payloads; later same-sized boxes would reuse lost storage.
    probe := unsafe {{ fixture_gc_probe(payloadOf(&original)) }}
    requested := unsafe {{ fixture_gc_request() }}
    var noise: any Label = Counter {{ value: 1000_i32 }}
    if unsafe {{ fixture_gc_count() }} <= requested {{ unsafe {{ fixture_gc_detach() }}; return -3 }}
    if !unsafe {{ fixture_gc_live(probe) }} {{ unsafe {{ fixture_gc_detach() }}; return -4 }}
    var copied: any Duplicate & Label = original.duplicate()
    var next: any Duplicate & Label = large.duplicate()
    var owned: any Advance & Label = Counter {{ value: 5_i32 }}
    var advanced: any Advance & Label = owned.advance()
    if !collect() {{ unsafe {{ fixture_gc_detach() }}; return -2 }}
    first := original.number() + copied.number() + next.number() + large.number()
    var extracted: Counter = match copied as? Counter {{
        case .some(value) => value
        case .none => Counter {{ value: -100_i32 }}
    }}
    second := advanced.number() + extracted.value + readGeneric(&original) + noise.number()
    total := first + second
    unsafe {{ fixture_gc_detach() }}
    total
}}
func main() {{}}
"#
        );
        crate::test_support::analyze_native_class_fixture(
            &source,
            &[],
            &[(hir::StdItem::Optional, "Optional")],
            |_, bodies, gcx| {
                let bodies: Vec<_> = bodies.into_iter().map(|body| (body.owner, body)).collect();
                // original 7, copied 8, next (39+3), large (38+3), advanced 7,
                // extracted 8, generic 7 and the post-collection box 1000.
                assert_eq!(
                    compile_link_run(gcx, bodies, &entry, level, &runtime),
                    1120,
                    "erased payloads and re-erased Self results at O{level}"
                );
            },
        );
    }
}

#[derive(Clone, Copy)]
enum AllocationFixture {
    Foreign,
    Managed,
    ClassField,
    ReturnedLocal,
    OverlappingBindings,
    PartialAggregate,
}

fn exercise_source_roots(fixture: AllocationFixture) {
    let managed_mir = !matches!(fixture, AllocationFixture::Foreign);
    let class_payload = matches!(fixture, AllocationFixture::ClassField);
    let partial_aggregate = matches!(fixture, AllocationFixture::PartialAggregate);
    let overlapping = matches!(fixture, AllocationFixture::OverlappingBindings);
    let returned_local = matches!(
        fixture,
        AllocationFixture::ReturnedLocal
            | AllocationFixture::OverlappingBindings
            | AllocationFixture::PartialAggregate
    );
    let initial_value = if overlapping {
        41
    } else if returned_local {
        42
    } else {
        0
    };
    let _guard = super::test_support::GC_TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let runtime = gc_runtime_archive();
    for level in [0, 2, 3] {
        let optimized = level != 0;
        let entry = format!(
            "exercise_gc_o{}_{}",
            level,
            if partial_aggregate {
                "partial"
            } else if overlapping {
                "overlapping"
            } else if returned_local {
                "returned"
            } else if class_payload {
                "class"
            } else if managed_mir {
                "managed"
            } else {
                "foreign"
            }
        );
        let source = format!(
            r#"
extern "C" {{
    unsafe func fixture_gc_allocate() -> *mut int32
    unsafe func fixture_gc_probe(_ target: *const int32) -> *mut uint8
    unsafe func fixture_gc_live(_ probe: *mut uint8) -> bool
    unsafe func fixture_gc_detach()
    unsafe func fixture_gc_request() -> usize
    unsafe func fixture_gc_count() -> usize
    unsafe func fixture_gc_noop()
}}
class GcCell {{ link: *const int32; value: int32 }}
@noinline
func allocateEscaping() -> &int32 {{ loop {{}} }}
@noinline
func collectorPoll() {{ unsafe {{ fixture_gc_noop() }} }}
public func {entry}() -> int32 {{
    value := unsafe {{ fixture_gc_allocate() }}
    initial := unsafe {{ *value }}
    correct := initial == {initial_value}
    if !correct {{ unsafe {{ fixture_gc_detach() }}; return -1000 - initial }}
    unsafe {{ *value = 42 }}
    probe := unsafe {{ fixture_gc_probe(value as *const int32) }}
    before := unsafe {{ fixture_gc_request() }}
    collectorPoll()
    polled := unsafe {{ fixture_gc_count() }} > before
    kept := unsafe {{ fixture_gc_live(probe) }}
    answer := unsafe {{ *value }}
    remains := unsafe {{ fixture_gc_live(probe) }}
    unsafe {{ fixture_gc_detach() }}
    if correct && polled && kept && !remains {{ answer }} else {{ -1 }}
}}
func main() {{}}
"#
        );
        crate::test_support::analyze_native_class_fixture(
            &source,
            &[],
            &[],
            |package, bodies, gcx| {
                let mut bodies: Vec<_> =
                    bodies.into_iter().map(|body| (body.owner, body)).collect();
                for (_, body) in &mut bodies {
                    mir::optimize::run_local_passes(gcx, body)
                        .unwrap_or_else(|_| panic!("GC source lowering"));
                }
                let reference_helper = package
                    .root
                    .declarations
                    .iter()
                    .find(|declaration| {
                        gcx.definition_ident(declaration.id).symbol.as_str() == "allocateEscaping"
                    })
                    .unwrap()
                    .id;
                if returned_local {
                    // Native admission cannot return a reference to a local.
                    // Replace its diverging fixture body with valid target MIR;
                    // the actual production escape pass must heapify that local.
                    let body = &mut bodies
                        .iter_mut()
                        .find(|(id, _)| *id == reference_helper)
                        .unwrap()
                        .1;
                    let span = body.locals[body.return_local].span;
                    let result = body.locals[body.return_local].clone();
                    body.locals = index_vec::IndexVec::from(vec![result]);
                    body.return_local = mir::LocalId::new(0);
                    let data = body.locals.push(mir::LocalDecl {
                        ty: gcx.types.int32,
                        kind: mir::LocalKind::User,
                        mutable: true,
                        name: None,
                        span,
                    });
                    body.start_block = mir::BasicBlockId::new(0);
                    body.escape_locals.clear();
                    body.basic_blocks = index_vec::IndexVec::from(vec![mir::BasicBlockData {
                        note: Some("escaping managed local".into()),
                        statements: vec![
                            mir::Statement {
                                span,
                                kind: mir::StatementKind::StorageLive(data),
                            },
                            mir::Statement {
                                span,
                                kind: mir::StatementKind::Assign(
                                    Place::from_local(data),
                                    mir::Rvalue::Use(Operand::Constant(mir::Constant {
                                        ty: gcx.types.int32,
                                        value: mir::ConstantKind::Integer(42),
                                    })),
                                ),
                            },
                            mir::Statement {
                                span,
                                kind: mir::StatementKind::Assign(
                                    Place::from_local(body.return_local),
                                    mir::Rvalue::Ref {
                                        place: Place::from_local(data),
                                    },
                                ),
                            },
                        ],
                        terminator: Some(mir::Terminator {
                            span,
                            kind: mir::TerminatorKind::Return,
                        }),
                    }]);
                }
                if overlapping {
                    let body = &mut bodies
                        .iter_mut()
                        .find(|(id, _)| *id == reference_helper)
                        .unwrap()
                        .1;
                    install_overlapping_bindings(gcx, body, mir::LocalId::new(1));
                }
                if partial_aggregate {
                    let foreign = |name: &str| {
                        bodies
                            .iter()
                            .flat_map(|(_, body)| body.basic_blocks.iter())
                            .filter_map(|block| block.terminator.as_ref())
                            .find_map(|term| match &term.kind {
                                mir::TerminatorKind::Call {
                                    func: Operand::Constant(constant),
                                    ..
                                } => match constant.value {
                                    mir::ConstantKind::Function(id, _, _)
                                        if gcx.definition_ident(id).symbol.as_str() == name =>
                                    {
                                        Some(id)
                                    }
                                    _ => None,
                                },
                                _ => None,
                            })
                            .unwrap()
                    };
                    let probe = foreign("fixture_gc_probe");
                    let collect = foreign("fixture_gc_live");
                    let body = &mut bodies
                        .iter_mut()
                        .find(|(id, _)| *id == reference_helper)
                        .unwrap()
                        .1;
                    install_partial_aggregate(gcx, body, mir::LocalId::new(1), probe, collect);
                }
                let allocated_ty = if class_payload {
                    let class = package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| {
                            gcx.definition_ident(declaration.id).symbol.as_str() == "GcCell"
                        })
                        .unwrap()
                        .id;
                    crate::sema::tycheck::class_layout::gc_class_payload_ty(
                        gcx,
                        gcx.get_type(class),
                    )
                    .unwrap()
                } else {
                    gcx.types.int32
                };
                if managed_mir {
                    // Exercise the candidate allocation MIR before the source
                    // cutover removes the frontend's retired-GC diagnostics. All
                    // existing source computation and liveness remain unchanged.
                    for (_, body) in &mut bodies {
                        let original_blocks = body.basic_blocks.len();
                        let mut continuations = Vec::new();
                        for block in &mut body.basic_blocks {
                            let Some(term) = &block.terminator else {
                                continue;
                            };
                            let mir::TerminatorKind::Call {
                                func: Operand::Constant(constant),
                                destination,
                                target,
                                ..
                            } = &term.kind
                            else {
                                continue;
                            };
                            let mir::ConstantKind::Function(id, _, _) = constant.value else {
                                continue;
                            };
                            if gcx.definition_ident(id).symbol.as_str() != "fixture_gc_allocate" {
                                continue;
                            }
                            let span = term.span;
                            let destination = destination.clone();
                            let target = *target;
                            let reference = body.locals.push(mir::LocalDecl {
                                ty: Ty::new(TyKind::Reference(allocated_ty), gcx),
                                kind: mir::LocalKind::Temp,
                                mutable: true,
                                name: None,
                                span,
                            });
                            if returned_local {
                                let continuation =
                                    mir::BasicBlockId::new(original_blocks + continuations.len());
                                continuations.push(mir::BasicBlockData {
                                    note: Some("use returned managed reference".into()),
                                    statements: vec![mir::Statement {
                                        span,
                                        kind: mir::StatementKind::Assign(
                                            destination.clone(),
                                            mir::Rvalue::Cast {
                                                operand: Operand::Copy(Place::from_local(
                                                    reference,
                                                )),
                                                ty: body.locals[destination.local].ty,
                                                kind: mir::CastKind::Pointer,
                                            },
                                        ),
                                    }],
                                    terminator: Some(mir::Terminator {
                                        span,
                                        kind: mir::TerminatorKind::Goto { target },
                                    }),
                                });
                                let ty = gcx.get_type(reference_helper);
                                block.terminator = Some(mir::Terminator {
                                    span,
                                    kind: mir::TerminatorKind::Call {
                                        func: Operand::Constant(mir::Constant {
                                            ty,
                                            value: mir::ConstantKind::Function(
                                                reference_helper,
                                                GenericArguments::empty(),
                                                ty,
                                            ),
                                        }),
                                        args: vec![],
                                        destination: Place::from_local(reference),
                                        target: continuation,
                                        unwind: mir::CallUnwindAction::Terminate,
                                    },
                                });
                                continue;
                            }
                            block.statements.push(mir::Statement {
                                span,
                                kind: mir::StatementKind::Assign(
                                    Place::from_local(reference),
                                    mir::Rvalue::Alloc { ty: allocated_ty },
                                ),
                            });
                            let result_reference = if class_payload {
                                // Model an address of a field during construction:
                                // no class handle is published before initialization.
                                let field = body.locals.push(mir::LocalDecl {
                                    ty: Ty::new(TyKind::Reference(gcx.types.int32), gcx),
                                    kind: mir::LocalKind::Temp,
                                    mutable: true,
                                    name: None,
                                    span,
                                });
                                let mut place = Place::from_local(reference);
                                place.projection.push(mir::PlaceElem::Deref);
                                place.projection.push(mir::PlaceElem::Field(
                                    crate::thir::FieldIndex::new(2),
                                    gcx.types.int32,
                                ));
                                block.statements.push(mir::Statement {
                                    span,
                                    kind: mir::StatementKind::Assign(
                                        Place::from_local(field),
                                        mir::Rvalue::Ref { place },
                                    ),
                                });
                                field
                            } else {
                                reference
                            };
                            block.statements.push(mir::Statement {
                                span,
                                kind: mir::StatementKind::Assign(
                                    destination.clone(),
                                    mir::Rvalue::Cast {
                                        operand: Operand::Copy(Place::from_local(result_reference)),
                                        ty: body.locals[destination.local].ty,
                                        kind: mir::CastKind::Pointer,
                                    },
                                ),
                            });
                            block.terminator = Some(mir::Terminator {
                                span,
                                kind: mir::TerminatorKind::Goto { target },
                            });
                        }
                        body.basic_blocks.extend(continuations);
                    }
                }
                let result = compile_link_run(gcx, bodies, &entry, level, &runtime);
                assert_eq!(
                    result, 42,
                    "live root then exact dead-value collection, optimized={optimized}"
                );
            },
        );
    }
}

/// Lower one prepared source package with the candidate backend, link it to the
/// matched preview runtime and return the result of calling `entry`.
fn compile_link_run<'gcx>(
    gcx: GlobalContext<'gcx>,
    bodies: Vec<(hir::DefinitionID, mir::Body<'gcx>)>,
    entry: &str,
    level: u8,
    runtime: &std::path::Path,
) -> i32 {
    compile_link_run_with_metadata(gcx, bodies, entry, level, runtime, None)
}

fn compile_link_run_with_metadata<'gcx>(
    gcx: GlobalContext<'gcx>,
    bodies: Vec<(hir::DefinitionID, mir::Body<'gcx>)>,
    entry: &str,
    level: u8,
    runtime: &std::path::Path,
    hook: Option<fn(&mut crate::codegen::gc_pc_metadata::PcMetadata)>,
) -> i32 {
    let optimized = level != 0;
    let package = super::test_support::publish(gcx, bodies);
    let id = *package
        .functions
        .keys()
        .find(|&&id| gcx.definition_ident(id).symbol.as_str() == entry)
        .unwrap();
    let context = Context::create();
    let mut emitter = Emitter::new(
        &context,
        context.create_module("gc-source"),
        context.create_builder(),
        gcx,
    )
    .unwrap_or_else(|_| panic!("GC source emitter"));
    emitter.gc_metadata_test_hook = hook;
    emitter.target_machine = gcx
        .store
        .target_layout
        .create_target_machine(
            gcx.dcx(),
            if optimized {
                BuildProfile::Release
            } else {
                BuildProfile::Debug
            },
            OptimizationMode::Level(match level {
                0 => OptLevel::O0,
                2 => OptLevel::O2,
                _ => OptLevel::O3,
            }),
        )
        .unwrap_or_else(|_| panic!("GC test target machine"));

    let (function, _) =
        emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
    let name = function.get_name().to_str().unwrap().to_owned();
    emitter.lower_instances().unwrap_or_else(|_| {
        panic!(
            "GC source lowering: {:#?}",
            gcx.dcx().take_recorded_diagnostics()
        )
    });
    // Match ordinary module emission: class and erased-opening tables.
    emitter.emit_dispatch_registration_ctor();
    emitter.module.verify().unwrap();
    let ir = emitter.module.print_to_string().to_string();
    assert!(
        !ir.contains("borrow_control") && !ir.contains("__rt__borrow_"),
        "managed references must not emit native controllers"
    );
    assert!(
        !ir.contains("__rt__owned_existential"),
        "GC erased values must not emit unique native owners"
    );
    if optimized {
        emitter
            .module
            .run_passes(
                &format!("default<O{level}>"),
                &emitter.target_machine,
                PassBuilderOptions::create(),
            )
            .unwrap();
    }
    let artifact = emitter.emit_module_artifact().unwrap_or_else(|_| {
        panic!(
            "GC source object: {:#?}",
            gcx.dcx().take_recorded_diagnostics()
        )
    });
    let directory = crate::test_support::TempDir::new("gc-source-image");
    let library = directory.join(if cfg!(target_os = "macos") {
        "gc.dylib"
    } else {
        "gc.so"
    });
    // Native wrappers expose collector probes to the minimal source fixture,
    // which intentionally compiles without the standard library.
    let shim = directory.join("gc-fixture.c");
    std::fs::write(
        &shim,
        r#"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
extern void *__gc__alloc(size_t, const void *);
extern void *__gc__test_probe_create(const void *);
extern bool __gc__test_collect_probe_is_live(void *);
extern void __gc__thread_detach(void);
extern size_t __gc__test_request_collection(void);
extern size_t __gc__test_collection_count(void);
struct Descriptor { size_t size, align; const void *nodes; size_t node_count; };
static const struct Descriptor scalar = { sizeof(int32_t), _Alignof(int32_t), NULL, 0 };
int32_t *fixture_gc_allocate(void) { return __gc__alloc(sizeof(int32_t), &scalar); }
void *fixture_gc_probe(const void *p) { return __gc__test_probe_create(p); }
bool fixture_gc_live(void *p) { return __gc__test_collect_probe_is_live(p); }
void fixture_gc_detach(void) { __gc__thread_detach(); }
size_t fixture_gc_request(void) { return __gc__test_request_collection(); }
size_t fixture_gc_count(void) { return __gc__test_collection_count(); }
void fixture_gc_noop(void) {}
"#,
    )
    .unwrap();
    let mut linker = std::process::Command::new("clang");
    linker.arg(if cfg!(target_os = "macos") {
        "-dynamiclib"
    } else {
        "-shared"
    });
    for object in artifact.link_inputs() {
        linker.arg(object);
    }
    linker
        .arg(&shim)
        .arg("-funwind-tables")
        .arg(&runtime)
        .arg("-o")
        .arg(&library);
    if cfg!(target_os = "macos") {
        linker.args([
            "-liconv",
            "-framework",
            "Security",
            "-framework",
            "CoreFoundation",
        ]);
    } else {
        linker.args(["-ldl", "-lpthread", "-lm"]);
    }
    let linked = linker.output().unwrap();
    assert!(
        linked.status.success(),
        "GC source link: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    inkwell::support::load_library_permanently(&library).unwrap();
    let address =
        inkwell::support::search_for_address_of_symbol(&name).expect("source GC entry symbol");
    let run: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(address) };
    unsafe { run() }
}

/// The binding references remain inside the function. Only the scalar result
/// is copied into a separate returned cell, so return escape alone cannot
/// justify fresh storage for the loop binding.
fn install_overlapping_bindings<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut mir::Body<'ctx>,
    result: mir::LocalId,
) {
    let span = body.locals[body.return_local].span;
    let [outside, binding, index, previous] = [
        gcx.types.int32,
        gcx.types.int32,
        gcx.types.int32,
        Ty::new(TyKind::Reference(gcx.types.int32), gcx),
    ]
    .map(|ty| {
        body.locals.push(mir::LocalDecl {
            ty,
            kind: mir::LocalKind::User,
            mutable: true,
            name: None,
            span,
        })
    });
    let value = |number| {
        Operand::Constant(mir::Constant {
            ty: gcx.types.int32,
            value: mir::ConstantKind::Integer(number),
        })
    };
    let assign = |local, rvalue| mir::Statement {
        span,
        kind: mir::StatementKind::Assign(Place::from_local(local), rvalue),
    };
    let reference = |local| mir::Rvalue::Ref {
        place: Place::from_local(local),
    };
    let jump = |block| {
        Some(mir::Terminator {
            span,
            kind: mir::TerminatorKind::Goto {
                target: mir::BasicBlockId::new(block),
            },
        })
    };
    let mut previous_value = Place::from_local(previous);
    previous_value.projection.push(mir::PlaceElem::Deref);
    body.start_block = mir::BasicBlockId::new(0);
    body.basic_blocks = index_vec::IndexVec::from(vec![
        mir::BasicBlockData {
            note: Some("loop fixture entry".into()),
            statements: vec![
                mir::Statement {
                    span,
                    kind: mir::StatementKind::StorageLive(outside),
                },
                assign(outside, mir::Rvalue::Use(value(0))),
                assign(index, mir::Rvalue::Use(value(0))),
                assign(previous, reference(outside)),
            ],
            terminator: jump(1),
        },
        mir::BasicBlockData {
            note: Some("fresh binding".into()),
            statements: vec![
                mir::Statement {
                    span,
                    kind: mir::StatementKind::StorageLive(binding),
                },
                assign(
                    binding,
                    mir::Rvalue::BinaryOp {
                        op: mir::BinaryOperator::Add,
                        lhs: Operand::Copy(Place::from_local(index)),
                        rhs: value(41),
                    },
                ),
            ],
            terminator: Some(mir::Terminator {
                span,
                kind: mir::TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(index)),
                    targets: vec![(0, mir::BasicBlockId::new(2))],
                    otherwise: mir::BasicBlockId::new(3),
                },
            }),
        },
        mir::BasicBlockData {
            note: Some("retain first binding".into()),
            statements: vec![
                assign(previous, reference(binding)),
                assign(index, mir::Rvalue::Use(value(1))),
            ],
            terminator: jump(1),
        },
        mir::BasicBlockData {
            note: Some("read previous binding".into()),
            statements: vec![
                assign(result, mir::Rvalue::Use(Operand::Copy(previous_value))),
                assign(body.return_local, reference(result)),
            ],
            terminator: Some(mir::Terminator {
                span,
                kind: mir::TerminatorKind::Return,
            }),
        },
    ]);
}

/// Evaluate a constructor's next field while only its first reference field is
/// initialized. The source whole-value initialization fact must remain false.
fn install_partial_aggregate<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut mir::Body<'ctx>,
    result: mir::LocalId,
    probe_fn: hir::DefinitionID,
    collect_fn: hir::DefinitionID,
) {
    let span = body.locals[body.return_local].span;
    let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
    let pair = Ty::new(
        TyKind::Tuple(
            gcx.store
                .interners
                .intern_ty_list(vec![reference, reference]),
        ),
        gcx,
    );
    let raw = gcx.get_signature(probe_fn).inputs[0].ty;
    let probe_ty = gcx.get_signature(probe_fn).output;
    let [first, raw_first, aggregate, probe, kept] =
        [reference, raw, pair, probe_ty, gcx.types.bool].map(|ty| {
            body.locals.push(mir::LocalDecl {
                ty,
                kind: mir::LocalKind::User,
                mutable: true,
                name: None,
                span,
            })
        });
    let assign = |place, value| mir::Statement {
        span,
        kind: mir::StatementKind::Assign(place, value),
    };
    let integer = |value| {
        Operand::Constant(mir::Constant {
            ty: gcx.types.int32,
            value: mir::ConstantKind::Integer(value),
        })
    };
    let mut first_value = Place::from_local(first);
    first_value.projection.push(mir::PlaceElem::Deref);
    let mut field = Place::from_local(aggregate);
    field.projection.push(mir::PlaceElem::Field(
        crate::thir::FieldIndex::new(0),
        reference,
    ));
    let mut field_value = field.clone();
    field_value.projection.push(mir::PlaceElem::Deref);
    let call = |id, argument, destination, target| {
        let ty = gcx.get_type(id);
        Some(mir::Terminator {
            span,
            kind: mir::TerminatorKind::Call {
                func: Operand::Constant(mir::Constant {
                    ty,
                    value: mir::ConstantKind::Function(id, GenericArguments::empty(), ty),
                }),
                args: vec![Operand::Copy(Place::from_local(argument))],
                destination: Place::from_local(destination),
                target: mir::BasicBlockId::new(target),
                unwind: mir::CallUnwindAction::Terminate,
            },
        })
    };
    let finish = |value| mir::BasicBlockData {
        note: Some("finish partial constructor".into()),
        statements: vec![
            assign(Place::from_local(result), value),
            assign(
                Place::from_local(body.return_local),
                mir::Rvalue::Ref {
                    place: Place::from_local(result),
                },
            ),
        ],
        terminator: Some(mir::Terminator {
            span,
            kind: mir::TerminatorKind::Return,
        }),
    };
    body.start_block = mir::BasicBlockId::new(0);
    body.basic_blocks = index_vec::IndexVec::from(vec![
        mir::BasicBlockData {
            note: Some("initialize first field".into()),
            statements: vec![
                mir::Statement {
                    span,
                    kind: mir::StatementKind::StorageLive(aggregate),
                },
                assign(
                    Place::from_local(first),
                    mir::Rvalue::Alloc {
                        ty: gcx.types.int32,
                    },
                ),
                assign(first_value, mir::Rvalue::Use(integer(42))),
                assign(
                    field,
                    mir::Rvalue::Use(Operand::Copy(Place::from_local(first))),
                ),
                assign(
                    Place::from_local(raw_first),
                    mir::Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(first)),
                        ty: raw,
                        kind: mir::CastKind::Pointer,
                    },
                ),
            ],
            terminator: call(probe_fn, raw_first, probe, 1),
        },
        mir::BasicBlockData {
            note: Some("collect during partial construction".into()),
            statements: vec![],
            terminator: call(collect_fn, probe, kept, 2),
        },
        mir::BasicBlockData {
            note: Some("observe field survival".into()),
            statements: vec![],
            terminator: Some(mir::Terminator {
                span,
                kind: mir::TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(kept)),
                    targets: vec![(0, mir::BasicBlockId::new(4))],
                    otherwise: mir::BasicBlockId::new(3),
                },
            }),
        },
        finish(mir::Rvalue::Use(Operand::Copy(field_value))),
        finish(mir::Rvalue::UnaryOp {
            op: mir::UnaryOperator::Negate,
            operand: integer(99),
        }),
    ]);
}

// LLVM currently chooses FP-relative locations for the fixed Taro frames we
// emit. Re-express actual normalized root slots relative to SP in the test
// sidecar, then run the source through the real collector. This exercises the
// supported SP metadata ABI without a production codegen switch.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn source_sp_relative_roots_survive_collection() {
    let _guard = super::test_support::GC_TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let runtime = std::env::var_os("TARO_SP_ROOT_TEST_RUNTIME")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(gc_runtime_archive);
    let source = r#"
extern "C" {
    unsafe func fixture_gc_probe(_ target: *const int32) -> *mut uint8
    unsafe func fixture_gc_live(_ probe: *mut uint8) -> bool
    unsafe func fixture_gc_detach()
}
@noinline
func spMakeRoot() -> &int32 { var value: int32 = 42; &value }
public func exercise_sp_relative_roots() -> int32 {
    root := spMakeRoot()
    probe := unsafe { fixture_gc_probe(root as *const int32) }
    if !unsafe { fixture_gc_live(probe) } {
        unsafe { fixture_gc_detach() }
        return -1
    }
    answer := *root
    unsafe { fixture_gc_detach() }
    answer
}
func main() {}
"#;
    fn rewrite(metadata: &mut crate::codegen::gc_pc_metadata::PcMetadata) {
        let function = metadata
            .functions
            .iter_mut()
            .find(|f| f.symbol.contains("exercise_sp_relative_roots"))
            .unwrap();
        // AArch64 fixed frames put FP at entry SP - 16, and stack_size is
        // the full SP adjustment. Selector locations deliberately stay FP.
        let delta = i32::try_from(function.stack_size).unwrap() - 16;
        assert!(delta >= 0);
        let mut roots = 0;
        for record in &mut function.records {
            for root in &mut record.roots {
                assert_eq!(root.dwarf_register, 29);
                root.dwarf_register = 31;
                root.frame_offset += delta;
                roots += 1;
            }
        }
        assert!(roots > 0, "source must publish actual live roots");
    }
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        assert_eq!(
            compile_link_run_with_metadata(
                gcx,
                bodies.into_iter().map(|body| (body.owner, body)).collect(),
                "exercise_sp_relative_roots",
                0,
                &runtime,
                Some(rewrite)
            ),
            42
        );
    });
}

#[test]
fn pointer_bearing_copy_rejects_partial_word_constant() {
    let source = r#"
struct Handle { target: &int32 }
extern "taro_intrinsic" {
    unsafe func __intrinsic_memmove[T](_ dst: *mut T, _ src: *T, _ bytes: usize)
}
public func rawPartialCopy(_ dst: *mut Handle, _ src: *Handle) {
    unsafe { __intrinsic_memmove(dst, src, 7 as usize) }
}
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("partial-word"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let id = *package
            .functions
            .keys()
            .find(|&&id| gcx.definition_ident(id).symbol.as_str() == "rawPartialCopy")
            .unwrap();
        emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        assert!(
            emitter.lower_instances().is_err(),
            "partial pointer-word copy must be rejected"
        );
        assert!(
            format!("{:?}", gcx.dcx().take_recorded_diagnostics()).contains("multiple of 8 bytes")
        );
    });
}

#[test]
fn scalar_atomics_emit_sequentially_consistent_instructions() {
    let source = r#"
extern "taro_intrinsic" {
    unsafe func __intrinsic_atomic_load[T](_ slot: *const T) -> T
    unsafe func __intrinsic_atomic_store[T](_ slot: *mut T, _ value: T)
    unsafe func __intrinsic_atomic_swap[T](_ slot: *mut T, _ value: T) -> T
    unsafe func __intrinsic_atomic_compare_exchange[T](_ slot: *mut T, _ expected: T, _ desired: T) -> bool
    unsafe func __intrinsic_atomic_add[T](_ slot: *mut T, _ delta: T) -> T
}
public func atomicLoad(_ p: *int64) -> int64 { unsafe { __intrinsic_atomic_load(p) } }
public func atomicStore(_ p: *mut int64, _ v: int64) { unsafe { __intrinsic_atomic_store(p, v) } }
public func atomicSwap(_ p: *mut int64, _ v: int64) -> int64 { unsafe { __intrinsic_atomic_swap(p, v) } }
public func atomicAdd(_ p: *mut int8, _ v: int8) -> int8 { unsafe { __intrinsic_atomic_add(p, v) } }
public func atomicCas(_ p: *mut int64, _ a: int64, _ b: int64) -> bool { unsafe { __intrinsic_atomic_compare_exchange(p, a, b) } }
public func atomicPointerSwap(_ p: *mut *int32, _ v: *int32) -> *int32 { unsafe { __intrinsic_atomic_swap(p, v) } }
public func atomicPointerCas(_ p: *mut *int32, _ a: *int32, _ b: *int32) -> bool { unsafe { __intrinsic_atomic_compare_exchange(p, a, b) } }
func main() {}
"#;
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("scalar-atomic"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        for &id in package.functions.keys() {
            if gcx
                .definition_ident(id)
                .symbol
                .as_str()
                .starts_with("atomic")
            {
                emitter.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
            }
        }
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("{:?}", gcx.dcx().take_recorded_diagnostics()));
        emitter
            .module
            .verify()
            .expect("valid scalar atomic instructions");
        let ir = emitter.module.print_to_string().to_string();
        for instruction in [
            "load atomic i64",
            "store atomic i64",
            "atomicrmw xchg",
            "atomicrmw add",
            "cmpxchg",
            "seq_cst seq_cst",
        ] {
            assert!(ir.contains(instruction), "missing {instruction}: {ir}");
        }
        assert!(!ir.contains("__rt__atomic"), "{ir}");
    });
}

#[test]
fn enum_projection_substitutes_the_generic_base_before_downcast() {
    let source = "enum Choice { case payload(int32) }\nfunc shape[T](_ value: T) -> T { value }\nfunc main() {}";
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |package, bodies, gcx| {
        let choice = gcx.get_type(package.root.declarations[0].id);
        let body = bodies
            .iter()
            .find(|body| gcx.definition_ident(body.owner).symbol.as_str() == "shape")
            .unwrap();
        let parameter = body
            .locals
            .iter_enumerated()
            .find(|(_, local)| local.kind == mir::LocalKind::Param)
            .unwrap()
            .0;
        let place = Place {
            local: parameter,
            projection: vec![mir::PlaceElem::VariantDowncast {
                name: gcx.intern_symbol("payload"),
                index: crate::thir::VariantIndex::from_raw(0),
            }],
        };
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("generic-enum-place"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        emitter.current_subst = gcx
            .store
            .interners
            .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(choice)]);
        assert_eq!(
            emitter.place_ty(body, &place),
            Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![gcx.types.int32])),
                gcx
            )
        );
    });
}
