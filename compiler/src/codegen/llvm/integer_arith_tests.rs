use super::*;

/// The overflow-tolerant std integer methods rely on these intrinsics lowering
/// to plain LLVM arithmetic or to the overflow flag only, never to a checked
/// operation with a panic branch, whatever the package's overflow policy.
#[test]
fn wrapping_and_overflow_flag_intrinsics_never_branch_to_a_panic() {
    use inkwell::values::AnyValue;
    let source = r#"
extern "taro_intrinsic" {
    func __intrinsic_wrapping_add[T](_ lhs: T, _ rhs: T) -> T
    func __intrinsic_wrapping_sub[T](_ lhs: T, _ rhs: T) -> T
    func __intrinsic_wrapping_mul[T](_ lhs: T, _ rhs: T) -> T
    func __intrinsic_overflows_add[T](_ lhs: T, _ rhs: T) -> bool
    func __intrinsic_overflows_sub[T](_ lhs: T, _ rhs: T) -> bool
    func __intrinsic_overflows_mul[T](_ lhs: T, _ rhs: T) -> bool
}
public func wrapAdd(_ a: int8, _ b: int8) -> int8 { __intrinsic_wrapping_add(a, b) }
public func wrapSub(_ a: uint16, _ b: uint16) -> uint16 { __intrinsic_wrapping_sub(a, b) }
public func wrapMul(_ a: int64, _ b: int64) -> int64 { __intrinsic_wrapping_mul(a, b) }
public func ovfAdd(_ a: uint32, _ b: uint32) -> bool { __intrinsic_overflows_add(a, b) }
public func ovfSub(_ a: int16, _ b: int16) -> bool { __intrinsic_overflows_sub(a, b) }
public func ovfMul(_ a: int64, _ b: int64) -> bool { __intrinsic_overflows_mul(a, b) }
func main() {}
"#;
    let expected = [
        ("wrapAdd", "add i8"),
        ("wrapSub", "sub i16"),
        ("wrapMul", "mul i64"),
        ("ovfAdd", "@llvm.uadd.with.overflow.i32"),
        ("ovfSub", "@llvm.ssub.with.overflow.i16"),
        ("ovfMul", "@llvm.smul.with.overflow.i64"),
    ];
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("integer-arith-intrinsics"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let functions: Vec<_> = expected
            .into_iter()
            .map(|(name, instruction)| {
                let id = *package
                    .functions
                    .keys()
                    .find(|&&id| gcx.symbol_text(gcx.definition_ident(id).symbol).as_str() == name)
                    .unwrap();
                let (function, _) = emitter
                    .instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
                (name, instruction, function)
            })
            .collect();
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        for (name, instruction, function) in functions {
            let ir = function.print_to_string().to_string();
            assert!(ir.contains(instruction), "{name}: {ir}");
            assert!(!ir.contains("ovf_panic"), "{name}: {ir}");
            if name.starts_with("wrap") {
                assert!(!ir.contains(".with.overflow"), "{name}: {ir}");
            }
        }
    });
}

#[test]
fn bit_manipulation_intrinsics_lower_to_llvm_instructions() {
    use inkwell::values::AnyValue;
    let source = r#"
extern "taro_intrinsic" {
    func __intrinsic_ctpop[T](_ value: T) -> uint32
    func __intrinsic_ctlz[T](_ value: T) -> uint32
    func __intrinsic_cttz[T](_ value: T) -> uint32
    func __intrinsic_bswap[T](_ value: T) -> T
    func __intrinsic_bitreverse[T](_ value: T) -> T
    func __intrinsic_fshl[T](_ hi: T, _ lo: T, _ shift: uint32) -> T
    func __intrinsic_fshr[T](_ hi: T, _ lo: T, _ shift: uint32) -> T
}
public func pop8(_ a: uint8) -> uint32 { __intrinsic_ctpop(a) }
public func pop64(_ a: int64) -> uint32 { __intrinsic_ctpop(a) }
public func lz16(_ a: uint16) -> uint32 { __intrinsic_ctlz(a) }
public func tz32(_ a: int32) -> uint32 { __intrinsic_cttz(a) }
public func swap8(_ a: uint8) -> uint8 { __intrinsic_bswap(a) }
public func swap32(_ a: uint32) -> uint32 { __intrinsic_bswap(a) }
public func rev8(_ a: int8) -> int8 { __intrinsic_bitreverse(a) }
public func rotl8(_ a: uint8, _ n: uint32) -> uint8 { __intrinsic_fshl(a, a, n) }
public func rotr64(_ a: uint64, _ n: uint32) -> uint64 { __intrinsic_fshr(a, a, n) }
func main() {}
"#;
    let expected = [
        ("pop8", "@llvm.ctpop.i8"),
        ("pop64", "@llvm.ctpop.i64"),
        ("lz16", "@llvm.ctlz.i16"),
        ("tz32", "@llvm.cttz.i32"),
        ("swap32", "@llvm.bswap.i32"),
        ("rev8", "@llvm.bitreverse.i8"),
        ("rotl8", "@llvm.fshl.i8"),
        ("rotr64", "@llvm.fshr.i64"),
    ];
    crate::test_support::analyze_native_class_fixture(source, &[], &[], |_, bodies, gcx| {
        let package = super::test_support::publish(
            gcx,
            bodies.into_iter().map(|body| (body.owner, body)).collect(),
        );
        let context = Context::create();
        let mut emitter = Emitter::new(
            &context,
            context.create_module("integer-bit-intrinsics"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("emitter"));
        let functions: Vec<_> = expected
            .into_iter()
            .map(|(name, instruction)| {
                let id = *package
                    .functions
                    .keys()
                    .find(|&&id| gcx.symbol_text(gcx.definition_ident(id).symbol).as_str() == name)
                    .unwrap();
                let (function, _) = emitter
                    .instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
                (name, instruction, function)
            })
            .collect();
        let swap8_id = *package
            .functions
            .keys()
            .find(|&&id| gcx.symbol_text(gcx.definition_ident(id).symbol).as_str() == "swap8")
            .unwrap();
        let (swap8_fn, _) = emitter
            .instance_function_with_abi(Instance::item(swap8_id, GenericArguments::empty()));
        emitter
            .lower_instances()
            .unwrap_or_else(|_| panic!("lowering"));
        emitter.module.verify().unwrap();
        for (name, instruction, function) in functions {
            let ir = function.print_to_string().to_string();
            assert!(ir.contains(instruction), "{name}: {ir}");
            if name == "lz16" || name == "tz32" {
                assert!(ir.contains("i1 false"), "{name} must pass is_zero_poison=false: {ir}");
            }
        }
        let swap8_ir = swap8_fn.print_to_string().to_string();
        assert!(
            !swap8_ir.contains("llvm.bswap"),
            "i8 bswap must lower to identity: {swap8_ir}"
        );
    });
}
