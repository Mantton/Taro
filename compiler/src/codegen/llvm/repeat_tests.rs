use super::*;

/// Nonzero repeats previously interned a distinct full array after each insert,
/// exhausting compiler memory before the byte-storage stress fixture could run.
/// Run this focused regression under the same RSS guard as the GC tests.
#[test]
fn large_scalar_repeat_builds_a_single_constant_array() {
    crate::mir::test_support::with_test_gcx(|gcx| {
        let context = Context::create();
        let module = context.create_module("large-scalar-repeat");
        let mut emitter = Emitter::new(&context, module, context.create_builder(), gcx)
            .unwrap_or_else(|_| panic!("repeat emitter"));
        let body = crate::mir::test_support::minimal_body(gcx);
        let count = 8192;
        let ty = Ty::new(
            TyKind::Array {
                element: gcx.types.uint8,
                len: crate::sema::models::Const {
                    ty: gcx.types.uint,
                    kind: ConstKind::Value(ConstValue::Integer(count as _)),
                },
            },
            gcx,
        );
        let repeated = emitter
            .lower_rvalue(
                &body,
                &mut [],
                ty,
                &mir::Rvalue::Repeat {
                    operand: Operand::Constant(mir::Constant {
                        ty: gcx.types.uint8,
                        value: mir::ConstantKind::Integer(7),
                    }),
                    count,
                    element: gcx.types.uint8,
                },
            )
            .unwrap_or_else(|_| panic!("repeat lowering"))
            .unwrap()
            .into_array_value();
        assert_eq!(repeated.get_type().len(), count as u32);
        let expected = context
            .i8_type()
            .const_array(&vec![context.i8_type().const_int(7, false); count]);
        assert_eq!(repeated, expected);
        emitter.module.verify().unwrap();
    });
}
