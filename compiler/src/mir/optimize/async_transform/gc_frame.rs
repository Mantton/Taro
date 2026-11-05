//! Fresh GC frame allocation, separate from the migration GC allocator.
use super::*;
use crate::sema::models::{
    GenericParameterDefinition, GenericParameterDefinitionKind, Generics, SyntheticDefinition,
    SyntheticDefinitionKind,
};

const ALLOCATOR: &str = "$gcAsyncFrameAllocate";

fn allocator(gcx: Gcx<'_>, span: Span) -> DefinitionID {
    if let Some(id) = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .find_map(|(id, def)| {
            (id.package() == gcx.package_index()
                && def.signature.abi == Some(crate::hir::Abi::Intrinsic)
                && gcx.symbol_eq(def.name, ALLOCATOR))
            .then_some(*id)
        })
    {
        return id;
    }
    let id = gcx.allocate_synthetic_id(gcx.package_index());
    let parameter = gcx.allocate_synthetic_id(gcx.package_index());
    let name = gcx.intern_symbol("Frame");
    let generics = gcx.store.arenas.generics.alloc(Generics {
        parameters: vec![GenericParameterDefinition {
            name,
            id: parameter,
            index: 0,
            kind: GenericParameterDefinitionKind::Type { default: None },
        }],
        has_self: false,
        parent: None,
        parent_count: 0,
    });
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(LabeledFunctionSignature {
            inputs: vec![],
            output: raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
            is_variadic: false,
            abi: Some(crate::hir::Abi::Intrinsic),
        });
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind: SyntheticDefinitionKind::Ordinary,
            name: gcx.intern_symbol(ALLOCATOR),
            generics,
            signature,
            span,
        },
    );
    gcx.with_session_type_database(|db| {
        db.def_to_unsafe.insert(id);
    });
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
    id
}

/// Allocation publishes zero-safe tracing bytes before any incoming value can
/// move out of its caller root. The create_owned call later consumes this exact
/// owner; a data pointer is never adopted into another allocation family.
pub(super) fn install<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    frame: Ty<'ctx>,
    entry: BasicBlockId,
    initialized: BasicBlockId,
    owner: LocalId,
    bytes: LocalId,
    typed: LocalId,
    span: Span,
) {
    let pointer = raw_ptr_ty(gcx, frame, crate::hir::Mutability::Mutable);
    let cast = body.basic_blocks.push(BasicBlockData {
        note: Some("GC frame data from its unique owner".into()),
        statements: vec![Statement {
            span,
            kind: StatementKind::Assign(
                Place::from_local(typed),
                Rvalue::Cast {
                    operand: Operand::Copy(Place::from_local(bytes)),
                    ty: pointer,
                    kind: crate::mir::CastKind::Pointer,
                },
            ),
        }],
        terminator: Some(Terminator {
            span,
            kind: TerminatorKind::Goto {
                target: initialized,
            },
        }),
    });
    let query = find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::FrameData, span);
    let data = body.basic_blocks.push(BasicBlockData {
        note: Some("query GC frame allocation data".into()),
        statements: vec![],
        terminator: Some(Terminator {
            span,
            kind: TerminatorKind::Call {
                func: fn_operand(query, GenericArguments::empty(), gcx.get_type(query)),
                args: vec![Operand::Copy(Place::from_local(owner))],
                destination: Place::from_local(bytes),
                target: cast,
                unwind: CallUnwindAction::Terminate,
            },
        }),
    });
    let allocate = allocator(gcx, span);
    let arguments = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(frame)]);
    body.basic_blocks[entry].statements.clear();
    body.basic_blocks[entry].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Call {
            func: fn_operand(allocate, arguments, gcx.get_type(allocate)),
            args: vec![],
            destination: Place::from_local(owner),
            target: data,
            unwind: CallUnwindAction::Terminate,
        },
    });
}
