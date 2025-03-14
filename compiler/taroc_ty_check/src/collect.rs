use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DeclarationContext, DeclarationKind, DefinitionID, Enum, NodeID, Package, Struct,
    TypeParameterKind, TypeParameters, visitor::HirVisitor,
};
use taroc_span::Symbol;
use taroc_types::{AdtKind, GenericArgument, Ty, TyKind};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    TypeCollector::run(package, context)
}

/// This Pass, Collects top level symbols  & converts them to `types::Ty`
///
/// Once Converted they are mapped as `hir::DefinitionID` -> `types::Ty`
struct TypeCollector<'ctx> {
    context: GlobalContext<'ctx>,
    table: FxHashMap<DefinitionID, Ty<'ctx>>,
}

impl TypeCollector<'_> {
    fn new<'a>(context: GlobalContext<'a>) -> TypeCollector<'a> {
        TypeCollector {
            context,
            table: Default::default(),
        }
    }

    fn run<'a>(package: &Package, context: GlobalContext<'a>) -> CompileResult<()> {
        let mut actor = TypeCollector::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for TypeCollector<'_> {
    fn visit_declaration(&mut self, d: &Declaration, _c: DeclarationContext) -> Self::Result {
        match &d.kind {
            // DeclarationKind::Struct(node) => self.collect_struct(&d.id, node, d),
            // DeclarationKind::Enum(node) => self.collect_enum(&d.id, node, d),
            DeclarationKind::Module(node) => self.visit_module(&node, d.id),
            _ => {}
        }
    }
}

impl<'ctx> TypeCollector<'ctx> {
    fn def_id(&self, node: &NodeID) -> DefinitionID {
        todo!()
    }

    fn tag(&mut self, node: &NodeID, ty: Ty<'ctx>) {
        let id = self.def_id(node);
        self.table.insert(id, ty);
    }
}

// impl<'ctx> TypeCollector<'ctx> {
//     fn collect_struct(&mut self, id: &NodeID, _node: &Struct, decl: &Declaration) {
//         if self.context.config.is_std
//             && let Some(builtin) = self.check_builtin(decl.identifier.symbol)
//         {
//             self.tag(id, builtin);
//         } else {
//             let arguments = self.collect_type_parameters(&_node.generics.parameters);
//             let arguments = self.context.type_store.interners.mk_args(arguments);
//             let kind = TyKind::Adt {
//                 id: self.def_id(id),
//                 name: decl.identifier.symbol,
//                 kind: AdtKind::Struct,
//                 arguments,
//             };
//             let ty = self.context.type_store.interners.intern_ty(kind);
//             self.tag(id, ty);
//         }
//     }

//     fn collect_enum(&mut self, id: &NodeID, _node: &Enum, decl: &Declaration) {
//         let arguments = self.collect_type_parameters(&_node.generics.parameters);
//         let arguments = self.context.type_store.interners.mk_args(arguments);

//         let kind = TyKind::Adt {
//             id: self.def_id(id),
//             name: decl.identifier.symbol,
//             kind: AdtKind::Enum,
//             arguments,
//         };
//         let ty = self.context.type_store.interners.intern_ty(kind);
//         self.tag(id, ty);
//     }

//     fn check_builtin(&self, symbol: Symbol) -> Option<Ty<'ctx>> {
//         let value = match symbol.as_str() {
//             "Bool" => self.context.type_store.common.bool,
//             "Rune" => self.context.type_store.common.rune,
//             "Void" => self.context.type_store.common.void,
//             "UInt" => self.context.type_store.common.uint,
//             "UInt8" => self.context.type_store.common.uint8,
//             "UInt16" => self.context.type_store.common.uint16,
//             "UInt32" => self.context.type_store.common.uint32,
//             "UInt64" => self.context.type_store.common.uint64,
//             "Int" => self.context.type_store.common.int,
//             "Int8" => self.context.type_store.common.int8,
//             "Int16" => self.context.type_store.common.int16,
//             "Int32" => self.context.type_store.common.int32,
//             "Int64" => self.context.type_store.common.int64,
//             "Float32" => self.context.type_store.common.float32,
//             "Float64" => self.context.type_store.common.float64,
//             _ => return None,
//         };

//         return Some(value);
//     }
// }
// impl<'ctx> TypeCollector<'ctx> {
//     // Return an owned Vec instead of a borrowed slice.
//     fn collect_type_parameters(
//         &mut self,
//         parameters: &TypeParameters,
//     ) -> Vec<GenericArgument<'ctx>> {
//         let mut arguments = Vec::new();

//         for parameter in parameters.parameters.iter() {
//             match parameter.kind {
//                 TypeParameterKind::Type { .. } => {
//                     let kind = TyKind::Parameter;
//                     let ty = self.context.type_store.interners.intern_ty(kind);
//                     self.tag(&parameter.id, ty);
//                     let argument = types::GenericArgument::Type(ty);
//                     arguments.push(argument);
//                 }
//                 TypeParameterKind::Constant { .. } => {
//                     continue;
//                 }
//             }
//         }

//         arguments
//     }
// }
