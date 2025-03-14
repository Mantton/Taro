use std::rc::Rc;

use rustc_hash::FxHashMap;
use taroc_context::CompilerSession;
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DeclarationContext, DeclarationKind, DefinitionID, Enum, NodeID, Package, Struct,
    TypeParameterKind, TypeParameters, visitor::HirVisitor,
};
use taroc_span::Symbol;
use taroc_types::{AdtData, AdtKind, GenericArgument, Ty, TyKind};

pub fn run(package: &taroc_hir::Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    TypeCollector::run(package, session)
}

/// This Pass, Collects top level symbols  & converts them to `types::Ty`
///
/// Once Converted they are mapped as `hir::DefinitionID` -> `types::Ty`
struct TypeCollector<'ctx> {
    session: Rc<CompilerSession<'ctx>>,
    table: FxHashMap<DefinitionID, Ty<'ctx>>,
}

impl<'ctx> TypeCollector<'ctx> {
    fn new(session: Rc<CompilerSession<'ctx>>) -> TypeCollector<'ctx> {
        TypeCollector {
            session,
            table: Default::default(),
        }
    }

    fn run<'a>(package: &Package, session: Rc<CompilerSession<'ctx>>) -> CompileResult<()> {
        let mut actor = TypeCollector::new(session.clone());
        taroc_hir::visitor::walk_package(&mut actor, package);
        session.context.diagnostics.report()
    }
}

impl HirVisitor for TypeCollector<'_> {
    fn visit_declaration(&mut self, d: &Declaration, _c: DeclarationContext) -> Self::Result {
        match &d.kind {
            DeclarationKind::Struct(node) => self.collect_struct(&d.id, node, d),
            DeclarationKind::Enum(node) => self.collect_enum(&d.id, node, d),
            DeclarationKind::Module(node) => self.visit_module(&node, d.id),
            _ => {}
        }
    }
}

impl<'ctx> TypeCollector<'ctx> {
    fn def_id(&self, node: &NodeID) -> DefinitionID {
        let resolutions = self.session.context.store.resolutions.borrow();
        let resolutions = resolutions
            .get(&self.session.index)
            .expect("resolution data");

        *resolutions.node_to_def.get(node).expect("nodeid")
    }

    fn tag(&mut self, node: &NodeID, ty: Ty<'ctx>) {
        let id = self.def_id(node);
        self.table.insert(id, ty);
    }
}

impl<'ctx> TypeCollector<'ctx> {
    fn collect_struct(&mut self, id: &NodeID, _node: &Struct, decl: &Declaration) {
        if self.session.config.is_std
            && let Some(builtin) = self.check_builtin(decl.identifier.symbol)
        {
            self.tag(id, builtin);
        } else {
            let arguments = self.collect_type_parameters(&_node.generics.parameters);
            let arguments = self.session.context.store.interners.mk_args(arguments);
            let data = AdtData {
                id: self.def_id(id),
                name: decl.identifier.symbol,
                kind: AdtKind::Struct,
            };
            let kind = TyKind::Adt(data, arguments);
            let ty = self.session.context.store.interners.intern_ty(kind);
            self.tag(id, ty);
        }
    }

    fn collect_enum(&mut self, id: &NodeID, _node: &Enum, decl: &Declaration) {
        let arguments = self.collect_type_parameters(&_node.generics.parameters);
        let arguments = self.session.context.store.interners.mk_args(arguments);
        let data = AdtData {
            id: self.def_id(id),
            name: decl.identifier.symbol,
            kind: AdtKind::Enum,
        };
        let kind = TyKind::Adt(data, arguments);
        let ty = self.session.context.store.interners.intern_ty(kind);
        self.tag(id, ty);
    }

    fn check_builtin(&self, symbol: Symbol) -> Option<Ty<'ctx>> {
        let store = &self.session.context.store;
        let value = match symbol.as_str() {
            "Bool" => store.common_types.bool,
            "Rune" => store.common_types.rune,
            "Void" => store.common_types.void,
            "UInt" => store.common_types.uint,
            "UInt8" => store.common_types.uint8,
            "UInt16" => store.common_types.uint16,
            "UInt32" => store.common_types.uint32,
            "UInt64" => store.common_types.uint64,
            "Int" => store.common_types.int,
            "Int8" => store.common_types.int8,
            "Int16" => store.common_types.int16,
            "Int32" => store.common_types.int32,
            "Int64" => store.common_types.int64,
            "Float32" => store.common_types.float32,
            "Float64" => store.common_types.float64,
            _ => return None,
        };

        return Some(value);
    }
}
impl<'ctx> TypeCollector<'ctx> {
    // Return an owned Vec instead of a borrowed slice.
    fn collect_type_parameters(
        &mut self,
        parameters: &TypeParameters,
    ) -> Vec<GenericArgument<'ctx>> {
        let mut arguments = Vec::new();

        for parameter in parameters.parameters.iter() {
            match parameter.kind {
                TypeParameterKind::Type { .. } => {
                    let kind = TyKind::Parameter;
                    let ty = self.session.context.store.interners.intern_ty(kind);
                    self.tag(&parameter.id, ty);
                    let argument = GenericArgument::Type(ty);
                    arguments.push(argument);
                }
                TypeParameterKind::Constant { .. } => {
                    continue;
                }
            }
        }

        arguments
    }
}
