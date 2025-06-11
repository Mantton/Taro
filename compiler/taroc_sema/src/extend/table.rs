use crate::freshen::TypeFreshener;
use crate::ty::{Constraint, SimpleType};
use crate::utils::labeled_signature_to_ty;
use crate::{GlobalContext, ty::Ty};
use rustc_hash::{FxHashMap, FxHasher};
use std::hash::{Hash, Hasher};
use taroc_error::CompileResult;
use taroc_hir::{
    DefinitionID, OperatorKind,
    visitor::{HirVisitor, walk_declaration},
};
use taroc_span::{Identifier, Span, Spanned, Symbol};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    package: PackageOverloadTable,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            package: Default::default(),
        }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &taroc_hir::Declaration) -> Self::Result {
        let def_id = self.context.def_id(declaration.id);

        match &declaration.kind {
            taroc_hir::DeclarationKind::Function(node) => {
                self.collect_top_level_function(def_id, declaration.identifier, node)
            }
            _ => {
                walk_declaration(self, declaration);
            }
        }
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        context: taroc_hir::visitor::AssocContext,
    ) -> Self::Result {
        match context {
            taroc_hir::visitor::AssocContext::Interface(..) => {
                self.collect_interface_requirement(declaration);
            }
            taroc_hir::visitor::AssocContext::Extend(parent_id) => {
                let parent_id = self.context.def_id(parent_id);
                self.collect_extended_member(declaration, parent_id);
            }
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_interface_requirement(&self, _: &taroc_hir::AssociatedDeclaration) {

        // match &declaration.kind {
        //     taroc_hir::AssociatedDeclarationKind::Constant(node) => todo!(),
        //     taroc_hir::AssociatedDeclarationKind::Function(node) => todo!(),
        //     taroc_hir::AssociatedDeclarationKind::Type(node) => todo!(),
        //     taroc_hir::AssociatedDeclarationKind::Operator(op, node) => todo!(),
        // }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_extended_member(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        parent: DefinitionID,
    ) {
        let gcx = self.context;
        let assoc_id = gcx.def_id(declaration.id);
        let extension_id = parent;

        match &declaration.kind {
            taroc_hir::AssociatedDeclarationKind::Function(node) => {
                self.collect_assoc_function(assoc_id, extension_id, declaration.identifier, node);
            }
            taroc_hir::AssociatedDeclarationKind::Operator(op, node) => {
                self.collect_assoc_operator(
                    assoc_id,
                    extension_id,
                    *op,
                    declaration.identifier.span,
                    node,
                );
            }
            _ => {}
        }
    }
}
impl<'ctx> Actor<'ctx> {
    fn collect_assoc_function(
        &mut self,
        assoc_id: DefinitionID,
        extension_id: DefinitionID,
        ident: Identifier,
        _: &taroc_hir::Function,
    ) {
        let gcx = self.context;
        let type_key = gcx.with_type_database(extension_id.package(), |db| {
            db.extension_ty_map[&extension_id]
        });

        let (overload_key, fingerprint) = self.key_for(assoc_id);
        let member_index = self.package.methods.entry(type_key).or_default(); // member index for type
        let symbol_set = member_index.functions.entry(ident.symbol).or_default(); // overload sets of function name
        let overload_data = symbol_set.signatures.entry(overload_key).or_default(); // overload data containing members matching arity and arguments

        let previous = overload_data.fingerprints.insert(fingerprint, assoc_id);
        if let Some(previous) = previous {
            let message = format!("invalid redeclaration of '{}'", ident.symbol);
            gcx.diagnostics.error(message, ident.span);

            let message = format!("'{}' is initially defined here", ident.symbol);
            gcx.diagnostics.info(message, gcx.ident_for(previous).span);
        }

        overload_data.members.push(assoc_id);
        symbol_set.members.push(assoc_id);
    }

    fn collect_assoc_operator(
        &mut self,
        assoc_id: DefinitionID,
        extension_id: DefinitionID,
        op: OperatorKind,
        span: Span,
        _: &taroc_hir::Function,
    ) {
        let gcx = self.context;
        let type_key = gcx.with_type_database(extension_id.package(), |db| {
            db.extension_ty_map[&extension_id]
        });

        let (overload_key, fingerprint) = self.key_for(assoc_id);
        let member_index = self.package.methods.entry(type_key).or_default(); // member index for type
        let symbol_set = member_index.operators.entry(op).or_default(); // overload sets of function name
        let overload_data = symbol_set.signatures.entry(overload_key).or_default(); // overload data containing members matching arity and arguments

        let previous = overload_data.fingerprints.insert(fingerprint, assoc_id);
        if let Some(previous) = previous {
            let message = format!("invalid redeclaration operator '{:?}'", op);
            gcx.diagnostics.error(message, span);

            let message = format!("'{:?}' operator signature is initially defined here", op);
            gcx.diagnostics.info(message, gcx.ident_for(previous).span);
        }

        overload_data.members.push(assoc_id);
        symbol_set.members.push(assoc_id);
    }

    fn collect_top_level_function(
        &mut self,
        def_id: DefinitionID,
        ident: Identifier,
        _: &taroc_hir::Function,
    ) {
        let gcx = self.context;

        let (overload_key, fingerprint) = self.key_for(def_id);
        let symbol_set = self.package.functions.entry(ident.symbol).or_default(); // table for top level symbols with name
        let overload_data = symbol_set.signatures.entry(overload_key).or_default(); // overload data containing members matching arity and arguments

        let previous = overload_data.fingerprints.insert(fingerprint, def_id);
        if let Some(previous) = previous {
            let message = format!("invalid redeclaration of '{}'", ident.symbol);
            gcx.diagnostics.error(message, ident.span);

            let message = format!("'{}' is initially defined here", ident.symbol);
            gcx.diagnostics.info(message, gcx.ident_for(previous).span);
        }

        overload_data.members.push(def_id);
        symbol_set.members.push(def_id);
    }

    fn key_for(&self, id: DefinitionID) -> (OverloadKey, u64) {
        let gcx = self.context;
        let signature = gcx.fn_signature(id);
        let generics = gcx.generics_of(id);

        let has_self = generics.has_self;

        let arity = if has_self {
            signature.inputs.len() - 1
        } else {
            signature.inputs.len()
        };

        let labels: Vec<_> = signature
            .inputs
            .iter()
            .skip(if has_self { 1 } else { 0 })
            .map(|param| param.label)
            .collect();

        // Produce Fingerprint based on Predicates, Generic Count and Signature
        let predicates = gcx.canon_predicates_of(id);
        let generic_count = if generics.has_self {
            generics.parameters.len() - 1
        } else {
            generics.parameters.len()
        };

        let fn_ty = labeled_signature_to_ty(signature, gcx); // TODO: Freshen
        let mut freshener = TypeFreshener::new(gcx);
        let signature = freshener.freshen(fn_ty);

        // Fingerprint takes into account -> Predicates, Type Params, Inputs, Output
        let fingerprint = LeanSignature {
            generic_count,
            signature,
            predicates,
        }
        .fingerprint();

        let overload_key = OverloadKey { arity, labels };
        (overload_key, fingerprint)
    }
}

// Package Level Structure Holding Ty -> Members
#[derive(Default)]
struct PackageOverloadTable {
    functions: FxHashMap<Symbol, OverloadSymbolSet>,
    methods: FxHashMap<SimpleType, TypeMemberIndex>,
}

// Per Member Structure holding associated members
#[derive(Default)]
struct TypeMemberIndex {
    // constants: FxHashMap<Symbol, !>
    functions: FxHashMap<Symbol, OverloadSymbolSet>,
    operators: FxHashMap<OperatorKind, OverloadSymbolSet>,
}

#[derive(Default)]
struct OverloadSymbolSet {
    pub members: Vec<DefinitionID>, // all members for this symbol
    pub signatures: FxHashMap<OverloadKey, OverloadKeyData>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct OverloadKey {
    pub arity: usize,
    pub labels: Vec<Option<Symbol>>,
}

#[derive(Default)]
struct OverloadKeyData {
    members: Vec<DefinitionID>,
    fingerprints: FxHashMap<u64, DefinitionID>,
}

struct LeanSignature<'ctx> {
    generic_count: usize,
    signature: Ty<'ctx>,
    predicates: &'ctx Vec<Spanned<Constraint<'ctx>>>,
}

impl<'ctx> LeanSignature<'ctx> {
    /// Computes a 64-bit fingerprint of the entire signature,
    /// combining ordered fields and an order-independent sum of constraints.
    pub fn fingerprint(&self) -> u64 {
        // 1) Hash the ordered fields into the main hasher
        let mut main_hasher = FxHasher::default();
        self.generic_count.hash(&mut main_hasher);
        self.signature.hash(&mut main_hasher);

        // 2) Commutatively combine each constraint’s hash
        let mut acc: u64 = 0;
        for sp in self.predicates.iter() {
            let mut h = FxHasher::default();
            sp.value.hash(&mut h);
            acc = acc.wrapping_add(h.finish());
        }

        // 3) Fold the accumulator into the main hasher and finalize
        main_hasher.write_u64(acc);
        main_hasher.finish()
    }
}
