use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    mir::{Body, Constant, ConstantKind, Operand, Rvalue, StatementKind, TerminatorKind},
    sema::models::{GenericArgument, GenericArguments},
    specialize::{Instance, resolve_instance},
};
use rustc_hash::FxHashSet;
use std::mem;

/// Collects all function instantiations needed for a MIR package.
///
/// Implements a reachability analysis:
/// 1. Start with concrete entry points (roots)
/// 2. Scan each instance's MIR for generic calls
/// 3. Add discovered instantiations to worklist
/// 4. Repeat until fixpoint
pub fn collect_instances<'ctx>(package: &crate::mir::MirPackage<'ctx>, gcx: GlobalContext<'ctx>) {
    let mut collector = Collector {
        gcx,
        items: FxHashSet::default(),
        worklist: Vec::new(),
    };

    // 1. Find roots: concrete entry points
    collector.find_roots(package);

    // 2. Worklist algorithm: visit each instance, discover calls
    while let Some(instance) = collector.worklist.pop() {
        if collector.items.contains(&instance) {
            continue;
        }

        collector.items.insert(instance);

        // Get the MIR body for this function.
        let def_id = instance.def_id();
        let body = collector.mir_body(def_id);
        collector.visit_body(instance, body);
    }

    let instances = mem::take(&mut collector.items);
    gcx.cache_specializations(gcx.package_index(), instances);
}

pub struct Collector<'ctx> {
    gcx: GlobalContext<'ctx>,
    /// Discovered instances
    items: FxHashSet<Instance<'ctx>>,
    /// Worklist for graph traversal
    worklist: Vec<Instance<'ctx>>,
}

impl<'ctx> Collector<'ctx> {
    /// Find concrete entry points (roots of the reachability graph).
    fn find_roots(&mut self, package: &crate::mir::MirPackage<'ctx>) {
        // Add the entry point if it exists and is concrete
        if let Some(entry_id) = package.entry {
            let generics = self.gcx.generics_of(entry_id);
            if generics.is_empty() {
                let root = Instance::item(entry_id, &[]);
                self.worklist.push(root);
            }
        }

        // Add all other concrete (non-generic) functions
        for (&def_id, _) in &package.functions {
            let generics = self.gcx.generics_of(def_id);
            if generics.is_empty() {
                let root = Instance::item(def_id, &[]);
                if !self.items.contains(&root) {
                    self.worklist.push(root);
                }
            }
        }
    }

    /// Visit a body and discover generic calls.
    fn visit_body(&mut self, parent: Instance<'ctx>, body: &Body<'ctx>) {
        // Walk all blocks
        for block in &body.basic_blocks {
            // Check statements
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind {
                    self.visit_rvalue(parent, rvalue);
                }
            }

            // Check terminator
            if let Some(terminator) = &block.terminator {
                match &terminator.kind {
                    TerminatorKind::Call { func, args, .. } => {
                        self.visit_operand(parent, func);
                        for arg in args {
                            self.visit_operand(parent, arg);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// Visit an operand, looking for function constants.
    fn visit_operand(&mut self, parent: Instance<'ctx>, operand: &Operand<'ctx>) {
        if let Operand::Constant(constant) = operand {
            self.visit_constant(parent, constant);
        }
    }

    /// Visit a constant, extracting generic function calls.
    fn visit_constant(&mut self, parent: Instance<'ctx>, constant: &Constant<'ctx>) {
        if let ConstantKind::Function(callee_id, call_args, _) = constant.value {
            // Only process if there are generic arguments
            if !call_args.is_empty() {
                // Substitute parent's types into the call's arguments
                let concrete_args = self.substitute_args(parent, call_args);

                // Compute the instantiation key
                let instance = self.compute_instance(callee_id, concrete_args);
                if instance.is_item() && !self.items.contains(&instance) {
                    self.worklist.push(instance);
                }
            }
        }
    }

    /// Visit an rvalue, looking for nested operands.
    fn visit_rvalue(&mut self, parent: Instance<'ctx>, rvalue: &Rvalue<'ctx>) {
        match rvalue {
            Rvalue::Use(op) => self.visit_operand(parent, op),
            Rvalue::UnaryOp { operand, .. } => self.visit_operand(parent, operand),
            Rvalue::BinaryOp { lhs, rhs, .. } => {
                self.visit_operand(parent, lhs);
                self.visit_operand(parent, rhs);
            }
            Rvalue::Cast { operand, .. } => self.visit_operand(parent, operand),
            Rvalue::Aggregate { fields, .. } => {
                for field in fields {
                    self.visit_operand(parent, field);
                }
            }
            _ => {}
        }
    }

    fn mir_body(&self, def_id: DefinitionID) -> &'ctx Body<'ctx> {
        let packages = self.gcx.store.mir_packages.borrow();
        let package = *packages
            .get(&def_id.package())
            .expect("mir package for definition");
        package
            .functions
            .get(&def_id)
            .copied()
            .expect("mir body for definition")
    }

    /// Substitute parent's concrete types into child's generic arguments.
    fn substitute_args(
        &self,
        parent: Instance<'ctx>,
        call_args: GenericArguments<'ctx>,
    ) -> GenericArguments<'ctx> {
        let parent_args = parent.args();

        if parent_args.is_empty() {
            // Parent has no substitutions, call args are already concrete
            call_args
        } else {
            // Perform substitution
            self.substitute_with_args(call_args, parent_args)
        }
    }

    /// Substitute generic arguments using parent's substitution.
    fn substitute_with_args(
        &self,
        args: GenericArguments<'ctx>,
        subst: GenericArguments<'ctx>,
    ) -> GenericArguments<'ctx> {
        if subst.is_empty() {
            return args;
        }

        let substituted: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => {
                    let new_ty = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                        self.gcx, *ty, subst,
                    );
                    GenericArgument::Type(new_ty)
                }
                GenericArgument::Const(c) => GenericArgument::Const(*c),
            })
            .collect();

        self.gcx.store.interners.intern_generic_args(substituted)
    }

    fn compute_instance(
        &self,
        def_id: DefinitionID,
        args: GenericArguments<'ctx>,
    ) -> Instance<'ctx> {
        resolve_instance(self.gcx, def_id, args)
    }
}
