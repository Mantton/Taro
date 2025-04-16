use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{DefinitionID, DefinitionKind};
use taroc_span::{Span, Symbol};
use taroc_ty::{
    AssociatedTypeDefinition, ConformanceRecord, InterfaceMethodRequirement, InterfaceReference, Ty,
};

use crate::utils;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    CheckRecursiveTypes::run(context)?;
    CheckInterfaceImplementation::run(context)?;
    context.diagnostics.report()
}

/// Check Recursive Types
/// Check Interface Implementation
/// Checks if type correctly implement an interface
struct CheckRecursiveTypes<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> CheckRecursiveTypes<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> CheckRecursiveTypes<'ctx> {
        CheckRecursiveTypes { context }
    }

    fn run<'a>(context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = CheckRecursiveTypes::new(context);

        context.diagnostics.report()
    }
}

/// Check Interface Implementation
/// Checks if type correctly implement an interface
struct CheckInterfaceImplementation<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> CheckInterfaceImplementation<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> CheckInterfaceImplementation<'ctx> {
        CheckInterfaceImplementation { context }
    }

    fn run<'a>(context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = CheckInterfaceImplementation::new(context);

        let types: Vec<DefinitionID> = actor.context.with_type_database(None, |database| {
            database.def_to_ty.keys().cloned().collect()
        });

        for ty in types {
            actor.check_type(ty)
        }

        return context.diagnostics.report();
    }
}

impl<'ctx> CheckInterfaceImplementation<'ctx> {
    fn check_type(&mut self, id: DefinitionID) {
        if self.context.def_kind(id) == DefinitionKind::Interface {
            return;
        }

        let conformances = self.context.with_type_database(None, |db| {
            db.conformances.get(&id).cloned().unwrap_or_default()
        });

        for interface in conformances.into_iter() {
            self.check_conformance(id, interface);
        }
    }

    fn check_conformance(&mut self, id: DefinitionID, interface: InterfaceReference<'ctx>) {
        let definition = self.context.interface_definition(interface.id);
        let definition = definition.borrow();
        // println!("Working on {}", definition.name);

        // Build type witness map first.
        let type_witnesses = self.build_type_witnesses(id, &definition.requirements.types);

        // Now build a conformance record; note that witness_methods will be set later.
        let mut conformance = ConformanceRecord {
            ty: id,
            interface: interface.id,
            type_witnesses,
            method_witnesses: Default::default(),
        };

        for requirement in &definition.requirements.methods {
            self.check_method_requirement(id, interface, requirement, &mut conformance);
        }
    }

    fn check_method_requirement(
        &mut self,
        id: DefinitionID,
        interface: InterfaceReference<'ctx>,
        requirement: &InterfaceMethodRequirement<'ctx>,
        conformance: &mut ConformanceRecord<'ctx>,
    ) -> bool {
        // --- Candidate Lookup ---
        let functions_data = self.context.with_type_database(None, |db| {
            db.def_to_functions
                .entry(id)
                .or_insert(Default::default())
                .clone()
        });

        let functions_data = functions_data.borrow();
        let candidates = functions_data.methods.get(&requirement.name);
        let Some(candidates) = candidates else {
            if requirement.is_required {
                let message = format!(
                    "missing interface method requirement '{}'",
                    requirement.name
                );
                self.context.diagnostics.error(message, Span::module());
                return false;
            }
            // TODO: Report
            return false;
        };

        let initial_map =
            utils::create_substitution_map(self.context, interface.id, interface.arguments);

        let signature =
            utils::convert_labeled_signature_to_signature(&requirement.signature, self.context);

        let expected = utils::substitute(signature, &initial_map, Some(conformance), self.context);

        let mut found_candidate = false;
        for candidate in candidates {
            let recieved = utils::convert_labeled_signature_to_signature(candidate, self.context);
            // println!("--- Checking ---  ");
            // println!("{:?}", expected);
            // println!("{:?}", recieved);
            // println!("\n\n");

            // Check Function Signatures
            if expected != recieved {
                continue;
            }
            // Check Parameter Labels
            if !utils::compare_signature_labels(&requirement.signature, candidate) {
                continue;
            }
            // Register Method Witness
            found_candidate = true;

            // TODO: Add Method Witness
            break;
        }

        if !found_candidate {
            println!("no valid candidate found");
            return false;
        }

        return true;
    }
}

impl<'ctx> CheckInterfaceImplementation<'ctx> {
    /// Check associated type requirements and build type witnesses.
    fn check_type_requirement(
        &mut self,
        id: DefinitionID,
        requirement: &AssociatedTypeDefinition<'ctx>,
    ) -> Option<(Symbol, Ty<'ctx>)> {
        // For example, search the concrete type (id)'s associated type declarations.
        let candidate = self.context.associated_type(id, requirement.name);
        if let Some(candidate_type) = candidate {
            // Report that "Foo::Bar" is witnessed by candidate_type.
            // println!(
            //     "Type witness Found: {} -> {:?}",
            //     requirement.name, candidate_type
            // );
            Some((requirement.name.clone(), candidate_type))
        } else {
            let message = format!(
                "Missing type witness for associated type requirement '{}'",
                requirement.name
            );
            self.context.diagnostics.error(message, Span::module());
            None
        }
    }

    /// Build a map of type witnesses for a given interface conformance.
    fn build_type_witnesses(
        &mut self,
        id: DefinitionID,
        type_requirements: &[AssociatedTypeDefinition<'ctx>],
    ) -> FxHashMap<Symbol, Ty<'ctx>> {
        let mut type_witnesses: FxHashMap<Symbol, Ty<'ctx>> = Default::default();
        for req in type_requirements {
            if let Some((name, witness)) = self.check_type_requirement(id, req) {
                type_witnesses.insert(name, witness);
            }
        }
        type_witnesses
    }
}
