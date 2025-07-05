use crate::{
    GlobalContext, freshen,
    normalize::assoc::normalize_ty,
    ty::{AssociatedTypeDefinition, ConformanceRecord, InterfaceMethodRequirement, SimpleType, Ty},
    utils::{instantiate_ty_with_args, labeled_signature_to_ty},
};
use rustc_hash::FxHashMap;
use taroc_error::CompileResult;
use taroc_hir::DefinitionID;
use taroc_span::{SpannedMessage, Symbol};

pub fn run(context: GlobalContext) -> CompileResult<()> {
    Actor::run(context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(context: GlobalContext<'ctx>) -> CompileResult<()> {
        let actor = Actor::new(context);
        actor.package();
        context.diagnostics.report()
    }
}

impl<'ctx> Actor<'ctx> {
    fn package(&self) {
        // Get Conformance Records in Package

        let conformances = self
            .context
            .with_session_type_database(|db| db.conformances.clone());

        for (key, records) in conformances {
            self.definition(key, records);
        }
    }

    fn definition(&self, key: SimpleType, records: Vec<ConformanceRecord<'ctx>>) {
        for record in &records {
            self.check(key, record);
        }
    }

    fn check(&self, key: SimpleType, record: &ConformanceRecord<'ctx>) {
        let interface_id = record.interface.id;
        let requirements = self
            .context
            .with_type_database(interface_id.package(), |db| {
                *db.interface_requirements
                    .get(&interface_id)
                    .expect("interface requirments")
            });

        // let ty = ty_from_simple(self.context, key);
        // println!(
        //     "Check {} conforms to {}",
        //     ty.format(self.context),
        //     record.interface.format(self.context)
        // );

        // Build Type Witness
        let Some(_) = self.check_type_requirements(key, &requirements.types, record) else {
            return;
        };

        self.check_method_requirements(key, &requirements.methods, record);
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_type_requirements(
        &self,
        key: SimpleType,
        types: &[AssociatedTypeDefinition<'ctx>],
        record: &ConformanceRecord<'ctx>,
    ) -> Option<FxHashMap<Symbol, (DefinitionID, Ty<'ctx>)>> {
        let mut map = FxHashMap::default();
        let mut errors = vec![];
        for def in types {
            let result = self.check_type_requirement(key, def, record);

            match result {
                Ok(data) => {
                    map.insert(def.name, data);
                }
                Err(err) => {
                    errors.push(err);
                }
            }
        }

        if !errors.is_empty() {
            let message = format!(
                "type '{}' does not conform to interface '{}'",
                key.format(self.context),
                self.context.ident_for(record.interface.id).symbol
            );
            self.context.diagnostics.error(message, record.location);

            for err in errors {
                self.context.diagnostics.error(err.message, err.span);
            }
            return None;
        }

        return Some(map);
    }

    fn check_type_requirement(
        &self,
        key: SimpleType,
        def: &AssociatedTypeDefinition<'ctx>,
        record: &ConformanceRecord<'ctx>,
    ) -> Result<(DefinitionID, Ty<'ctx>), SpannedMessage> {
        let packages = self.context.packages_at_file(record.location.file);
        let candidate = packages.into_iter().find_map(|package| {
            // look up a candidate in this package
            let found = self.context.with_type_database(package, |db| {
                db.alias_table
                    .by_type
                    .get(&key)
                    .and_then(|table| table.aliases.get(&def.name))
                    .cloned()
            });

            found
        });

        let candidate = if let Some((cand, _)) = candidate {
            (cand, self.context.type_of(cand))
        } else if let Some(ty) = def.default_type {
            (def.id, ty)
        } else {
            let message = format!(
                "interface '{}' requires an associated type '{}' on '{}'",
                self.context.ident_for(record.interface.id).symbol,
                def.name,
                record.target.format(self.context)
            );

            return Err(SpannedMessage::new(message, record.location));
        };

        return Ok(candidate);
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_method_requirements(
        &self,
        key: SimpleType,
        requirements: &[InterfaceMethodRequirement<'ctx>],
        record: &ConformanceRecord<'ctx>,
    ) -> Option<FxHashMap<DefinitionID, DefinitionID>> {
        let mut map = FxHashMap::default();
        let mut errors = vec![];
        for req in requirements {
            let result = self.check_method_requirement(key, req, record);

            match result {
                Ok(data) => {
                    map.insert(req.id, data);
                }
                Err(err) => {
                    errors.push(err);
                }
            }
        }

        if !errors.is_empty() {
            let message = format!(
                "type '{}' does not conform to interface '{}'",
                key.format(self.context),
                self.context.ident_for(record.interface.id).symbol
            );
            self.context.diagnostics.error(message, record.location);

            for err in errors {
                self.context.diagnostics.error(err.message, err.span);
            }

            return None;
        }

        return Some(map);
    }

    fn check_method_requirement(
        &self,
        key: SimpleType,
        requirement: &InterfaceMethodRequirement<'ctx>,
        record: &ConformanceRecord<'ctx>,
    ) -> Result<DefinitionID, SpannedMessage> {
        let packages = self.context.packages_at_file(record.location.file);

        // Find Candidate in Visible Package
        let candidates: Vec<_> = packages
            .into_iter()
            .map(|package| {
                // look up a candidates in this package
                let candidates = self.context.with_type_database(package, |db| {
                    db.function_table
                        .methods
                        .get(&key)
                        .map(|table| table.functions.get(&requirement.name))
                        .flatten()
                        .map(|members| members.members.clone())
                });
                candidates.unwrap_or_default()
            })
            .flatten()
            .collect();

        let candidate = candidates.into_iter().find_map(|candiadte| {
            if self.check_signatures(requirement.id, candiadte, record) {
                return Some(candiadte);
            }

            None
        });

        if let Some(candidate) = candidate {
            return Ok(candidate);
        }

        if !requirement.is_required {
            return Ok(requirement.id); // not required as def provides a default implementation
        }

        // return error
        let interface_name = self.context.ident_for(record.interface.id).symbol;
        let signature =
            labeled_signature_to_ty(self.context.fn_signature(requirement.id), self.context);
        let message = format!(
            "interface '{}' requires function '{}' with signature '{}'",
            interface_name,
            requirement.name,
            signature.format(self.context)
        );

        return Err(SpannedMessage::new(message, record.location));
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_signatures(
        &self,
        interface_fn_id: DefinitionID,
        method_impl_fn_id: DefinitionID,
        record: &ConformanceRecord<'ctx>,
    ) -> bool {
        let gcx = self.context;
        let interface_fn_sig = gcx.fn_signature(interface_fn_id);
        let method_impl_fn_sig = gcx.fn_signature(method_impl_fn_id);

        // Quick Arity + Label + Modifier Check
        if !interface_fn_sig.same_shape(method_impl_fn_sig) {
            return false;
        }

        // Generics
        let interface_fn_generics = gcx.generics_of(interface_fn_id);
        let method_impl_fn_generics = gcx.generics_of(method_impl_fn_id);
        if interface_fn_generics.parameters.len() != method_impl_fn_generics.parameters.len() {
            return false;
        }

        // Check Signature
        let interface_fn_ty = {
            let ty = labeled_signature_to_ty(interface_fn_sig, gcx);
            let ty = instantiate_ty_with_args(gcx, ty, record.interface.arguments);
            let ty = normalize_ty(ty, gcx);
            let ty = freshen::TypeFreshener::new(gcx).freshen(ty);
            ty
        };

        let method_impl_fn_ty = {
            let ty = labeled_signature_to_ty(method_impl_fn_sig, gcx);
            let ty = normalize_ty(ty, gcx);
            let ty = freshen::TypeFreshener::new(gcx).freshen(ty);
            ty
        };

        // println!(
        //     "Compare:\nInterface Type: {}\nMethod Type: {}",
        //     interface_fn_ty.format(gcx),
        //     method_impl_fn_ty.format(gcx)
        // );

        // Quick Exit
        if interface_fn_ty == method_impl_fn_ty {
            return true;
        }

        // now try unfication
        // TODO!

        return false;
    }
}
