//! Target inputs consumed by semantic analysis independently of code generation.

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(try_from = "TargetDescriptor")]
pub struct TargetFacts {
    triple: String,
    pointer_bits: u32,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TargetDescriptor {
    triple: String,
    pointer_bits: u32,
}

impl TryFrom<TargetDescriptor> for TargetFacts {
    type Error = String;

    fn try_from(descriptor: TargetDescriptor) -> Result<Self, Self::Error> {
        Self::new(descriptor.triple, descriptor.pointer_bits)
    }
}

impl TargetFacts {
    pub(crate) fn new(triple: String, pointer_bits: u32) -> Result<Self, String> {
        if triple.is_empty() || triple.bytes().any(|byte| byte.is_ascii_whitespace()) {
            return Err(format!("invalid target triple '{triple}'"));
        }
        if !matches!(pointer_bits, 16 | 32 | 64) {
            return Err(format!(
                "unsupported pointer width {pointer_bits} for '{triple}'"
            ));
        }
        Ok(Self {
            triple,
            pointer_bits,
        })
    }

    pub fn triple(&self) -> &str {
        &self.triple
    }

    pub fn pointer_bits(&self) -> u32 {
        self.pointer_bits
    }
}

#[cfg(test)]
mod tests {
    use super::TargetFacts;
    use crate::compile::config::HarnessMode;
    use crate::test_support::with_target_source_compiler;

    #[test]
    fn round_trips_authoritative_width_and_drives_semantic_checks() {
        for (triple, width) in [
            ("x86_64-unknown-linux-gnu", 64),
            ("i686-unknown-linux-gnu", 32),
        ] {
            let source = r#"
                @cfg(arch("x86_64"))
                func selected() -> isize { 2147483648 }
                @cfg(arch("i686"))
                func selected() -> isize { 2147483648 }
                func call() -> isize { selected() }
            "#;
            with_target_source_compiler(
                &[("main.tr", source)],
                false,
                HarnessMode::None,
                Some(triple.into()),
                |compiler| {
                    let facts = &compiler.context.store.target_facts;
                    assert_eq!(facts.pointer_bits(), width);
                    assert_eq!(facts, compiler.context.store.target_layout.facts());
                    let descriptor = toml::to_string(facts).unwrap();
                    assert_eq!(toml::from_str::<TargetFacts>(&descriptor).unwrap(), *facts);
                    let result = compiler.analyze();
                    let diagnostics = compiler.context.dcx().take_recorded_diagnostics();
                    if width == 64 {
                        assert!(result.is_ok(), "{diagnostics:?}");
                    } else {
                        assert!(result.is_err());
                        assert!(
                            diagnostics.iter().any(|diagnostic| {
                                diagnostic.message.contains("2147483648")
                                    && diagnostic.message.contains("out of range")
                            }),
                            "{diagnostics:?}"
                        );
                    }
                },
            );
        }
    }

    #[test]
    fn rejects_unsupported_pointer_width_in_descriptor() {
        let error = toml::from_str::<TargetFacts>("triple = 'test'\npointer_bits = 7").unwrap_err();
        assert!(error.to_string().contains("unsupported pointer width"));
    }
}
