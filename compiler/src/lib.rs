#![feature(associated_type_defaults)]
// GC execution tests use C ABI symbols from this matched runtime.
#[cfg(test)]
extern crate taro_runtime as _;

mod ast;
mod ast_lowering;
#[cfg(test)]
#[path = "../build_identity.rs"]
mod build_identity;
mod cfg;
mod cfg_eval;
pub mod codegen;
pub mod compile;
pub mod constants;
pub mod diagnostics;
pub mod error;
mod hir;
mod interner;
pub mod metadata;
pub mod mir;
pub mod package;
mod parse;
pub mod runtime_abi;
mod sema;
pub mod span;
pub mod specialize;
#[cfg(test)]
mod test_support;
mod thir;
mod utils;

pub use span::PackageIndex;

/// Verify that `original` and `formatted` lex cleanly and produce the exact
/// same semantic token stream (including ASI-inserted semicolons, literals,
/// and nested string interpolation tokens).
pub fn verify_format_equivalence(original: &str, formatted: &str) -> Result<(), String> {
    let file_id = span::FileID::from_raw(0);
    let orig = parse::lexer::Lexer::new(original, file_id)
        .tokenize()
        .map_err(|err| format!("syntax/lex error: {}", err.value))?;
    let next = parse::lexer::Lexer::new(formatted, file_id)
        .tokenize()
        .map_err(|err| format!("formatter internal verification failed to re-lex output: {}", err.value))?;
    let orig_tokens: Vec<_> = orig.tokens.into_iter().map(|s| s.value).collect();
    let next_tokens: Vec<_> = next.tokens.into_iter().map(|s| s.value).collect();
    if orig_tokens != next_tokens {
        return Err(
            "formatter safety check detected a token/ASI change; leaving file unmodified"
                .to_string(),
        );
    }
    Ok(())
}
