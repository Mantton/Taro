//! Configuration predicate evaluation for conditional compilation.
//!
//! This module provides utilities for evaluating `//+cfg` file-level directives
//! and `#cfg()` expression predicates. It's designed to work at the lexer stage
//! (before AST parsing) for file-level cfg, and can also be used by AST lowering.

/// Target information extracted from a triple string.
#[derive(Debug, Clone)]
pub struct TargetInfo {
    pub arch: String,
    pub os: String,
    pub family: String,
    pub profile: String,
}

impl TargetInfo {
    /// Parse target information from a triple string.
    /// Format: arch-vendor-os or arch-vendor-os-env
    pub fn from_triple(triple: &str) -> TargetInfo {
        let parts: Vec<&str> = triple.split('-').collect();
        let arch = parts.first().cloned().unwrap_or("").to_string();
        let os = if parts.len() >= 3 {
            parts[2].to_string()
        } else {
            String::new()
        };

        // Determine family from OS
        let family = match os.as_str() {
            s if s.contains("darwin") || s == "macos" => "unix",
            "linux" | "freebsd" | "openbsd" | "netbsd" | "dragonfly" => "unix",
            s if s.contains("windows") || s == "win32" => "windows",
            _ => "unknown",
        }
        .to_string();

        TargetInfo {
            arch,
            os,
            family,
            profile: "debug".to_string(),
        }
    }

    /// Check if this matches an os predicate.
    pub fn matches_os(&self, value: &str) -> bool {
        match value {
            "macos" | "darwin" => self.os.contains("darwin") || self.os == "macos",
            "linux" => self.os == "linux",
            "windows" => self.os.contains("windows") || self.os == "win32",
            _ => self.os == value,
        }
    }

    /// Check if this matches an arch predicate.
    pub fn matches_arch(&self, value: &str) -> bool {
        match value {
            "x86_64" | "amd64" => self.arch == "x86_64",
            "aarch64" | "arm64" => self.arch == "aarch64" || self.arch == "arm64",
            "arm" => self.arch.starts_with("arm"),
            _ => self.arch == value,
        }
    }

    /// Check if this matches a family predicate.
    pub fn matches_family(&self, value: &str) -> bool {
        self.family == value
    }

    /// Check if this matches a build profile predicate.
    pub fn matches_profile(&self, value: &str) -> bool {
        self.profile == value
    }
}

/// A parsed cfg expression for file-level directives.
#[derive(Debug, Clone)]
pub enum FileCfgExpr {
    /// `os("macos")` or `arch("x86_64")` or `family("unix")`
    Predicate { name: String, value: String },
    /// `!expr`
    Not(Box<FileCfgExpr>),
    /// `expr && expr`
    All(Vec<FileCfgExpr>),
    /// `expr || expr`
    Any(Vec<FileCfgExpr>),
}

impl FileCfgExpr {
    /// Evaluate this expression against target info.
    pub fn evaluate(&self, target: &TargetInfo) -> bool {
        match self {
            FileCfgExpr::Predicate { name, value } => match name.as_str() {
                "os" => target.matches_os(value),
                "arch" => target.matches_arch(value),
                "family" => target.matches_family(value),
                "profile" => target.matches_profile(value),
                _ => false,
            },
            FileCfgExpr::Not(inner) => !inner.evaluate(target),
            FileCfgExpr::All(items) => items.iter().all(|e| e.evaluate(target)),
            FileCfgExpr::Any(items) => items.iter().any(|e| e.evaluate(target)),
        }
    }
}

/// Extract a `//+cfg ...` directive from the first line of source code.
/// Returns the cfg expression string if found.
pub fn extract_file_cfg(source: &str) -> Option<&str> {
    let first_line = source.lines().next()?;
    let trimmed = first_line.trim();
    if trimmed.starts_with("//+cfg ") {
        Some(trimmed[7..].trim())
    } else {
        None
    }
}

/// Parse a file-level cfg expression string into a FileCfgExpr.
/// Supports: `os("linux")`, `arch("x86_64")`, `family("unix")`, `&&`, `||`, `!`
pub fn parse_file_cfg(expr: &str) -> Option<FileCfgExpr> {
    let expr = expr.trim();
    if expr.is_empty() {
        return None;
    }

    Parser::new(expr).parse_expr()
}

/// Simple recursive descent parser for cfg expressions.
struct Parser<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Parser { input, pos: 0 }
    }

    fn remaining(&self) -> &'a str {
        &self.input[self.pos..]
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.input.len() {
            let c = self.input[self.pos..].chars().next().unwrap();
            if c.is_whitespace() {
                self.pos += c.len_utf8();
            } else {
                break;
            }
        }
    }

    fn parse_expr(&mut self) -> Option<FileCfgExpr> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Option<FileCfgExpr> {
        let mut left = self.parse_and()?;
        self.skip_whitespace();

        while self.remaining().starts_with("||") {
            self.pos += 2;
            self.skip_whitespace();
            let right = self.parse_and()?;
            left = match left {
                FileCfgExpr::Any(mut items) => {
                    items.push(right);
                    FileCfgExpr::Any(items)
                }
                other => FileCfgExpr::Any(vec![other, right]),
            };
            self.skip_whitespace();
        }

        Some(left)
    }

    fn parse_and(&mut self) -> Option<FileCfgExpr> {
        let mut left = self.parse_unary()?;
        self.skip_whitespace();

        while self.remaining().starts_with("&&") {
            self.pos += 2;
            self.skip_whitespace();
            let right = self.parse_unary()?;
            left = match left {
                FileCfgExpr::All(mut items) => {
                    items.push(right);
                    FileCfgExpr::All(items)
                }
                other => FileCfgExpr::All(vec![other, right]),
            };
            self.skip_whitespace();
        }

        Some(left)
    }

    fn parse_unary(&mut self) -> Option<FileCfgExpr> {
        self.skip_whitespace();

        if self.remaining().starts_with('!') {
            self.pos += 1;
            self.skip_whitespace();
            let inner = self.parse_unary()?;
            return Some(FileCfgExpr::Not(Box::new(inner)));
        }

        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Option<FileCfgExpr> {
        self.skip_whitespace();

        // Parenthesized expression
        if self.remaining().starts_with('(') {
            self.pos += 1;
            let expr = self.parse_expr()?;
            self.skip_whitespace();
            if self.remaining().starts_with(')') {
                self.pos += 1;
                return Some(expr);
            }
            return None;
        }

        // Predicate: name("value")
        self.parse_predicate()
    }

    fn parse_predicate(&mut self) -> Option<FileCfgExpr> {
        self.skip_whitespace();

        // Parse identifier (name)
        let start = self.pos;
        while self.pos < self.input.len() {
            let c = self.input[self.pos..].chars().next().unwrap();
            if c.is_alphanumeric() || c == '_' {
                self.pos += c.len_utf8();
            } else {
                break;
            }
        }

        if self.pos == start {
            return None;
        }

        let name = self.input[start..self.pos].to_string();

        self.skip_whitespace();

        // Expect '('
        if !self.remaining().starts_with('(') {
            return None;
        }
        self.pos += 1;

        self.skip_whitespace();

        // Expect '"'
        if !self.remaining().starts_with('"') {
            return None;
        }
        self.pos += 1;

        // Parse string value
        let value_start = self.pos;
        while self.pos < self.input.len() {
            let c = self.input[self.pos..].chars().next().unwrap();
            if c == '"' {
                break;
            }
            self.pos += c.len_utf8();
        }
        let value = self.input[value_start..self.pos].to_string();

        // Expect closing '"'
        if !self.remaining().starts_with('"') {
            return None;
        }
        self.pos += 1;

        self.skip_whitespace();

        // Expect ')'
        if !self.remaining().starts_with(')') {
            return None;
        }
        self.pos += 1;

        Some(FileCfgExpr::Predicate { name, value })
    }
}

/// Evaluate a file-level cfg directive against a target triple.
/// Returns true if the file should be included, false if it should be skipped.
pub fn evaluate_file_cfg(source: &str, triple: &str) -> bool {
    let Some(cfg_str) = extract_file_cfg(source) else {
        return true; // No cfg directive, include file
    };

    let Some(expr) = parse_file_cfg(cfg_str) else {
        return true; // Invalid cfg expression, include file (will error later)
    };

    let target = TargetInfo::from_triple(triple);
    expr.evaluate(&target)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_file_cfg() {
        assert_eq!(
            extract_file_cfg("//+cfg os(\"linux\")"),
            Some("os(\"linux\")")
        );
        assert_eq!(
            extract_file_cfg("//+cfg  family(\"unix\")"),
            Some("family(\"unix\")")
        );
        assert_eq!(extract_file_cfg("// normal comment"), None);
        assert_eq!(extract_file_cfg("func main() {}"), None);
    }

    #[test]
    fn test_parse_simple_predicate() {
        let expr = parse_file_cfg("os(\"linux\")").unwrap();
        if let FileCfgExpr::Predicate { name, value } = expr {
            assert_eq!(name, "os");
            assert_eq!(value, "linux");
        } else {
            panic!("expected predicate");
        }
    }

    #[test]
    fn test_parse_and() {
        let expr = parse_file_cfg("os(\"linux\") && arch(\"x86_64\")").unwrap();
        if let FileCfgExpr::All(items) = expr {
            assert_eq!(items.len(), 2);
        } else {
            panic!("expected All");
        }
    }

    #[test]
    fn test_parse_or() {
        let expr = parse_file_cfg("os(\"linux\") || os(\"macos\")").unwrap();
        if let FileCfgExpr::Any(items) = expr {
            assert_eq!(items.len(), 2);
        } else {
            panic!("expected Any");
        }
    }

    #[test]
    fn test_parse_not() {
        let expr = parse_file_cfg("!os(\"windows\")").unwrap();
        if let FileCfgExpr::Not(_) = expr {
            // ok
        } else {
            panic!("expected Not");
        }
    }

    #[test]
    fn test_target_info_unix() {
        let target = TargetInfo::from_triple("aarch64-apple-darwin");
        assert!(target.matches_os("macos"));
        assert!(target.matches_os("darwin"));
        assert!(target.matches_arch("aarch64"));
        assert!(target.matches_arch("arm64"));
        assert!(target.matches_family("unix"));
    }

    #[test]
    fn test_target_info_linux() {
        let target = TargetInfo::from_triple("x86_64-unknown-linux-gnu");
        assert!(target.matches_os("linux"));
        assert!(target.matches_arch("x86_64"));
        assert!(target.matches_family("unix"));
    }

    #[test]
    fn test_target_info_windows() {
        let target = TargetInfo::from_triple("x86_64-pc-windows-msvc");
        assert!(target.matches_os("windows"));
        assert!(target.matches_arch("x86_64"));
        assert!(target.matches_family("windows"));
    }

    #[test]
    fn test_evaluate_family_unix() {
        let source = "//+cfg family(\"unix\")\nextern \"C\" {}";
        assert!(evaluate_file_cfg(source, "aarch64-apple-darwin"));
        assert!(evaluate_file_cfg(source, "x86_64-unknown-linux-gnu"));
        assert!(!evaluate_file_cfg(source, "x86_64-pc-windows-msvc"));
    }

    #[test]
    fn test_evaluate_family_windows() {
        let source = "//+cfg family(\"windows\")\nextern \"C\" {}";
        assert!(!evaluate_file_cfg(source, "aarch64-apple-darwin"));
        assert!(!evaluate_file_cfg(source, "x86_64-unknown-linux-gnu"));
        assert!(evaluate_file_cfg(source, "x86_64-pc-windows-msvc"));
    }
}
