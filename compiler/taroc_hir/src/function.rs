use taroc_ast_ir::Mutability;
use taroc_span::{Identifier, Span, Symbol};

use super::{
    AttributeList, Label, NodeID, block::Block, expression::Expression, generics::Generics,
    ty::Type,
};

#[derive(Debug, Clone)]
pub struct Function {
    pub generics: Generics,
    pub signature: FunctionSignature,
    pub block: Option<Block>,
}

impl Function {
    pub fn has_self(&self) -> bool {
        self.signature
            .prototype
            .inputs
            .get(0)
            .is_some_and(|p| p.name.symbol == Symbol::with("self"))
    }
}

/// AST Representation of a function parameter
///
/// ```text
/// name: String
/// name: String = "Default Value"
/// @attribute name: String
///
/// ```
#[derive(Debug, Clone)]
pub struct FunctionParameter {
    pub attributes: AttributeList,
    pub id: NodeID,
    pub label: Option<Label>,
    pub name: Identifier,
    pub annotated_type: Box<Type>,
    pub default_value: Option<Box<Expression>>,
    pub is_variadic: bool,
    pub span: Span,
}

/// AST representation of the function prototype, with its inputs and outputs
///
/// `(name: string) -> int`
/// `(name: string) -> void` // defaults to void if not provided
#[derive(Debug, Clone)]
pub struct FunctionPrototype {
    pub inputs: Vec<FunctionParameter>,
    pub output: Option<Box<Type>>,
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub span: Span,
    pub prototype: FunctionPrototype,
    pub is_async: bool,
}

#[derive(Debug, Clone)]
pub enum FunctionReceiverKind {
    Copy(Identifier),
    Ref(Mutability, Option<Identifier>),
    Ptr(Mutability, Option<Identifier>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SelfKind {
    Copy,
    Reference,
    Pointer,
}
