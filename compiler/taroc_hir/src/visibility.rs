use taroc_span::{FileID, Span};

use crate::DefinitionID;

#[derive(Debug, Clone, Copy)]
pub struct Visibility {
    pub span: Span,
    pub level: VisibilityLevel,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisibilityLevel {
    Public,
    Inherent,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TVisibility {
    Public,
    ModuleRestricted(DefinitionID),
    FileRestricted(FileID),
}
