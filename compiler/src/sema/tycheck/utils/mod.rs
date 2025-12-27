pub mod autoderef;
pub mod generics;
pub mod instantiate;

pub enum AutoReference {
    None,
    Mutable,
    Immutable,
}
