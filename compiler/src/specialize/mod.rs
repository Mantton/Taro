pub mod collect;
mod instance;
mod resolve;

pub use instance::{Instance, InstanceKind, VirtualInstance};
pub use resolve::resolve_instance;
