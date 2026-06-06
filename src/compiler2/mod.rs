mod code;
mod driver;
mod identity;
mod namespace;
mod world;

pub use code::{CodeId, CodeMap, CodeRecord};
pub use driver::{CodeSubmission, Compiler2, Submission};
pub use identity::{
    Function, FunctionId, FunctionMap, FunctionRef, FunctionState, Module, ModuleId, ModuleMap, ModuleState, Root,
    RootId, RootMap, RootState,
};
pub use namespace::{BindingId, NamespaceHead, NamespaceStore, NamespaceSymbol};
pub use world::World;

#[cfg(test)]
mod compiler2_test;
#[cfg(test)]
mod identity_test;
#[cfg(test)]
mod namespace_test;
