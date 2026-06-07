mod agenda;
mod code;
mod deps;
mod driver;
mod facts;
mod identity;
mod namespace;
mod scheduler;
mod work;
mod world;

pub use agenda::Agenda;
pub use code::{Code, CodeId, CodeMap, CodeState};
pub use deps::{DependencyIndex, ExactPattern, FactPattern};
pub use driver::{CodeSubmission, Compiler2};
pub use facts::{FactChange, FactReplace, FactSlot, FactTable};
pub use identity::{
    Function, FunctionDef, FunctionId, FunctionMap, FunctionRef, FunctionState, Module, ModuleExport, ModuleId,
    ModuleMap, ModuleSource, ModuleState, ModuleSurface,
};
pub use namespace::{BindingId, Namespace, NamespaceStore, NamespaceSymbol};
pub use scheduler::{AppliedStep, DriveError, FatalError, Scheduler};
pub use work::{FactKey, Job, WorkGraph};
pub use world::World;

#[cfg(test)]
mod code_test;
#[cfg(test)]
mod compiler2_test;
#[cfg(test)]
mod identity_test;
#[cfg(test)]
mod namespace_test;
#[cfg(test)]
mod scheduler_test;
#[cfg(test)]
mod work_test;
#[cfg(test)]
mod world_test;
