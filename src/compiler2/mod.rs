mod agenda;
mod code;
mod deps;
mod driver;
mod facts;
mod identity;
mod namespace;
mod scheduler;
mod world;

pub use agenda::Agenda;
pub use code::{CodeId, CodeMap, CodeRecord};
pub use deps::{DependencyIndex, ExactPattern, FactPattern};
pub use driver::{CodeSubmission, Compiler2, Submission};
pub use facts::{FactAggregator, FactChange, FactReplace, FactSlot, FactTable, Fingerprint};
pub use identity::{
    Function, FunctionId, FunctionMap, FunctionRef, FunctionState, Module, ModuleId, ModuleMap, ModuleState, Root,
    RootId, RootMap, RootState,
};
pub use namespace::{BindingId, NamespaceHead, NamespaceStore, NamespaceSymbol};
pub use scheduler::{DriveDone, DriveResult, JobOutcome, Scheduler, StepResult};
pub use world::World;

#[cfg(test)]
mod compiler2_test;
#[cfg(test)]
mod identity_test;
#[cfg(test)]
mod namespace_test;
#[cfg(test)]
mod scheduler_test;
