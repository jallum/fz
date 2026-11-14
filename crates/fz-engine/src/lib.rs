//! The fact engine: a generic fixpoint over jobs and facts.
//!
//! The engine knows nothing of the compiler's World, types or telemetry. A
//! client supplies its fact keys, its jobs and the order its keys are compared
//! in (`SemanticOrd`); the engine schedules, wakes and settles.

mod agenda;
mod deps;
mod facts;
mod groups;
mod ordered_set;
mod ordered_worklist;
mod scheduler;
mod waits;

mod fast_hash;

pub use agenda::Agenda;
pub use deps::{DependencyIndex, UnresolvedWait};
pub use facts::{
    ClaimShape, FactChange, FactMovement, FactReadiness, FactReplace, FactState, FactTable, FactUse, Publisher,
    SemanticOrd,
};
pub use ordered_set::OrderedSet;
pub use ordered_worklist::OrderedWorklist;
pub use scheduler::{
    AppliedStep, ClientReason, CompletionEffects, DerivationEffects, DriveOutcome, ExternalDependencyStates,
    FatalError, NoExternalDependencyStates, Scheduler, Wake, WakeDisposition, WorkStart, WorkStartTally,
};
pub use waits::StandingWaits;
