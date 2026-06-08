mod agenda;
mod artifact;
mod body;
mod code;
mod compiler;
mod deps;
mod dispatch;
mod drive;
mod facts;
mod identity;
mod jobs;
mod keying;
mod namespace;
mod protocol;
mod runtime;
mod scheduler;
mod semantic;
mod types;
mod world;

pub use agenda::Agenda;
pub(crate) use artifact::NativeBody;
pub use artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiReadyProgram, AbiReadyProgramMap, AbiValueRepr, BackendBlock, BackendBody,
    BackendCallArg, BackendCallableEntry, BackendClause, BackendExecutable, BackendProgram, BackendProgramMap,
    BackendStep, CallableEntry, EmissionReadyCallEdge, EmissionReadyCallableEntry, EmissionReadyExecutable,
    EmissionReadyProgram, EmissionReadyProgramMap, ExecutableDispatch, MaterializedCallEdge, MaterializedExecutable,
    MaterializedProgram, MaterializedProgramMap, ReturnAbi,
};
#[cfg(test)]
pub(crate) use artifact::{NativeEntryAbi, NativeProgram};
pub use body::{
    BodySlot, BodyState, CallSiteId, DirectCallee, Literal, LoweredBlock, LoweredBody, LoweredBodyMap, LoweredClause,
    LoweredExtern, LoweredStep, ValueId,
};
pub use code::{Code, CodeId, CodeMap, CodeState};
pub use compiler::{CodeSubmission, Compiler2, RootSubmission};
pub use deps::{DependencyIndex, UnresolvedWait};
pub use drive::{FactKey, Job, WorkGraph};
pub use facts::{FactChange, FactReplace, FactSlot, FactTable, FactValue};
pub use identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, Function, FunctionDef, FunctionId, FunctionMap, FunctionRef,
    FunctionState, Module, ModuleExport, ModuleId, ModuleMap, ModuleSource, ModuleSourceKind, ModuleState,
    ModuleSurface, Root, RootEntry, RootId, RootMap,
};
pub use namespace::{BindingId, Namespace, NamespaceStore, NamespaceSymbol};
pub use scheduler::{AppliedStep, DriveOutcome, FatalError, Scheduler};
pub use semantic::{
    ActivationAnalysis, ActivationMap, ActivationSlot, CallSiteKey, CallSiteMap, CallSiteSummary, SelectedCallee,
    SemanticClosure, SemanticClosureMap,
};
pub use types::{
    CallableClause, CallableValueKind, ClosureLitInfo, ClosureTarget, MapKey, Nominals, OpaqueVisibilityError, Sigma,
    Ty, TypeVarId, Types,
};
pub use world::World;

#[cfg(test)]
mod artifact_test;
#[cfg(test)]
mod code_test;
#[cfg(test)]
mod compiler2_test;
#[cfg(test)]
mod drive_test;
#[cfg(test)]
mod facts_test;
#[cfg(test)]
mod identity_test;
#[cfg(test)]
mod namespace_test;
#[cfg(test)]
mod scheduler_test;
#[cfg(test)]
mod telemetry_dump_test;
#[cfg(test)]
mod world_test;
