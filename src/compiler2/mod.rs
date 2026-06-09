mod agenda;
mod artifact;
mod body;
mod cli;
mod code;
mod compiler;
mod contract;
mod deps;
mod dispatch;
mod drive;
mod facts;
mod frontdoor;
mod identity;
mod jobs;
mod keying;
mod namespace;
mod native_codegen;
mod protocol;
mod quoted_surface;
mod resolve;
mod runtime;
mod scheduler;
mod scope;
mod semantic;
mod source;
mod type_expr;
mod typedef;
mod types;
mod world;

pub use agenda::Agenda;
pub(crate) use artifact::NativeEntryAbi;
pub use artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiReadyProgram, AbiReadyProgramMap, AbiValueRepr, BackendBody,
    BackendCallArg, BackendCallableEntry, BackendClause, BackendEntry, BackendEntryOrigin, BackendExecutable,
    BackendProgram, BackendProgramMap, BackendReceive, BackendStep, BackendTail, CallableEntry, EmissionReadyCallEdge,
    EmissionReadyCallableEntry, EmissionReadyExecutable, EmissionReadyProgram, EmissionReadyProgramMap,
    ExecutableDispatch, MaterializedCallEdge, MaterializedExecutable, MaterializedProgram, MaterializedProgramMap,
    ReturnAbi,
};
pub(crate) use artifact::{NativeBody, NativeProgram};
pub use body::{
    BodySlot, BodyState, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin,
    DirectCallee, DispatchBindings, Literal, LoweredBitField, LoweredBitFieldSpec, LoweredBitSize, LoweredBody,
    LoweredBodyMap, LoweredClause, LoweredEntry, LoweredExtern, LoweredReceive, LoweredStep, LoweredTail, ReceiveAfter,
    ReceiveClause, ValueId,
};
pub use cli::run as run_cli;
pub use code::{Code, CodeId, CodeMap, CodeState, LegacyCodeSource, QuotedCodeSource};
pub use compiler::{CodeSubmission, Compiler2, RootSubmission};
pub use contract::{FunctionContract, FunctionContractMap};
pub use deps::{DependencyIndex, UnresolvedWait};
pub use drive::{FactKey, Job, WorkGraph};
pub use facts::{FactChange, FactReplace, FactSlot, FactTable, FactValue};
pub use frontdoor::{FrontDoorError, parse_quoted_program};
pub use identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, Function, FunctionDef, FunctionId, FunctionMap, FunctionRef,
    FunctionState, LegacyModuleBody, LegacyModuleSource, LegacyProtocolSource, Module, ModuleExport, ModuleId,
    ModuleMap, ModuleSource, ModuleSourceKind, ModuleState, ModuleSurface, NotedTypeDecl, Root, RootEntry, RootId,
    RootMap, TypeName,
};
pub use namespace::{BindingId, Namespace, NamespaceStore, NamespaceSymbol};
pub use scheduler::{AppliedStep, DriveOutcome, FatalError, Scheduler};
pub use scope::ScopeSnapshot;
pub use semantic::{
    ActivationAnalysis, ActivationMap, ActivationSlot, CallSiteKey, CallSiteMap, CallSiteSummary, SelectedCallee,
    SemanticClosure, SemanticClosureMap,
};
pub use source::{
    QuotedAstNode, QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceBuilder, QuotedSourceCarrier,
    QuotedSourceCursor, QuotedSourceError, QuotedSourceFingerprint, QuotedSourceFingerprintPolicy, QuotedSourceHeap,
    QuotedSourceKey, QuotedSourceMetadata, QuotedSourceRoot, QuotedSourceSpan,
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
mod contract_test;
#[cfg(test)]
mod drive_test;
#[cfg(test)]
mod facts_test;
#[cfg(test)]
mod frontdoor_test;
#[cfg(test)]
mod identity_test;
#[cfg(test)]
mod namespace_test;
#[cfg(test)]
mod quoted_surface_test;
#[cfg(test)]
mod scheduler_test;
#[cfg(test)]
mod scope_test;
#[cfg(test)]
mod source_test;
#[cfg(test)]
mod telemetry_dump_test;
#[cfg(test)]
mod type_expr_test;
#[cfg(test)]
mod world_test;
