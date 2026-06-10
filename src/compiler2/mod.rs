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
mod quoted_function;
mod quoted_surface;
mod resolve;
mod runtime;
mod scheduler;
mod scope;
mod semantic;
mod source;
mod source_publish;
mod source_sugar;
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
    BodyState, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin, DirectCallee,
    DispatchBindings, Literal, LoweredBitField, LoweredBitFieldSpec, LoweredBitSize, LoweredBody, LoweredBodyMap,
    LoweredClause, LoweredEntry, LoweredExtern, LoweredReceive, LoweredStep, LoweredTail, ReceiveAfter, ReceiveClause,
    ValueId,
};
pub use cli::run as run_cli;
pub use code::{CodeId, CodeMap, CodeState, QuotedCodeSource};
pub use compiler::{CodeSubmission, Compiler2, RootSubmission};
pub use contract::{FunctionContract, FunctionContractMap};
pub use deps::{DependencyIndex, UnresolvedWait};
pub use drive::{FactKey, Job, WorkGraph};
pub use facts::{FactChange, FactReplace, FactTable};
pub use frontdoor::{FrontDoorError, parse_quoted_program};
pub use identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, FunctionMap, FunctionRef, FunctionSource, FunctionState,
    ModuleExport, ModuleId, ModuleMap, ModuleSource, ModuleSourceKind, ModuleState, ModuleSurface, NotedTypeDecl,
    RootEntry, RootId, RootKind, RootMap, TypeName,
};
pub use namespace::{BindingId, Namespace, NamespaceStore, NamespaceSymbol};
pub use quoted_surface::SurfaceSourceContext;
pub use scheduler::{AppliedStep, DriveOutcome, FatalError, Scheduler};
pub use scope::ScopeSnapshot;
pub use semantic::{
    ActivationAnalysis, ActivationMap, ActivationSlot, CallSiteKey, CallSiteMap, CallSiteSummary, SelectedCallee,
    SemanticClosure, SemanticClosureMap,
};
pub use source::{
    Horizon, QuotedAstNode, QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceBuilder, QuotedSourceCursor,
    QuotedSourceError, QuotedSourceHeap, QuotedSourceKey, QuotedSourceMetadata, QuotedSourceRoot, QuotedSourceSpan,
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
mod port_codegen_test;
#[cfg(test)]
mod port_frontend_test;
#[cfg(test)]
mod port_interp_test;
#[cfg(test)]
mod port_lower_test;
#[cfg(test)]
mod port_macros_test;
#[cfg(test)]
mod port_misc_test;
#[cfg(test)]
mod port_planner_test;
#[cfg(test)]
mod port_resolve_test;
#[cfg(test)]
mod port_type_infer_test;
#[cfg(test)]
mod quoted_function_test;
#[cfg(test)]
mod quoted_surface_test;
#[cfg(test)]
mod scheduler_test;
#[cfg(test)]
mod scope_test;
#[cfg(test)]
mod source_publish_test;
#[cfg(test)]
mod source_test;
#[cfg(test)]
mod telemetry_dump_test;
#[cfg(test)]
mod type_expr_test;
#[cfg(test)]
mod world_test;
