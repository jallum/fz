mod agenda;
mod artifact;
mod body;
pub(crate) mod callsite_dispatch;
mod canon;
mod cli;
mod code;
mod compiler;
mod contract;
mod deps;
mod dispatch;
mod dispatch_reachability;
mod drive;
mod dump;
mod executable_facts;
mod facts;
mod fixture_metadata;
mod frontdoor;
mod identity;
mod jobs;
mod keying;
mod module_interface;
mod namespace;
mod native_codegen;
mod ordered_set;
mod product_drive;
mod protocol;
#[doc(hidden)]
pub mod pull;
mod quoted_expander;
mod quoted_function;
mod quoted_surface;
mod resolve;
mod runtime;
mod scheduler;
mod scope;
mod semantic;
mod source;
mod source_diagnostics;
mod source_publish;
mod source_sugar;
mod structdef;
mod token_payload;
pub mod transport;
mod type_expr;
mod typedef;
mod types;
mod world;

pub use agenda::Agenda;
pub use artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiValueRepr, BackendBody, BackendCallArg, BackendClause,
    BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry, BackendEntryCapture,
    BackendEntryOrigin, BackendExecutable, BackendProgram, BackendProgramMap, BackendReceive, BackendReturnLayout,
    BackendSemanticInputLayout, BackendStep, BackendTail, CallEdge, CallTarget, DirectCallEdge, DispatchCallArm,
    DispatchCallEdge, DispatchCallMiss, EmissionReadyCallEdge, EmissionReadyExecutable, ExecutableDispatch,
    MaterializedCallEdge, MaterializedExecutable,
};
pub(crate) use artifact::{NativeBody, NativeProgram};
pub(crate) use artifact::{NativeEntryAbi, required_dispatch_input_ordinals};
pub use body::{
    BodyState, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin, DispatchBindings,
    LoweredBitField, LoweredBitFieldSpec, LoweredBitSize, LoweredBody, LoweredBodyMap, LoweredClause, LoweredEntry,
    LoweredExtern, LoweredReceive, LoweredStep, LoweredTail, ReceiveAfter, ReceiveClause, ValueId,
};
pub(crate) use canon::function_label;
pub use cli::run as run_cli;
pub use code::{CodeId, CodeMap, CodeState, QuotedCodeSource};
pub use compiler::{CodeSubmission, Compiler2, RootSubmission};
pub use contract::{FunctionContract, FunctionContractMap};
pub use deps::{DependencyIndex, UnresolvedWait};
pub(crate) use drive::JobEffects;
pub use drive::{FactKey, Job, WorkGraph};
pub use facts::{FactChange, FactMovement, FactReadiness, FactReplace, FactState, FactTable, FactUse};
#[cfg(test)]
pub use fixture_metadata::fixture_frontmatter_prefix_bytes;
pub use fixture_metadata::{
    BudgetAssertion, EdgeAssertion, FixtureCompilerMetadata, FixtureExpect, FixtureKind, FixtureMatrixMetadata,
    FixtureMatrixPath, FixtureMetadata, FixtureMetadataError, FixtureRoot, MetricAssertion, PathTimeout,
    fixture_matrix_paths_from_filename, parse_fixture_metadata,
};
pub use frontdoor::{FrontDoorError, parse_quoted_program};
pub use identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, FunctionMap, FunctionRef, FunctionSource, FunctionState,
    ModuleId, ModuleMap, ModuleSource, ModuleSourceKind, ModuleState, NotedTypeDecl, RootEntry, RootId, RootKind,
    RootMap, TypeName,
};
pub(crate) use jobs::runtime_demand::DemandConeSettlement;
pub(crate) use keying::InputDemand;
pub use module_interface::{
    InterfaceCallableKind, InterfaceExpectation, InterfaceRequester, ModuleInterface, ModuleInterfaceCallable,
    ReadyOrPending,
};
pub use namespace::{BindingId, Namespace, NamespaceStore, NamespaceSymbol};
pub(crate) use pull::{ProductKey, PullSession};
pub use scheduler::{
    AppliedStep, DriveOutcome, FatalError, Scheduler, Wake, WakeDisposition, WorkStartReason, WorkStartTally,
};
pub use scope::ScopeSnapshot;
pub use semantic::{
    ActivationAnalysis, ActivationMap, ActivationSlot, CallSiteKey, CallSiteMap, CallSiteResolution, CallSiteSummary,
    CallTargetSummary, CallableDemand, CallableFlowFact, CallableSurface, ContributionMap, ContributionReplace,
    EntryReachability, ExecutableRuntimeDemand, RuntimeDemand, SelectedCallee, SemanticClosure, SemanticClosureMap,
    ShapeDemand,
};
pub use source::{
    Horizon, QuotedAstNode, QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceBuilder, QuotedSourceCursor,
    QuotedSourceError, QuotedSourceHeap, QuotedSourceKey, QuotedSourceMetadata, QuotedSourceRoot,
};
pub(crate) use types::TyCanon;
pub use types::{
    CallableClause, CallableValueKind, ClosureLitInfo, ClosureTarget, MapKey, Nominals, OpaqueVisibilityError, Sigma,
    Ty, TypeVarId, Types,
};
pub(crate) use world::JobCompletion;
pub use world::World;

#[cfg(test)]
mod artifact_test;
#[cfg(test)]
mod canon_test;
#[cfg(test)]
mod code_test;
#[cfg(test)]
mod compiler2_test;
#[cfg(test)]
mod contract_test;
#[cfg(test)]
mod drive_test;
#[cfg(test)]
mod elixir_surface_fixtures_test;
#[cfg(test)]
mod facts_test;
#[cfg(test)]
mod fixture_contract_harness_test;
#[cfg(test)]
mod fixture_facts;
#[cfg(test)]
mod fixture_facts_test;
#[cfg(test)]
mod fixture_metadata_test;
#[cfg(test)]
mod frontdoor_test;
#[cfg(test)]
mod identity_test;
#[cfg(test)]
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
mod product_drive_test;
#[cfg(test)]
mod quoted_function_test;
#[cfg(test)]
mod quoted_surface_test;
#[cfg(test)]
mod resolve_test;
#[cfg(test)]
mod scheduler_test;
#[cfg(test)]
mod scope_test;
#[cfg(test)]
mod semantic_analysis_test;
#[cfg(test)]
mod source_publish_test;
#[cfg(test)]
mod source_test;
#[cfg(test)]
mod telemetry_dump_test;
#[cfg(test)]
mod transport_contract_test;
#[cfg(test)]
mod transport_test;
#[cfg(test)]
mod type_expr_test;
#[cfg(test)]
mod work_start_reason_test;
#[cfg(test)]
mod world_test;
