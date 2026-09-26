//! The one way a compiler2 test drives a fixture.
//!
//! `Drive::fixture(n)` finds `fixtures/{n:05}_*.fz`, falling back to
//! `fixtures2/{n:05}_*.fz` for a fixture not yet moved there, reads it at
//! runtime, and submits it under its repo-relative path. There is no
//! source-string entry point: a test that needs a program the corpus does not
//! already carry adds a numbered `fixtures/` file for it, the same as any
//! other fixture.
//!
//! `.before_submit(|world| ...)` runs against the compiler's `World` before
//! either is submitted — the hook a test that pre-allocates unrelated
//! functions (to prove a result is independent of allocation order) mutates
//! through, instead of reaching for a bare `Compiler2::new()`.
//!
//! The default root is `main/0` under `ExecutableNeed::Value`; `.open_root`
//! overrides it for a fixture whose entry is a different function, or one
//! under a module. `.demand(|world| job)` queues a targeted job demand, built
//! against the `World` after the source and root are submitted, so the job
//! can name ids the submission mints.
//!
//! Three terminal methods run the compiler and hand back a `Settled`:
//! `.settle()` drives to `DriveOutcome::Resolved` and panics (naming the
//! fixture) otherwise; `.drive()` drives once and returns the raw outcome
//! alongside `Settled`, for a test that expects a diagnostic or an
//! unresolved drive; `.dump_stage(stage)` calls `drive_root_to_dump_stage`
//! directly instead of `drive()` — the product-pull path canon's tests read,
//! which settles a root's backend/native product without running the
//! semantic fixpoint layer at all.
//!
//! Every `Drive` installs `FunctionCapture`, `ModuleCapture`,
//! `CallsiteCapture`, `ReturnTypeCapture`, `LoweredBodyCapture`,
//! `BackendProgramCapture`, `NativeProgramCapture`, `OutputCapture` and
//! `DbgCapture` before submitting anything, so nothing a settled compile
//! publishes is missed. `Settled` exposes each as a typed lookup method
//! (`function`, `module`, `lowered_body`, `backend_program`, ...) plus the
//! raw capture accessors for a test that needs to walk every record.

use super::artifact::NativeProgram;
use super::drive::{DependencyKey, JobEffects};
use super::dump::DumpStage;
use super::pull::{ProductKey, ProductSettlement, ProductValue};
use super::{
    ActivationKey, AppliedStep, BackendProgram, CallSiteKey, CallSiteSummary, CodeSubmission, Compiler2, DriveOutcome,
    ExecutableNeed, FactKey, FunctionId, FunctionRef, Job, LoweredBody, ModuleId, RootId, RootSubmission, Ty, World,
};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};
use crate::exec::runtime::DbgCapture;
use crate::modules::identity::{ModuleDenotation, ModuleName};
use crate::telemetry::{ConfiguredTelemetry, Value};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

type OutputFacts = Vec<(FactKey, bool)>;

/// Locates fixture number `n`: exactly one `fixtures/{n:05}_*.fz`, else
/// exactly one `fixtures2/{n:05}_*.fz`. Panics loudly on zero or several
/// matches in whichever directory answers. `fixtures/` is the purpose-bearing
/// home every fixture is meant to reach; `fixtures2/` holds the numbered
/// fixtures that have not moved there yet.
fn locate_fixture(number: u32) -> (PathBuf, String) {
    let prefix = format!("{number:05}_");
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    for dir in ["fixtures", "fixtures2"] {
        let full_dir = manifest_dir.join(dir);
        let Ok(entries) = fs::read_dir(&full_dir) else { continue };
        let mut matches: Vec<PathBuf> = entries
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "fz"))
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with(&prefix))
            })
            .collect();
        match matches.len() {
            0 => continue,
            1 => {
                let path = matches.remove(0);
                let repo_relative = format!("{dir}/{}", path.file_name().unwrap().to_string_lossy());
                return (path, repo_relative);
            }
            _ => panic!("fixture {number:05} matches more than one file under {dir}/: {matches:?}"),
        }
    }
    panic!("no fixture numbered {number:05} found under fixtures/ or fixtures2/");
}

/// Where a numbered fixture's `main/0` (or an override) should be entered.
#[derive(Clone)]
struct RootRequest {
    module: Option<String>,
    name: String,
    arity: u64,
}

impl Default for RootRequest {
    fn default() -> Self {
        Self {
            module: None,
            name: "main".to_string(),
            arity: 0,
        }
    }
}

/// The telemetry captures every `Drive` installs before submitting any
/// source, so nothing a settled compile publishes is missed.
pub(crate) struct Captures {
    functions: FunctionCapture,
    modules: ModuleCapture,
    callsites: CallsiteCapture,
    return_types: ReturnTypeCapture,
    lowered_bodies: LoweredBodyCapture,
    backend_programs: BackendProgramCapture,
    native_programs: NativeProgramCapture,
    outputs: OutputCapture,
    dbg: DbgCapture,
}

impl Captures {
    fn install(telemetry: &ConfiguredTelemetry) -> Self {
        let functions = FunctionCapture::new();
        functions.install(telemetry);
        let modules = ModuleCapture::new();
        modules.install(telemetry);
        let callsites = CallsiteCapture::new();
        callsites.install(telemetry);
        let return_types = ReturnTypeCapture::new();
        return_types.install(telemetry);
        let lowered_bodies = LoweredBodyCapture::new();
        lowered_bodies.install(telemetry);
        let backend_programs = BackendProgramCapture::new();
        backend_programs.install(telemetry);
        let native_programs = NativeProgramCapture::new();
        native_programs.install(telemetry);
        let outputs = OutputCapture::new();
        outputs.install(telemetry);
        let dbg = DbgCapture::new();
        Self {
            functions,
            modules,
            callsites,
            return_types,
            lowered_bodies,
            backend_programs,
            native_programs,
            outputs,
            dbg,
        }
    }
}

/// Builds a demanded job from the `World` once the submission has minted its ids.
type DemandBuilder = Box<dyn FnOnce(&mut World) -> Job>;

/// The one way a compiler2 test drives a fixture. See the module doc comment.
pub(crate) struct Drive {
    compiler: Compiler2<ConfiguredTelemetry>,
    fixture_path: String,
    text: String,
    root_request: RootRequest,
    demands: Vec<DemandBuilder>,
    captures: Captures,
}

impl Drive {
    /// Submits fixture `number`'s source. Reads the file at runtime relative
    /// to `CARGO_MANIFEST_DIR`.
    pub(crate) fn fixture(number: u32) -> Self {
        let (path, fixture_path) = locate_fixture(number);
        let text = fs::read_to_string(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        Self::new(fixture_path, text)
    }

    fn new(fixture_path: String, text: String) -> Self {
        let telemetry = ConfiguredTelemetry::new();
        let captures = Captures::install(&telemetry);
        let mut compiler = Compiler2::new(telemetry);
        compiler.set_output(captures.dbg.sink());
        Self {
            compiler,
            fixture_path,
            text,
            root_request: RootRequest::default(),
            demands: Vec::new(),
            captures,
        }
    }

    /// Runs `mutate` against the compiler's `World` before source is
    /// submitted — the seam a test that pre-allocates unrelated functions (to
    /// prove a result does not depend on allocation order) mutates through.
    pub(crate) fn before_submit(mut self, mutate: impl FnOnce(&mut World)) -> Self {
        mutate(self.compiler.world_mut());
        self
    }

    /// The only root override: a function nothing calls, or one with open
    /// inputs. `module` is `None` for the global namespace.
    pub(crate) fn open_root(mut self, module: Option<&str>, name: &str, arity: u64) -> Self {
        self.root_request = RootRequest {
            module: module.map(str::to_string),
            name: name.to_string(),
            arity,
        };
        self
    }

    /// A targeted job demand, built against the `World` after the source and
    /// root are submitted and before the drive that `settle()`/`drive()` runs.
    pub(crate) fn demand(mut self, job: impl FnOnce(&mut World) -> Job + 'static) -> Self {
        self.demands.push(Box::new(job));
        self
    }

    /// The telemetry `Drive` will submit against — for a test that installs
    /// its own capture on top of the standard set before driving.
    pub(crate) fn telemetry(&self) -> &ConfiguredTelemetry {
        self.compiler.telemetry()
    }

    fn submit(&mut self) -> RootId {
        self.compiler.submit_code(CodeSubmission {
            name: Some(self.fixture_path.clone()),
            text: std::mem::take(&mut self.text),
        });
        let RootRequest { module, name, arity } = self.root_request.clone();
        let root = self.compiler.submit_root(RootSubmission {
            module_name: module,
            name,
            arity: arity as usize,
            need: ExecutableNeed::Value,
        });
        for build in std::mem::take(&mut self.demands) {
            let job = build(self.compiler.world_mut());
            self.compiler.demand(job);
        }
        root
    }

    /// Drives to `DriveOutcome::Resolved`, panicking with the fixture's path
    /// in the message otherwise.
    pub(crate) fn settle(mut self) -> Settled {
        let root = self.submit();
        let outcome = self.compiler.drive();
        assert!(
            matches!(outcome, DriveOutcome::Resolved),
            "{}: drive should settle: {outcome:?}",
            self.fixture_path
        );
        Settled::new(self.compiler, root, self.fixture_path, self.captures)
    }

    /// Drives once and hands back the raw outcome, for a test that expects a
    /// diagnostic or an unresolved drive.
    pub(crate) fn drive(mut self) -> (Settled, DriveOutcome<Job, DependencyKey>) {
        let root = self.submit();
        let outcome = self.compiler.drive();
        (
            Settled::new(self.compiler, root, self.fixture_path, self.captures),
            outcome,
        )
    }

    /// Drives the root to `stage` through `drive_root_to_dump_stage` — the
    /// product-pull path, which settles a backend/native product without
    /// running the semantic fixpoint layer `settle()`/`drive()` run.
    pub(crate) fn dump_stage(mut self, stage: DumpStage) -> Settled {
        let root = self.submit();
        self.compiler
            .drive_root_to_dump_stage(root, stage)
            .unwrap_or_else(|error| panic!("{}: should reach dump stage {stage:?}: {error}", self.fixture_path));
        Settled::new(self.compiler, root, self.fixture_path, self.captures)
    }
}

/// A driven fixture's settled compiler, its root, and every capture `Drive`
/// installed. The lookups the moved capture helpers provide are exposed as
/// methods; anything else reads `compiler()`/`compiler_mut()`/`world()`
/// directly.
pub(crate) struct Settled {
    compiler: Compiler2<ConfiguredTelemetry>,
    root: RootId,
    fixture_path: String,
    captures: Captures,
}

impl Settled {
    fn new(compiler: Compiler2<ConfiguredTelemetry>, root: RootId, fixture_path: String, captures: Captures) -> Self {
        Self {
            compiler,
            root,
            fixture_path,
            captures,
        }
    }

    pub(crate) fn compiler(&self) -> &Compiler2<ConfiguredTelemetry> {
        &self.compiler
    }

    pub(crate) fn compiler_mut(&mut self) -> &mut Compiler2<ConfiguredTelemetry> {
        &mut self.compiler
    }

    pub(crate) fn root(&self) -> RootId {
        self.root
    }

    pub(crate) fn world(&self) -> &World {
        self.compiler.world()
    }

    pub(crate) fn fixture_path(&self) -> &str {
        &self.fixture_path
    }

    pub(crate) fn function(&self, name: &str, arity: u64) -> FunctionId {
        function_id(&self.captures.functions, name, arity)
    }

    pub(crate) fn module(&self, name: &str) -> ModuleId {
        module_id(&self.captures.modules, name)
    }

    pub(crate) fn lowered_body(&self, function: FunctionId) -> LoweredBody {
        lowered_body(&self.captures.lowered_bodies, function)
    }

    /// The settled backend product for this run's root, materialized by
    /// whichever of `settle()`/`drive()`/`dump_stage()` requested it.
    pub(crate) fn backend_program(&self) -> Rc<BackendProgram> {
        self.captures.backend_programs.last(self.root).program
    }

    /// The settled native product for this run's root; only present after a
    /// `dump_stage(DumpStage::Native)` (or a production path that pulls one).
    pub(crate) fn native_program(&self) -> Rc<NativeProgram> {
        self.captures.native_programs.last(self.root).program
    }

    pub(crate) fn presence(&self, fact: FactKey, changed: bool) -> (FactKey, bool) {
        presence(fact, changed)
    }

    pub(crate) fn functions(&self) -> &FunctionCapture {
        &self.captures.functions
    }

    pub(crate) fn modules(&self) -> &ModuleCapture {
        &self.captures.modules
    }

    pub(crate) fn callsites(&self) -> &CallsiteCapture {
        &self.captures.callsites
    }

    pub(crate) fn return_types(&self) -> &ReturnTypeCapture {
        &self.captures.return_types
    }

    pub(crate) fn backend_programs(&self) -> &BackendProgramCapture {
        &self.captures.backend_programs
    }

    pub(crate) fn native_programs(&self) -> &NativeProgramCapture {
        &self.captures.native_programs
    }

    pub(crate) fn outputs(&self) -> &OutputCapture {
        &self.captures.outputs
    }

    pub(crate) fn dbg(&self) -> &DbgCapture {
        &self.captures.dbg
    }
}

pub(crate) fn output_facts(effects: &JobEffects) -> OutputFacts {
    let changed = effects.changed.iter().cloned().collect::<HashSet<_>>();
    effects
        .outputs
        .iter()
        .cloned()
        .map(|fact| {
            let changed = changed.contains(&fact);
            (fact, changed)
        })
        .collect()
}

pub(crate) fn module_name(text: &str) -> ModuleName {
    ModuleName::parse_dotted(text).unwrap()
}

type JobOutputMap = Rc<RefCell<HashMap<Job, Vec<OutputFacts>>>>;
type AppliedSteps = Rc<RefCell<Vec<AppliedStep<Job, DependencyKey>>>>;
type EntryDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<Rc<PatternDispatchPlan<Ty>>>>>>;
type GuardDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<Arc<PatternGuardDispatch<Ty>>>>>>;
type LoweredBodyDefs = Rc<RefCell<HashMap<FunctionId, Vec<LoweredBody>>>>;
type FunctionDefs = Rc<RefCell<HashMap<FunctionId, FunctionDefinedRecord>>>;
type SourceNotes = Rc<RefCell<Vec<FunctionRef>>>;
type ModuleDefs = Rc<RefCell<HashMap<ModuleId, Vec<ModuleDenotation>>>>;
type CallsiteDefs = Rc<RefCell<Vec<CallsiteDefinedRecord>>>;
type BackendProgramDefs = Rc<RefCell<Vec<BackendProgramRecord>>>;
type NativeProgramDefs = Rc<RefCell<Vec<NativeProgramRecord>>>;
type ReturnTypeDefs = Rc<RefCell<Vec<ReturnTypeRecord>>>;
type ActivationInputDefs = Rc<RefCell<Vec<ActivationInputRecord>>>;

type ListRetentionCounts = Rc<RefCell<Vec<(crate::compiler2::RootId, u64, u64)>>>;

pub(crate) fn presence(fact: FactKey, changed: bool) -> (FactKey, bool) {
    (fact, changed)
}

pub(crate) struct OutputCapture {
    outputs: JobOutputMap,
    stops: Rc<RefCell<Vec<JobSpanStop>>>,
}

pub(crate) struct WorkGraphCapture {
    steps: AppliedSteps,
}

#[derive(Debug, Clone)]
pub(crate) struct JobSpanStop {
    pub(crate) job: Job,
    pub(crate) effects_present: bool,
    pub(crate) effects: Option<JobEffects>,
}

#[derive(Debug, Clone)]
pub(crate) struct FunctionDefinedRecord {
    pub(crate) function_id: FunctionId,
    pub(crate) module_id: ModuleId,
    pub(crate) arity: u64,
    pub(crate) clauses: u64,
    pub(crate) owner_function_id: Option<FunctionId>,
    pub(crate) function_ref: FunctionRef,
}

#[derive(Debug, Clone)]
pub(crate) struct CallsiteDefinedRecord {
    pub(crate) key: CallSiteKey,
    pub(crate) summary: CallSiteSummary,
}

#[derive(Debug, Clone)]
pub(crate) struct BackendProgramRecord {
    pub(crate) root_id: crate::compiler2::RootId,
    pub(crate) changed: bool,
    pub(crate) program: Rc<BackendProgram>,
}

#[derive(Debug, Clone)]
pub(crate) struct NativeProgramRecord {
    pub(crate) root_id: crate::compiler2::RootId,
    pub(crate) program: Rc<NativeProgram>,
}

#[derive(Debug, Clone)]
pub(crate) struct ReturnTypeRecord {
    pub(crate) activation: ActivationKey,
    pub(crate) return_ty: Ty,
}

#[derive(Debug, Clone)]
pub(crate) struct ActivationInputRecord {
    pub(crate) activation: ActivationKey,
    pub(crate) inputs: Vec<Ty>,
}

pub(crate) struct FunctionCapture {
    defs: FunctionDefs,
}

pub(crate) struct ModuleCapture {
    defs: ModuleDefs,
}

pub(crate) struct CallsiteCapture {
    defs: CallsiteDefs,
}

pub(crate) struct ReturnTypeCapture {
    defs: ReturnTypeDefs,
}

pub(crate) struct ActivationInputCapture {
    defs: ActivationInputDefs,
}

pub(crate) struct BackendProgramCapture {
    defs: BackendProgramDefs,
}

pub(crate) struct NativeProgramCapture {
    defs: NativeProgramDefs,
}

pub(crate) struct ListRetentionTelemetryCapture {
    counts: ListRetentionCounts,
}

impl ListRetentionTelemetryCapture {
    pub(crate) fn new() -> Self {
        Self {
            counts: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let counts = Rc::clone(&self.counts);
        telemetry.attach_raw_event2::<crate::compiler2::RootId, BackendProgram, _>(
            &["fz", "compiler2", "native_program", "list_retention"],
            move |_, _, _, root, program| {
                let (construction_count, physical_capture_count) =
                    crate::telemetry::jsonl::list_retention_counts(program);
                counts
                    .borrow_mut()
                    .push((*root, construction_count, physical_capture_count));
            },
        );
    }

    pub(crate) fn last(&self) -> Option<(crate::compiler2::RootId, u64, u64)> {
        self.counts.borrow().last().copied()
    }
}

pub(crate) struct EntryDispatchCapture {
    plans: EntryDispatchMap,
}

pub(crate) struct GuardDispatchCapture {
    dispatches: GuardDispatchMap,
}

pub(crate) struct LoweredBodyCapture {
    bodies: LoweredBodyDefs,
}

impl OutputCapture {
    pub(crate) fn new() -> Self {
        Self {
            outputs: Rc::new(RefCell::new(HashMap::new())),
            stops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let outputs = Rc::clone(&self.outputs);
        let stops = Rc::clone(&self.stops);
        telemetry.attach_raw_event2::<crate::compiler2::World, crate::compiler2::JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, world, completion| {
                let job = completion.job.clone();
                let changed = completion
                    .changed
                    .iter()
                    .filter(|change| change.content_changed())
                    .filter_map(|change| change.key.fact().cloned())
                    .collect();
                let effects = JobEffects {
                    reads: world.job_reads(&job).into_iter().collect(),
                    waits: completion
                        .blocked
                        .iter()
                        .cloned()
                        .filter_map(super::drive::as_fact_use)
                        .collect(),
                    outputs: world.job_outputs(&job),
                    changed,
                    ..JobEffects::default()
                };
                stops.borrow_mut().push(JobSpanStop {
                    job: job.clone(),
                    effects_present: true,
                    effects: Some(effects.clone()),
                });
                outputs
                    .borrow_mut()
                    .entry(job)
                    .or_default()
                    .push(output_facts(&effects));
            },
        );
    }

    pub(crate) fn take(&self, job: Job) -> Option<OutputFacts> {
        let mut outputs = self.outputs.borrow_mut();
        let matches = outputs.get_mut(&job)?;
        let output = matches.pop();
        if matches.is_empty() {
            outputs.remove(&job);
        }
        output
    }

    pub(crate) fn stop(&self, job: Job) -> JobSpanStop {
        self.stops
            .borrow()
            .iter()
            .rev()
            .find(|stop| stop.job == job)
            .cloned()
            .unwrap_or_else(|| panic!("job stop event for {job:?}"))
    }

    pub(crate) fn effects(&self, job: Job) -> JobEffects {
        self.stop(job.clone())
            .effects
            .unwrap_or_else(|| panic!("job effects for {job:?}"))
    }

    pub(crate) fn stops_matching(&self, mut matches: impl FnMut(&Job) -> bool) -> Vec<JobSpanStop> {
        self.stops
            .borrow()
            .iter()
            .filter(|stop| matches(&stop.job))
            .cloned()
            .collect()
    }
}

impl WorkGraphCapture {
    pub(crate) fn new() -> Self {
        Self {
            steps: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let steps = Rc::clone(&self.steps);
        telemetry.attach_raw_event2::<crate::compiler2::World, crate::compiler2::JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, _, completion| steps.borrow_mut().push(completion.step.clone()),
        );
    }

    pub(crate) fn all(&self) -> Vec<AppliedStep<Job, DependencyKey>> {
        self.steps.borrow().clone()
    }
}

impl FunctionCapture {
    pub(crate) fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event2::<crate::compiler2::World, FunctionId, _>(
            &["fz", "compiler2", "function"],
            move |name, _, _, world, function| {
                let from_source = match name {
                    ["fz", "compiler2", "function", "defined"] => false,
                    ["fz", "compiler2", "function", "source", "noted"] => true,
                    _ => return,
                };
                record_function_definition(&defs, world, *function, None, from_source);
            },
        );
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event3::<crate::compiler2::World, FunctionId, FunctionId, _>(
            &["fz", "compiler2", "function", "defined"],
            move |_, _, _, world, function, owner| {
                record_function_definition(&defs, world, *function, Some(*owner), false);
            },
        );
    }

    pub(crate) fn all(&self) -> Vec<FunctionDefinedRecord> {
        self.defs.borrow().values().cloned().collect()
    }

    pub(crate) fn id(&self, name: &str, arity: u64) -> FunctionId {
        self.defs
            .borrow()
            .values()
            .find(|record| record.function_ref.is_named(name) && record.arity == arity)
            .map(|record| record.function_id)
            .unwrap_or_else(|| panic!("function fact for {name}/{arity}"))
    }

    /// The one `name/arity` owned by the module with this last segment, for
    /// sources where two modules define the same name.
    pub(crate) fn id_in_module(&self, module: &str, name: &str, arity: u64) -> FunctionId {
        self.try_id_in_module(module, name, arity)
            .unwrap_or_else(|| panic!("function fact for {module}.{name}/{arity}"))
    }

    pub(crate) fn try_id_in_module(&self, module: &str, name: &str, arity: u64) -> Option<FunctionId> {
        use crate::compiler2::identity::FunctionOrigin;
        self.defs
            .borrow()
            .values()
            .find(|record| {
                record.function_ref.is_named(name)
                    && record.arity == arity
                    && matches!(
                        &record.function_ref.denotation.origin,
                        FunctionOrigin::Named {
                            module: Some(ModuleDenotation::Named(owner)),
                            ..
                        } if owner.last_segment() == module
                    )
            })
            .map(|record| record.function_id)
    }
}

impl SourceNoteCapture {
    pub(crate) fn new() -> Self {
        Self {
            notes: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let event: &'static [&'static str] = &["fz", "compiler2", "function", "source", "noted"];
        let notes = Rc::clone(&self.notes);
        telemetry.attach_raw_event2::<crate::compiler2::World, FunctionId, _>(
            event,
            move |name, _, _, world, function| {
                if name == event {
                    notes.borrow_mut().push(world.function_ref(*function).clone());
                }
            },
        );
    }

    pub(crate) fn count(&self, name: &str, arity: usize) -> usize {
        self.notes
            .borrow()
            .iter()
            .filter(|function_ref| function_ref.is_named(name) && function_ref.arity == arity)
            .count()
    }
}

impl ModuleCapture {
    pub(crate) fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event2::<crate::compiler2::World, ModuleId, _>(
            &["fz", "compiler2", "module", "defined"],
            move |_, _, _, world, module| {
                defs.borrow_mut().entry(*module).or_default().push(
                    world
                        .module_denotation(*module)
                        .expect("defined module denotation")
                        .clone(),
                );
            },
        );
    }

    pub(crate) fn qualified_name(&self, module_id: ModuleId) -> String {
        if module_id == ModuleId::GLOBAL {
            return "<top-level>".to_string();
        }
        self.defs
            .borrow()
            .get(&module_id)
            .and_then(|defs| defs.last())
            .map(ToString::to_string)
            .unwrap_or_else(|| panic!("module.defined for {}", module_id.as_u32()))
    }

    pub(crate) fn try_qualified_name(&self, module_id: ModuleId) -> Option<String> {
        if module_id == ModuleId::GLOBAL {
            return Some("<top-level>".to_string());
        }
        self.defs
            .borrow()
            .get(&module_id)
            .and_then(|defs| defs.last())
            .map(ToString::to_string)
    }

    pub(crate) fn defined_names(&self) -> Vec<String> {
        let ids = self.defs.borrow().keys().copied().collect::<Vec<_>>();
        ids.into_iter().map(|id| self.qualified_name(id)).collect()
    }
}

impl CallsiteCapture {
    pub(crate) fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event2::<crate::compiler2::World, CallSiteKey, _>(
            &["fz", "compiler2", "callsite", "defined"],
            move |_, _, _, world, key| {
                let Some(summary) = world.callsite_summary(key) else {
                    return;
                };
                defs.borrow_mut().push(CallsiteDefinedRecord {
                    key: key.clone(),
                    summary: summary.clone(),
                });
            },
        );
    }

    pub(crate) fn all(&self) -> Vec<CallsiteDefinedRecord> {
        self.defs.borrow().clone()
    }
}

impl ReturnTypeCapture {
    pub(crate) fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
            &["fz", "compiler2", "return_type", "defined"],
            move |_, _, _, world, activation| {
                let Some(return_ty) = world.activation_return_evidence(activation) else {
                    return;
                };
                defs.borrow_mut().push(ReturnTypeRecord {
                    activation: activation.clone(),
                    return_ty,
                });
            },
        );
    }

    pub(crate) fn last_for_function(
        &self,
        root_id: crate::compiler2::RootId,
        function_id: FunctionId,
    ) -> ReturnTypeRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.activation.root == root_id && record.activation.function == function_id)
            .cloned()
            .unwrap_or_else(|| panic!("return_type.defined for root={root_id:?} function={function_id:?}"))
    }

    /// Every `return_type.defined` record for one activation, in emission order —
    /// used to inspect the `changed` split (fz-go4.18.31) directly rather than
    /// through the Ty-id-churn proxy (a re-published Ty can carry a fresh id even
    /// when the fact did not move).
    pub(crate) fn records_for_function(
        &self,
        root_id: crate::compiler2::RootId,
        function_id: FunctionId,
    ) -> Vec<ReturnTypeRecord> {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.activation.root == root_id && record.activation.function == function_id)
            .cloned()
            .collect()
    }

    /// The distinct activation keys under `root_id` that ever earned a settled
    /// (`Some`) return through `return_type.defined`. Intersecting this with the
    /// `activation_analysis.defined` keys keeps only converged activations —
    /// mid-convergence intermediates that never settle a return drop out — a
    /// telemetry-only stand-in for `world.activation_return(..).is_some()` where
    /// the test drives through `Compiler2` and has no direct `World` handle.
    pub(crate) fn settled_activations(&self, root_id: crate::compiler2::RootId) -> HashSet<ActivationKey> {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.activation.root == root_id)
            .map(|record| record.activation.clone())
            .collect()
    }
}

impl ActivationInputCapture {
    pub(crate) fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event2::<crate::compiler2::World, super::world::JobCompletion, _>(
            &["fz", "compiler2", "activation_inputs", "defined"],
            move |_, _, _, world, completion| {
                for activation in &completion.activation_input_changed {
                    let Some(inputs) = world.activation_inputs_joined(activation) else {
                        continue;
                    };
                    defs.borrow_mut().push(ActivationInputRecord {
                        activation: activation.clone(),
                        inputs,
                    });
                }
            },
        );
    }

    pub(crate) fn last_for_function(
        &self,
        root_id: crate::compiler2::RootId,
        function_id: FunctionId,
    ) -> ActivationInputRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.activation.root == root_id && record.activation.function == function_id)
            .cloned()
            .unwrap_or_else(|| panic!("activation_inputs.defined for root={root_id:?} function={function_id:?}"))
    }
}

impl BackendProgramCapture {
    pub(crate) fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
            &["fz", "compiler2", "pull", "product", "settled"],
            move |_, _, _, key, value, settlement| {
                if let (ProductKey::RootBackendProduct(root), ProductValue::RootBackendProduct(answer)) = (key, value)
                    && settlement.changed
                {
                    defs.borrow_mut().push(BackendProgramRecord {
                        root_id: *root,
                        changed: settlement.changed,
                        program: Rc::clone(answer),
                    });
                }
            },
        );
    }

    pub(crate) fn last(&self, root_id: crate::compiler2::RootId) -> BackendProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("RootBackendProduct settlement for {root_id:?}"))
    }

    pub(crate) fn records(&self, root_id: crate::compiler2::RootId) -> Vec<BackendProgramRecord> {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.root_id == root_id)
            .cloned()
            .collect()
    }
}

impl NativeProgramCapture {
    pub(crate) fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let defs = Rc::clone(&self.defs);
        telemetry.attach_raw_event3::<crate::compiler2::ProductKey, ProductValue, ProductSettlement, _>(
            &["fz", "compiler2", "pull", "product", "settled"],
            move |_, _, _, key, value, _settlement| {
                let (crate::compiler2::ProductKey::NativeProgram(root), ProductValue::NativeProgram(program)) =
                    (key, value)
                else {
                    return;
                };
                defs.borrow_mut().push(NativeProgramRecord {
                    root_id: *root,
                    program: Rc::clone(program),
                });
            },
        );
    }

    pub(crate) fn last(&self, root_id: crate::compiler2::RootId) -> NativeProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("NativeProgram product settlement for {root_id:?}"))
    }
}

impl GuardDispatchCapture {
    pub(crate) fn new() -> Self {
        Self {
            dispatches: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let dispatches = Rc::clone(&self.dispatches);
        telemetry.attach_raw_event2::<crate::compiler2::World, FunctionId, _>(
            &["fz", "compiler2", "guard_dispatch", "defined"],
            move |_, _, _, world, function| {
                dispatches
                    .borrow_mut()
                    .entry(*function)
                    .or_default()
                    .push(world.guard_dispatch(*function));
            },
        );
    }

    pub(crate) fn take(&self, function: FunctionId) -> Option<Arc<PatternGuardDispatch<Ty>>> {
        let mut dispatches = self.dispatches.borrow_mut();
        let matches = dispatches.get_mut(&function)?;
        let dispatch = matches.pop();
        if matches.is_empty() {
            dispatches.remove(&function);
        }
        dispatch
    }

    pub(crate) fn last(&self, function: FunctionId) -> Option<Arc<PatternGuardDispatch<Ty>>> {
        self.dispatches
            .borrow()
            .get(&function)
            .and_then(|matches| matches.last())
            .cloned()
    }
}

impl EntryDispatchCapture {
    pub(crate) fn new() -> Self {
        Self {
            plans: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let plans = Rc::clone(&self.plans);
        telemetry.attach_raw_event2::<crate::compiler2::World, FunctionId, _>(
            &["fz", "compiler2", "entry_dispatch", "defined"],
            move |_, _, _, world, function| {
                plans
                    .borrow_mut()
                    .entry(*function)
                    .or_default()
                    .push(world.entry_dispatch(*function));
            },
        );
    }

    pub(crate) fn take(&self, function: FunctionId) -> Option<Rc<PatternDispatchPlan<Ty>>> {
        let mut plans = self.plans.borrow_mut();
        let matches = plans.get_mut(&function)?;
        let plan = matches.pop();
        if matches.is_empty() {
            plans.remove(&function);
        }
        plan
    }

    pub(crate) fn last(&self, function: FunctionId) -> Option<Rc<PatternDispatchPlan<Ty>>> {
        self.plans
            .borrow()
            .get(&function)
            .and_then(|matches| matches.last())
            .cloned()
    }
}

impl LoweredBodyCapture {
    pub(crate) fn new() -> Self {
        Self {
            bodies: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let bodies = Rc::clone(&self.bodies);
        telemetry.attach_raw_event2::<crate::compiler2::World, FunctionId, _>(
            &["fz", "compiler2", "lowered_body", "defined"],
            move |_, _, _, world, function| {
                bodies
                    .borrow_mut()
                    .entry(*function)
                    .or_default()
                    .push((*world.lowered_body(*function)).clone());
            },
        );
    }

    pub(crate) fn take(&self, function: FunctionId) -> Option<LoweredBody> {
        let mut bodies = self.bodies.borrow_mut();
        let matches = bodies.get_mut(&function)?;
        let body = matches.pop();
        if matches.is_empty() {
            bodies.remove(&function);
        }
        body
    }
}

pub(crate) struct SourceNoteCapture {
    notes: SourceNotes,
}

pub(crate) fn record_function_definition(
    defs: &FunctionDefs,
    world: &crate::compiler2::World,
    function_id: FunctionId,
    owner_function_id: Option<FunctionId>,
    from_source: bool,
) {
    let function_ref = world.function_ref(function_id);
    let module_id = function_ref.module;
    let clauses = if from_source {
        world
            .function_source(function_id)
            .and_then(|source| {
                let source_map = world.source_map();
                crate::compiler2::quoted_function::derive_function_surface(&source.source, &source_map.borrow()).ok()
            })
            .map_or(0, |surface| surface.clauses.len() as u64)
    } else {
        world.function_surface(function_id).clauses.len() as u64
    };
    defs.borrow_mut().insert(
        function_id,
        FunctionDefinedRecord {
            function_id,
            module_id,
            arity: function_ref.arity as u64,
            clauses,
            owner_function_id,
            function_ref: function_ref.clone(),
        },
    );
}

pub(crate) fn metadata_str<'a>(event: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match event.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        None if key == "code" => event
            .diagnostic
            .as_ref()
            .map(|diagnostic| diagnostic.code.0)
            .unwrap_or_else(|| panic!("diagnostic missing for metadata key `{key}`")),
        None if key == "message" => event
            .diagnostic
            .as_ref()
            .map(|diagnostic| diagnostic.message.as_str())
            .unwrap_or_else(|| panic!("diagnostic missing for metadata key `{key}`")),
        other => panic!("metadata key `{key}` missing or not str: {other:?}"),
    }
}

pub(crate) fn guard_dispatch(capture: &GuardDispatchCapture, function: FunctionId) -> Arc<PatternGuardDispatch<Ty>> {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("guard_dispatch.defined for {function:?}"))
}

pub(crate) fn entry_dispatch(capture: &EntryDispatchCapture, function: FunctionId) -> Rc<PatternDispatchPlan<Ty>> {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("entry_dispatch.defined for {function:?}"))
}

pub(crate) fn latest_guard_dispatch(
    capture: &GuardDispatchCapture,
    function: FunctionId,
) -> Arc<PatternGuardDispatch<Ty>> {
    capture
        .last(function)
        .unwrap_or_else(|| panic!("guard_dispatch.defined for {function:?}"))
}

pub(crate) fn latest_entry_dispatch(
    capture: &EntryDispatchCapture,
    function: FunctionId,
) -> Rc<PatternDispatchPlan<Ty>> {
    capture
        .last(function)
        .unwrap_or_else(|| panic!("entry_dispatch.defined for {function:?}"))
}

pub(crate) fn lowered_body(capture: &LoweredBodyCapture, function: FunctionId) -> LoweredBody {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("lowered_body.defined for {function:?}"))
}

pub(crate) fn backend_executable(
    program: &BackendProgram,
    function: FunctionId,
) -> (usize, &crate::compiler2::BackendExecutable) {
    program
        .executables()
        .iter()
        .enumerate()
        .find(|(_, executable)| executable.key.activation.function == function)
        .map(|(index, executable)| (index, executable.as_ref()))
        .unwrap_or_else(|| panic!("backend executable for {function:?}"))
}

pub(crate) fn assert_resolved(outcome: DriveOutcome<Job, DependencyKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

pub(crate) fn function_id(capture: &FunctionCapture, name: &str, arity: u64) -> FunctionId {
    capture.id(name, arity)
}

pub(crate) fn module_function_id(capture: &FunctionCapture, module: &str, name: &str, arity: u64) -> FunctionId {
    capture.id_in_module(module, name, arity)
}

pub(crate) fn try_module_function_id(
    capture: &FunctionCapture,
    module: &str,
    name: &str,
    arity: u64,
) -> Option<FunctionId> {
    capture.try_id_in_module(module, name, arity)
}

/// Records every `ActivationKey` the semantic pass publishes through
/// `activation_analysis.defined`. A key can be republished across rounds (and,
/// before convergence, a transient key can appear); callers dedup by key and
/// filter to the live frontier via `world.activation_analysis` to recover the
/// settled analyzed-activation set.
pub(crate) struct ActivationAnalysisCapture {
    keys: Rc<RefCell<Vec<ActivationKey>>>,
}

impl ActivationAnalysisCapture {
    pub(crate) fn new() -> Self {
        Self {
            keys: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub(crate) fn install(&self, telemetry: &ConfiguredTelemetry) {
        let keys = Rc::clone(&self.keys);
        telemetry.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
            &["fz", "compiler2", "activation_analysis", "defined"],
            move |_, _, _, _, activation| keys.borrow_mut().push(activation.clone()),
        );
    }

    pub(crate) fn keys_for_root(&self, root: crate::compiler2::RootId) -> Vec<ActivationKey> {
        self.keys
            .borrow()
            .iter()
            .filter(|key| key.root == root)
            .cloned()
            .collect()
    }
}

pub(crate) fn generated_functions_owned_by(capture: &FunctionCapture, owner: FunctionId) -> Vec<FunctionDefinedRecord> {
    capture
        .all()
        .into_iter()
        .filter(|record| record.owner_function_id == Some(owner))
        .collect()
}

pub(crate) fn function_id_in_module(
    functions: &FunctionCapture,
    modules: &ModuleCapture,
    module_name: &str,
    name: &str,
    arity: u64,
) -> FunctionId {
    functions
        .all()
        .into_iter()
        .find(|record| {
            record.function_ref.is_named(name)
                && record.arity == arity
                && modules.try_qualified_name(record.module_id).as_deref() == Some(module_name)
        })
        .map(|record| record.function_id)
        .unwrap_or_else(|| panic!("function.defined for {module_name}.{name}/{arity}"))
}

pub(crate) fn module_id(capture: &ModuleCapture, name: &str) -> ModuleId {
    capture
        .defs
        .borrow()
        .keys()
        .copied()
        .find(|module_id| capture.qualified_name(*module_id) == name)
        .unwrap_or_else(|| panic!("module.defined for {name}"))
}

pub(crate) fn function_fq_name(function: &FunctionDefinedRecord, modules: &ModuleCapture) -> String {
    if function.module_id == ModuleId::GLOBAL {
        function.function_ref.display_name()
    } else {
        format!(
            "{}.{}",
            modules.qualified_name(function.module_id),
            function.function_ref.display_name()
        )
    }
}

pub(crate) fn function_module_name(function: &FunctionDefinedRecord, modules: &ModuleCapture) -> String {
    modules
        .try_qualified_name(function.module_id)
        .unwrap_or_else(|| format!("<module:{}>", function.module_id.as_u32()))
}

pub(crate) fn module_indexed_ids(outputs: &OutputFacts) -> Vec<crate::compiler2::ModuleId> {
    outputs
        .iter()
        .filter_map(|(fact, _)| match fact {
            FactKey::ModuleIndexed(module_id) => Some(*module_id),
            _ => None,
        })
        .collect()
}

pub(crate) fn named_module_id(world: &crate::compiler2::World, modules: &[ModuleId], name: &str) -> ModuleId {
    let expected = module_name(name);
    modules
        .iter()
        .copied()
        .find(|module| world.module_name(*module) == Some(&expected))
        .unwrap_or_else(|| panic!("indexed module `{name}`"))
}
