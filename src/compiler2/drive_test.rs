use super::{AppliedStep, CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, Job, RootSubmission};
use crate::compiler2::artifact::{BackendCallableReturn, BackendEntry, BackendReturnFlow, BackendTail, CallEdge};
use crate::compiler2::artifact::{
    NativeBodyOrigin, NativeCallableBoundaryId, NativeEntryAbi, NativeGraphSharingWork, NativeProgram,
};
use crate::compiler2::drive::{DependencyKey, JobEffects};
use crate::compiler2::pull::{ProductKey, ProductSettlement, ProductValue, TransportCarrier};
use crate::compiler2::{
    AbiValueRepr, ActivationKey, BackendBody, BackendEntryOrigin, BackendProgram, BackendReturnLayout, BackendStep,
    CallSiteId, CallSiteKey, CallSiteSummary, CallTarget, ControlEntryOrigin, ExecutableKey, FactKey, FactUse,
    FunctionId, FunctionRef, LoweredBody, LoweredStep, LoweredTail, ModuleId, ModuleState, Namespace, QuotedSourceHeap,
    QuotedSourceMetadata, RuntimeDemand, SelectedCallee, Ty, TypeName, TypeVarId, Types, ValueId, World,
    parse_quoted_program,
};
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::dispatch_matrix::{Region, SubjectId};
use crate::exec::runtime::{DbgCapture, ProcessExitCapture};
use crate::fz_ir::{ExternTy, FnId, PhysicalCapability, Prim as IrPrim, Stmt as IrStmt, Term as IrTerm};
use crate::ir_interp::{
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset, tests_support_lock,
};
use crate::telemetry::handler::{Event, EventKind};
use crate::telemetry::sink::NullTelemetry;
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

type OutputFacts = Vec<(FactKey, bool)>;
type JobOutputMap = Rc<RefCell<HashMap<Job, Vec<OutputFacts>>>>;
type AppliedSteps = Rc<RefCell<Vec<AppliedStep<Job, DependencyKey>>>>;
type EntryDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<PatternDispatchPlan<Ty>>>>>;
type GuardDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<PatternGuardDispatch<Ty>>>>>;
type LoweredBodyDefs = Rc<RefCell<HashMap<FunctionId, Vec<LoweredBody>>>>;
type FunctionDefs = Rc<RefCell<HashMap<FunctionId, FunctionDefinedRecord>>>;
type SourceNotes = Rc<RefCell<Vec<FunctionRef>>>;
type ModuleDefs = Rc<RefCell<HashMap<ModuleId, Vec<ModuleState>>>>;
type CallsiteDefs = Rc<RefCell<Vec<CallsiteDefinedRecord>>>;
type BackendProgramDefs = Rc<RefCell<Vec<BackendProgramRecord>>>;
type NativeProgramDefs = Rc<RefCell<Vec<NativeProgramRecord>>>;
type ReturnTypeDefs = Rc<RefCell<Vec<ReturnTypeRecord>>>;
type ActivationInputDefs = Rc<RefCell<Vec<ActivationInputRecord>>>;
type PublishedStructFields = Rc<RefCell<Vec<(u32, Vec<String>)>>>;
type ReusableConsCounts = Rc<RefCell<Vec<(crate::compiler2::RootId, u64, u64)>>>;

fn settle_native_product(compiler: &mut Compiler2<ConfiguredTelemetry>, root: crate::compiler2::RootId) {
    compiler
        .drive_root_to_dump_stage(root, crate::compiler2::dump::DumpStage::Native)
        .expect("native product should settle");
}

#[test]
fn executable_construction_and_runtime_demand_share_one_world_type_projection() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("shared_runtime_demand_projection.fz".to_string()),
        text: "fn add_one(x), do: x + 1\nfn twice(x), do: add_one(add_one(x))\nfn main(), do: twice(40)\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let executables = compiler
        .product_executable_inventory(root)
        .expect("the shared-projection fixture should compile");
    let world = compiler.world();

    let mut uses = Vec::new();
    for executable in executables {
        let facts = world
            .executable_facts(&executable)
            .expect("each materialized executable should retain its settled facts");
        let demand_facts = facts.runtime_demand_facts(world.runtime_demand_type_projections());
        for &ty in facts.analysis().value_types.values() {
            if world.types().is_integer(&ty) {
                uses.push(demand_facts.projection_identity(ty));
            }
        }
    }
    assert!(
        uses.len() >= 2,
        "the fixture should exercise the same integer projection in multiple executable constructions",
    );
    assert!(
        uses.iter().all(|projection| *projection == uses[0]),
        "construction and formula views must borrow one World-owned projection for an interned type",
    );
}

#[test]
fn executable_facts_are_one_world_owned_scheduler_fact_with_exact_semantic_reads() {
    let tel = ConfiguredTelemetry::new();
    let product_lifecycle = Rc::new(RefCell::new(Vec::<(&'static str, String)>::new()));
    let observed_products = Rc::clone(&product_lifecycle);
    tel.attach_raw_event3::<
        crate::compiler2::pull::ProductKey,
        crate::compiler2::pull::ProductValue,
        crate::compiler2::pull::ProductSettlement,
        _,
    >(
        &["fz", "compiler2", "pull", "product", "settled"],
        move |_, _, _, key, _, _| {
            observed_products
                .borrow_mut()
                .push(("settled", key.kind().to_string()))
        },
    );
    for leaf in ["displaced", "cache_hit"] {
        let observed_products = Rc::clone(&product_lifecycle);
        tel.attach_raw_event1::<crate::compiler2::pull::ProductKey, _>(
            &["fz", "compiler2", "pull", "product", leaf],
            move |_, _, _, key| observed_products.borrow_mut().push((leaf, key.kind().to_string())),
        );
    }
    let demanded_executables = Rc::new(RefCell::new(HashSet::<ExecutableKey>::new()));
    let observed_demand = Rc::clone(&demanded_executables);
    tel.attach_raw_event1::<crate::compiler2::PullSession, _>(
        &["fz", "compiler2", "pull", "session", "finished"],
        move |_, _, _, session| {
            observed_demand
                .borrow_mut()
                .extend(session.demanded_executables().iter().cloned());
        },
    );
    let conclusions = Rc::new(RefCell::new(Vec::<(ExecutableKey, Vec<FactKey>)>::new()));
    let observed_conclusions = Rc::clone(&conclusions);
    tel.attach_raw_event2::<World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, world, completion| {
            let Job::DeriveExecutableFacts(executable) = &completion.job else {
                return;
            };
            let outputs = world.job_outputs(&completion.job);
            if outputs.contains(&FactKey::ExecutableFacts(executable.clone())) {
                observed_conclusions.borrow_mut().push((executable.clone(), outputs));
            }
        },
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("executable_facts_direct_fact.fz".to_string()),
        text: "fn add_one(x), do: x + 1\nfn main(), do: add_one(41)\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let executables = compiler
        .product_executable_inventory(root)
        .expect("the direct executable-facts fixture should compile");
    let world = compiler.world();
    assert!(
        product_lifecycle
            .borrow()
            .iter()
            .all(|(_, kind)| kind != "executable_facts"),
        "ExecutableFacts must be absent from every product lifecycle leaf: {:?}",
        product_lifecycle.borrow(),
    );
    assert!(!executables.is_empty());
    let demanded = demanded_executables.borrow().clone();
    let conclusions = conclusions.borrow();
    assert_eq!(
        conclusions
            .iter()
            .map(|(executable, _)| executable.clone())
            .collect::<HashSet<_>>(),
        demanded,
        "each demanded executable identity must close through its exact DeriveExecutableFacts work-graph conclusion",
    );
    assert_eq!(
        conclusions.len(),
        demanded.len(),
        "each demanded executable must have exactly one concluding executable-fact publication",
    );
    for (executable, outputs) in conclusions.iter() {
        assert_eq!(
            outputs,
            &[FactKey::ExecutableFacts(executable.clone())],
            "the correlated producer conclusion must publish only its exact executable fact",
        );
    }
    for executable in executables {
        let fact = FactKey::ExecutableFacts(executable.clone());
        let job = Job::DeriveExecutableFacts(executable.clone());
        let facts = world
            .executable_facts(&executable)
            .expect("every materialized executable should have one World-owned fact value");
        let mut expected_reads = HashSet::from([
            FactUse::settled(FactKey::ActivationAnalyzed(executable.activation.clone())),
            FactUse::settled(FactKey::LoweredBody(executable.activation.function)),
            FactUse::settled(FactKey::EntryDispatch(executable.activation.function)),
        ]);
        expected_reads.extend(facts.analysis().callsites.iter().map(|callsite| {
            FactUse::settled(FactKey::CallSiteSummary(CallSiteKey {
                activation: executable.activation.clone(),
                callsite: *callsite,
            }))
        }));

        assert_eq!(world.fact_revision(&fact), Some(1));
        assert_eq!(world.job_reads(&job), expected_reads);
        assert_eq!(world.job_outputs(&job), vec![fact]);
    }
}

// The receive-after join is `int | :timeout`; `bump`'s atom clause diverges
// through `panic`, so the post-receive call lowers as a two-member dispatch
// with one delivering and one no-return member. (Ill-typed arithmetic can no
// longer play the divergent member: `:timeout + 2` is a fatal compile-time
// spec violation now.)
const RECEIVE_AFTER_DIVERGENT_DISPATCH: &str = r#"
fn bump(x :: integer), do: x + 2
fn bump(:timeout), do: panic(:timeout)

fn main() do
  me = self()
  send(me, 1)
  value = receive do
    x -> x
  after
    10 -> :timeout
  end
  dbg(bump(value))
end
"#;

fn jit_compile_native_program(
    compiler: &mut Compiler2<ConfiguredTelemetry>,
    program: &NativeProgram,
) -> crate::ir_codegen::CompiledModule {
    compiler
        .compile_native_program_jit_for_test(program)
        .expect("compiler2-owned native codegen should compile a Compiler2 native program")
}

fn assert_no_legacy_planner_or_type_infer(capture: &Capture, context: &str) {
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty() && capture.find(&["fz", "planner"]).is_empty(),
        "{context}",
    );
}

fn presence(fact: FactKey, changed: bool) -> (FactKey, bool) {
    (fact, changed)
}

fn settled_fact(fact: FactKey) -> FactUse<FactKey> {
    FactUse::settled(fact)
}

fn output_facts(effects: &JobEffects) -> OutputFacts {
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

fn demand_backend_product(compiler: &mut Compiler2<ConfiguredTelemetry>, root_id: crate::compiler2::RootId) {
    compiler
        .drive_root_to_dump_stage(root_id, super::dump::DumpStage::Backend)
        .expect("the requested backend product should settle");
}

fn drive_world_backend_product(
    world: &mut super::World,
    telemetry: &ConfiguredTelemetry,
    sessions: &mut super::pull::ProductSessions,
    root: super::RootId,
) {
    super::product_drive::drive_retained_product(
        world,
        telemetry,
        sessions,
        super::drive::ProductAddress {
            root,
            key: ProductKey::RootBackendProduct(root),
        },
    )
    .expect("the retained backend product should settle");
}

#[test]
fn compiler2_runtime_prelude_does_not_run_frontend_before_drive() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_eq!(
        capture.count(&["fz", "lexer", "pass"]),
        0,
        "Compiler2 construction and submission should not lex runtime or user source"
    );
    assert_eq!(
        capture.count(&["fz", "lexer", "tokens_built"]),
        0,
        "Compiler2 construction and submission should not build tokens"
    );
    assert_eq!(
        capture.count(&["fz", "parser", "pass"]),
        0,
        "Compiler2 construction and submission should not parse source"
    );
    assert_eq!(
        capture.count(&["fz", "parser", "items_built"]),
        0,
        "Compiler2 construction and submission should not build AST items"
    );
}

#[test]
fn compiler2_notes_top_level_types_into_the_global_scope() {
    let tel = ConfiguredTelemetry::new();
    let noted_types = NotedTypeCapture::new();
    noted_types.install(&tel);

    // Unique `tkf_` names so the assertions ignore the runtime prelude's own
    // @types, which are noted in the same drive when the user scope pulls it.
    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("types.fz".to_string()),
        text: include_str!("../../fixtures2/00002_types_top_level.fz").to_string(),
    });
    assert_resolved(compiler.drive(), "first drive should index the source");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "scoping the top-level code should be demandable",
    );
    assert_resolved(compiler.drive(), "second drive should scope and note the @types");

    let mine = noted_types
        .all()
        .into_iter()
        .filter(|record| record.name.name.starts_with("tkf_"))
        .collect::<Vec<_>>();
    assert_eq!(mine.len(), 2, "each top-level @type is noted exactly once");
    for record in &mine {
        assert_eq!(
            record.name.module,
            ModuleId::GLOBAL,
            "a top-level @type is noted under the GLOBAL module",
        );
        assert_ne!(
            record.namespace,
            Namespace::default(),
            "the captured namespace is the built scope, never the empty namespace",
        );
    }
    let mut by_name = mine
        .iter()
        .map(|record| (record.name.name.clone(), record.name.arity as u64))
        .collect::<Vec<_>>();
    by_name.sort();
    assert_eq!(
        by_name,
        vec![("tkf_alpha".to_string(), 0), ("tkf_beta".to_string(), 1)],
        "arity is part of the type identity: tkf_alpha/0 and tkf_beta/1",
    );
}

#[test]
fn compiler2_records_type_references_as_consumer_dependencies() {
    let tel = ConfiguredTelemetry::new();
    let references = TypeReferenceCapture::new();
    references.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("refs.fz".to_string()),
        text: include_str!("../../fixtures2/00003_type_refs.fz").to_string(),
    });
    assert_resolved(compiler.drive(), "first drive should index the source");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "scoping the top-level code should be demandable",
    );
    assert_resolved(compiler.drive(), "second drive should scope, note, and walk references");
    let uses_id = function_id(&functions, "tkf_uses", 2);
    assert!(
        compiler.demand(Job::DefineFunction(uses_id)),
        "function type refs should become observable when the function surface is actually demanded",
    );
    assert_resolved(
        compiler.drive(),
        "third drive should materialize the function and publish its type references",
    );

    let consumers_of = |ref_name: &str| references.consumers_of(ref_name);

    // tkf_target is named by the @spec of `tkf_uses` and — nested inside the
    // parametric application `tkf_box(tkf_target)` — by the wrapper type. The
    // walk recurses into type arguments, and the free type variable `a` in the
    // spec (and the formal `a` in `tkf_box`'s own body) is no reference at all.
    assert_eq!(
        consumers_of("tkf_target"),
        vec!["fn:tkf_uses".to_string(), "type:tkf_wrapper".to_string()],
        "tkf_target is a dep of the function and, recursed out of tkf_box(tkf_target), the wrapper",
    );
    // tkf_param is named only by `tkf_uses`'s inline parameter annotation — a
    // function type-position walked the same way as its @spec.
    assert_eq!(
        consumers_of("tkf_param"),
        vec!["fn:tkf_uses".to_string()],
        "tkf_param is a dep of the function via its inline parameter annotation",
    );
    // The parametric type tkf_box is itself referenced, at arity 1 — parameter
    // arity is part of the identity, so tkf_box and tkf_box/1 never conflate.
    // (Its own body `list(a)` references nothing: `list` is a builtin ctor and
    // `a` is a formal type variable.)
    assert_eq!(
        references.reference_count("tkf_box", 1),
        1,
        "the parametric type tkf_box is referenced exactly once"
    );
    assert_eq!(
        consumers_of("tkf_box"),
        vec!["type:tkf_wrapper".to_string()],
        "the parametric type is a dep of the wrapper that applies it",
    );
}

struct TypeReferenceCapture(Rc<RefCell<Vec<(String, u64, String)>>>);

impl TypeReferenceCapture {
    fn new() -> Self {
        Self(Rc::new(RefCell::new(Vec::new())))
    }
    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let records = Rc::clone(&self.0);
        telemetry.attach_raw_event2::<crate::compiler2::World, FunctionId, _>(
            &["fz", "compiler2", "type", "references", "function", "recorded"],
            move |_, _, _, world, function| {
                let name = world.function_ref(*function).name.clone();
                records.borrow_mut().extend(
                    world
                        .function_type_refs(*function)
                        .iter()
                        .map(|reference| (reference.name.clone(), reference.arity as u64, format!("fn:{name}"))),
                );
            },
        );
        let records = Rc::clone(&self.0);
        telemetry.attach_raw_event2::<crate::compiler2::World, TypeName, _>(
            &["fz", "compiler2", "type", "references", "type", "recorded"],
            move |_, _, _, world, name| {
                records
                    .borrow_mut()
                    .extend(world.type_def_refs(name).iter().map(|reference| {
                        (
                            reference.name.clone(),
                            reference.arity as u64,
                            format!("type:{}", name.name),
                        )
                    }));
            },
        );
    }
    fn consumers_of(&self, ref_name: &str) -> Vec<String> {
        let mut consumers = self
            .0
            .borrow()
            .iter()
            .filter(|(name, _, _)| name == ref_name)
            .map(|(_, _, consumer)| consumer.clone())
            .collect::<Vec<_>>();
        consumers.sort();
        consumers
    }
    fn reference_count(&self, ref_name: &str, arity: u64) -> usize {
        self.0
            .borrow()
            .iter()
            .filter(|(name, found_arity, _)| name == ref_name && *found_arity == arity)
            .count()
    }
}

struct RenderedTypeDef {
    name: String,
    arity: u64,
    changed: bool,
    rendered: String,
}

#[derive(Clone)]
struct NotedTypeRecord {
    name: TypeName,
    namespace: Namespace,
}

struct NotedTypeCapture(Rc<RefCell<Vec<NotedTypeRecord>>>);

impl NotedTypeCapture {
    fn new() -> Self {
        Self(Rc::new(RefCell::new(Vec::new())))
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let records = Rc::clone(&self.0);
        telemetry.attach_raw_event2::<crate::compiler2::World, TypeName, _>(
            &["fz", "compiler2", "type", "noted"],
            move |_, _, _, world, name| {
                let Some(decl) = world.type_decl(name) else {
                    return;
                };
                records.borrow_mut().push(NotedTypeRecord {
                    name: name.clone(),
                    namespace: decl.namespace,
                });
            },
        );
    }

    fn all(&self) -> Vec<NotedTypeRecord> {
        self.0.borrow().clone()
    }
}

fn rendered_type_defs(tel: &ConfiguredTelemetry) -> Rc<RefCell<Vec<RenderedTypeDef>>> {
    let rendered: Rc<RefCell<Vec<RenderedTypeDef>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&rendered);
    tel.attach_raw_event2::<crate::compiler2::World, TypeName, _>(
        &["fz", "compiler2", "type", "defined"],
        move |_, _, _, world, name| {
            let Some(def) = world.type_def(name) else {
                return;
            };
            sink.borrow_mut().push(RenderedTypeDef {
                name: name.name.clone(),
                arity: name.arity as u64,
                changed: true,
                rendered: world.types().display(&def.ty),
            });
        },
    );
    rendered
}

#[test]
fn compiler2_derive_type_def_pulls_a_referenced_type_and_its_wait_set_leaving_others_cold() {
    let tel = ConfiguredTelemetry::new();
    let rendered = rendered_type_defs(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("typedefs.fz".to_string()),
        text: include_str!("../../fixtures2/00004_typedefs.fz").to_string(),
    });
    assert_resolved(compiler.drive(), "first drive should index the source");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "scoping the top-level code should be demandable"
    );
    assert_resolved(compiler.drive(), "second drive should scope, note, and walk references");

    let define_count = |name: &str| {
        rendered
            .borrow()
            .iter()
            .filter(|definition| definition.name == name)
            .count()
    };

    // DeriveTypeDef is strictly pulled: scoping notes and references the types
    // but resolves none of them.
    assert_eq!(
        define_count("tkf_int"),
        0,
        "a noted @type is not resolved until a consumer pulls it"
    );
    assert_eq!(
        define_count("tkf_wrapper"),
        0,
        "a noted @type is not resolved until a consumer pulls it"
    );

    // Pull the wrapper. Its body names tkf_box(tkf_int); the wait-set drags both
    // dependencies through. tkf_cold — reached by no one — stays cold.
    let wrapper = TypeName {
        module: ModuleId::GLOBAL,
        name: "tkf_wrapper".to_string(),
        arity: 0,
    };
    assert!(
        compiler.demand(Job::DeriveTypeDef(wrapper)),
        "deriving a type should be demandable"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should resolve the wrapper and its wait-set",
    );

    let resolved_ty = |name: &str| {
        rendered
            .borrow()
            .iter()
            .rev()
            .find(|def| def.name == name)
            .map(|def| def.rendered.clone())
    };

    // Render the expected types through the same renderer (a scratch interner),
    // so the assertion captures structural identity rather than a brittle format.
    let mut expect = Types::new();
    let int = expect.int();
    let list_int = expect.list(int);
    let var0 = expect.type_var(TypeVarId(0));
    let list_var = expect.list(var0);

    assert_eq!(
        resolved_ty("tkf_int").as_deref(),
        Some(expect.display(&int).as_str()),
        "a scalar @type resolves to the builtin it names",
    );
    assert_eq!(
        resolved_ty("tkf_box").as_deref(),
        Some(expect.display(&list_var).as_str()),
        "a parametric @type resolves to a template over its formal parameter",
    );
    assert_eq!(
        resolved_ty("tkf_wrapper").as_deref(),
        Some(expect.display(&list_int).as_str()),
        "applying tkf_box(tkf_int) instantiates the template to a list of integer",
    );

    assert_eq!(define_count("tkf_int"), 1, "each reached type resolves exactly once");
    assert_eq!(define_count("tkf_box"), 1, "each reached type resolves exactly once");
    assert_eq!(
        define_count("tkf_wrapper"),
        1,
        "each reached type resolves exactly once"
    );
    assert_eq!(
        define_count("tkf_cold"),
        0,
        "a type no reached consumer references stays cold"
    );
}

#[test]
fn compiler2_derive_type_def_mints_a_refines_brand_inner_in_symbol() {
    let tel = ConfiguredTelemetry::new();
    let rendered = rendered_type_defs(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("brand.fz".to_string()),
        text: include_str!("../../fixtures2/00005_brand.fz").to_string(),
    });
    assert_resolved(compiler.drive(), "first drive should index the source");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "scoping the top-level code should be demandable"
    );
    assert_resolved(compiler.drive(), "second drive should scope and note the brand");

    let pos = TypeName {
        module: ModuleId::GLOBAL,
        name: "tkf_pos".to_string(),
        arity: 0,
    };
    assert!(
        compiler.demand(Job::DeriveTypeDef(pos)),
        "deriving the brand should be demandable"
    );
    assert_resolved(compiler.drive(), "third drive should resolve the brand");

    let resolved = rendered
        .borrow()
        .iter()
        .filter(|def| def.name == "tkf_pos")
        .map(|def| def.rendered.clone())
        .collect::<Vec<_>>();
    assert_eq!(resolved.len(), 1, "the brand resolves exactly once");

    // A `refines T` brand is its inner T tagged in-symbol with the brand name —
    // the integer structure branded `tkf_pos`, distinct from a bare integer and
    // never a fresh opaque.
    let mut expect = Types::new();
    let int = expect.int();
    let branded = expect.mint_brand(int, "tkf_pos");
    assert_eq!(
        resolved[0],
        expect.display(&branded),
        "refines integer resolves to integer branded `tkf_pos`, minted inner-in-symbol",
    );
    assert_ne!(
        resolved[0],
        expect.display(&int),
        "the brand is observably distinct from its bare inner type",
    );
}

#[test]
fn compiler2_defimpl_callback_owner_remote_call_does_not_self_wait() {
    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new();
    let mut sessions = super::pull::ProductSessions::default();
    let code_id = world.submit_code(
        Some("defimpl_owner_remote_call.fz".to_string()),
        concat!(
            "defprotocol Proof do\n",
            "  @spec pick(t(a), a) :: a\n",
            "  fn pick(value, fallback)\n",
            "end\n",
            "\n",
            "defmodule Box do\n",
            "  fn pick(value, _fallback), do: value\n",
            "  defimpl Proof, for: List do\n",
            "    fn pick(value, fallback), do: Box.pick(value, fallback)\n",
            "  end\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "source should index protocol and owner modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "top-level scope should prepare module definitions",
    );

    let protocol = world.reference_module("Proof");
    assert!(
        world.demand(Job::DefineModule(protocol)),
        "protocol definition should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "protocol definition should publish callback facts first",
    );

    let owner = world.reference_module("Box");
    assert!(
        world.demand(Job::DefineModule(owner)),
        "owner module definition should be demandable",
    );
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "owner-module remote calls inside defimpl callbacks should use the live source namespace, not wait on ModuleDefined(owner)",
    );
}

#[test]
fn compiler2_nested_defimpl_resolves_protocol_and_target_through_namespace() {
    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new();
    let mut sessions = super::pull::ProductSessions::default();
    let code_id = world.submit_code(
        Some("nested_protocol_impl_dispatch.fz".to_string()),
        include_str!("../../fixtures2/00272_protocol_impl_dispatch.fz").to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "first drive should index the nested protocol/provider module and the caller module",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "scoping the nested protocol fixture should be demandable",
    );
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "top-level scoping should bind nested definition macros before root demand",
    );

    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_world_backend_product(&mut world, &tel, &mut sessions, root);
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "main should settle when nested defimpl resolves against the declared protocol identity",
    );

    let protocol = world.reference_module("Contracts.Collectable");
    let list = world.reference_module("List");
    let contracts_list = world.reference_module("Contracts.List");
    let id_callback = world.reference_function(protocol, "id", 1);
    let dispatch = world
        .protocol_dispatch(protocol)
        .expect("the nested protocol should publish a dispatch fact under Contracts.Collectable");
    assert_eq!(
        dispatch.arms.len(),
        1,
        "one nested defimpl should contribute exactly one dispatch arm",
    );
    assert_eq!(
        dispatch.arms[0].target, list,
        "defimpl target resolution should go through the namespace and land on List, not Contracts.List",
    );
    assert_ne!(
        dispatch.arms[0].target, contracts_list,
        "nested defimpl target resolution must not invent a child module for bare runtime targets",
    );
    assert!(
        dispatch.arms[0].callbacks.contains_key(&id_callback),
        "the nested defimpl should register the declared protocol callback under the protocol's real dispatch fact",
    );
}

#[test]
fn compiler2_protocol_domain_marker_stays_type_owned_while_dispatch_revises_when_impls_land() {
    let tel = ConfiguredTelemetry::new();
    let noted_types = NotedTypeCapture::new();
    noted_types.install(&tel);
    let rendered_defs = rendered_type_defs(&tel);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("protocol_domain.fz".to_string()),
        include_str!("../../fixtures2/00006_protocol_domain.fz").to_string(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index the protocol and impl owner modules",
    );
    let indexed = outputs
        .take(Job::IndexCode(code_id))
        .expect("IndexCode job effects for the protocol-domain case");
    let module_ids = module_indexed_ids(&indexed);
    assert_eq!(
        module_ids.len(),
        2,
        "the source defines one protocol and one impl owner module"
    );
    let protocol = *module_ids
        .iter()
        .find(|module| world.module_name(**module) == Some("Proof"))
        .expect("indexed module id for the protocol");
    let owner = *module_ids
        .iter()
        .find(|module| world.module_name(**module) == Some("Box"))
        .expect("indexed module id for the impl owner");

    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "scoping the protocol source should be demandable",
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope the protocol source",
    );
    assert!(
        world.demand(Job::DefineModule(protocol)),
        "defining the protocol module should be demandable",
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "third drive should define the protocol callback surface",
    );
    let protocol_defined = outputs
        .take(Job::DefineModule(protocol))
        .expect("DefineModule job effects for the protocol surface");

    let noted = noted_types
        .all()
        .into_iter()
        .filter(|record| record.name.name == "t")
        .map(|record| record.name.arity as u64)
        .collect::<Vec<_>>();
    assert_eq!(noted, vec![0, 1], "protocol modules should synthesize both t/0 and t/1");

    let t0 = TypeName {
        module: protocol,
        name: "t".to_string(),
        arity: 0,
    };
    let t1 = TypeName {
        module: protocol,
        name: "t".to_string(),
        arity: 1,
    };
    assert!(
        protocol_defined.contains(&presence(FactKey::ProtocolDispatch(protocol), true)),
        "defining the protocol should publish the initial dispatch fact",
    );
    assert!(
        !protocol_defined
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::TypeDefined(name) if name == &t0 || name == &t1)),
        "protocol definition should note t/0 and t/1 but leave TypeDefined facts to DeriveTypeDef",
    );
    assert_eq!(
        world.fact_revision(&FactKey::TypeDefined(t0.clone())),
        None,
        "t/0 should stay unresolved until a type consumer demands it",
    );
    assert_eq!(
        world.fact_revision(&FactKey::TypeDefined(t1.clone())),
        None,
        "t/1 should stay unresolved until a type consumer demands it",
    );

    assert!(
        world.demand(Job::DeriveTypeDef(t0.clone())),
        "t/0 derivation should be demandable"
    );
    assert!(
        world.demand(Job::DeriveTypeDef(t1.clone())),
        "t/1 derivation should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "demanded protocol-domain types should resolve through the normal DeriveTypeDef path",
    );
    let t0_derived = outputs
        .take(Job::DeriveTypeDef(t0.clone()))
        .expect("DeriveTypeDef job effects for protocol t/0");
    let t1_derived = outputs
        .take(Job::DeriveTypeDef(t1.clone()))
        .expect("DeriveTypeDef job effects for protocol t/1");
    assert_eq!(
        t0_derived,
        vec![presence(FactKey::TypeDefined(t0.clone()), true)],
        "t/0 should publish exactly one marker type fact",
    );
    assert_eq!(
        t1_derived,
        vec![presence(FactKey::TypeDefined(t1.clone()), true)],
        "t/1 should publish exactly one marker type fact",
    );

    let mut type_events = rendered_defs
        .borrow()
        .iter()
        .filter(|def| def.name == "t")
        .map(|def| (def.arity, def.changed, def.rendered.clone()))
        .collect::<Vec<_>>();
    type_events.sort();
    let t0_def = world
        .type_def(&t0)
        .cloned()
        .expect("the demanded monomorphic protocol-domain type should be stored");
    let t1_def = world
        .type_def(&t1)
        .cloned()
        .expect("the demanded parametric protocol-domain type should be stored");
    assert_eq!(
        type_events.len(),
        2,
        "only the demanded protocol-domain type derivations should publish type-defined events"
    );

    let mut expect = Types::new();
    let marker = expect.opaque_of(&crate::compiler2::protocol::protocol_domain_tag(
        crate::modules::identity::ModuleName::parse_dotted("Proof").expect("protocol name should parse"),
    ));
    let rendered = expect.display(&marker);
    assert_eq!(type_events[0].0, 0);
    assert!(type_events[0].1);
    assert_eq!(type_events[0].2, *rendered);
    assert_eq!(type_events[1].0, 1);
    assert!(type_events[1].1);
    assert_eq!(type_events[1].2, *rendered);
    assert_eq!(t0_def.params, Vec::new(), "t/0 should remain monomorphic");
    assert_eq!(
        t1_def.params,
        vec![TypeVarId(0)],
        "t/1 should remain a parametric type definition",
    );
    let world_marker = world
        .types_mut()
        .opaque_of(&crate::compiler2::protocol::protocol_domain_tag(
            crate::modules::identity::ModuleName::parse_dotted("Proof").expect("protocol name should parse"),
        ));
    assert_eq!(t0_def.ty, world_marker, "t/0 should resolve to the marker opaque");
    assert_eq!(
        t1_def.ty, world_marker,
        "t/1 should resolve to the same interned marker opaque"
    );
    assert_eq!(
        t0_def.ty, t1_def.ty,
        "protocol t/0 and t/1 should literally name the same interned marker type",
    );

    // fz-hwn.19.2.4.16.1: the `defimpl Proof, for: List` nested in `Box` is
    // hoisted to its own module `Proof.List`. The impl lands — and revises the
    // dispatch — when *that* module is defined, never its lexical host `Box`.
    let impl_module = world.reference_module("Proof.List".to_string());
    assert!(
        world.demand(Job::DefineModule(impl_module)),
        "defining the hoisted impl module `Proof.List` should be demandable",
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "defining the impl module should revise the protocol facts",
    );
    let impl_defined = outputs
        .take(Job::DefineModule(impl_module))
        .expect("DefineModule job effects for the hoisted impl module");
    assert!(
        impl_defined.contains(&presence(FactKey::ProtocolDispatch(protocol), true)),
        "an impl landing should revise the dispatch fact",
    );
    assert!(
        !impl_defined
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::TypeDefined(name) if name == &t0 || name == &t1)),
        "an impl landing should not revise protocol-domain type facts",
    );
    assert!(
        !world.has_fact(&FactKey::ModuleDefined(owner)),
        "the impl lands without defining its lexical host `Box`",
    );
    assert_eq!(
        world.fact_revision(&FactKey::TypeDefined(t0.clone())),
        Some(1),
        "t/0 should keep its original type fact revision after the impl lands",
    );
    assert_eq!(
        world.fact_revision(&FactKey::TypeDefined(t1.clone())),
        Some(1),
        "t/1 should keep its original type fact revision after the impl lands",
    );
    let stable_t0 = world
        .type_def(&t0)
        .cloned()
        .expect("the monomorphic protocol-domain type should stay stored after the impl lands");
    let stable_t1 = world
        .type_def(&t1)
        .cloned()
        .expect("the parametric protocol-domain type should stay stored after the impl lands");
    assert_eq!(
        stable_t0, t0_def,
        "the impl set should not mutate the stored t/0 definition",
    );
    assert_eq!(
        stable_t1, t1_def,
        "the impl set should not mutate the stored t/1 definition",
    );

    let pick_callback = world.reference_function(protocol, "pick", 2);
    let dispatch = world
        .protocol_dispatch(protocol)
        .expect("the revised protocol dispatch fact should be stored");
    assert_eq!(dispatch.arms.len(), 1, "one defimpl should produce one dispatch arm");
    assert!(
        world
            .module_name(dispatch.arms[0].target)
            .is_some_and(|name| name.ends_with("List")),
        "the dispatch arm should target the List receiver domain",
    );
    assert!(
        dispatch.arms[0].callbacks.contains_key(&pick_callback),
        "the dispatch arm should route the declared callback identity",
    );
}

#[test]
fn compiler2_struct_defined_publishes_independently_of_module_defined() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    // Observe the published `StructDef` through the callee-tier signal the
    // store emits — the same object slice .10 will read back — so the test
    // pins the store's *content*, not just that the fact fires.
    let published_fields: PublishedStructFields = Rc::new(RefCell::new(Vec::new()));
    let fields_sink = Rc::clone(&published_fields);
    tel.attach_raw_event2::<crate::compiler2::World, ModuleId, _>(
        &["fz", "compiler2", "struct_def", "defined"],
        move |_, _, _, world, module_id| {
            let Some(def) = world.struct_def(*module_id) else {
                return;
            };
            fields_sink.borrow_mut().push((module_id.as_u32(), def.fields.clone()));
        },
    );
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_defined_independence.fz".to_string()),
        concat!(
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
            "\n",
            "defmodule Helper do\n",
            "  fn id(x), do: x\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let point = world.reference_module("Point");
    let helper = world.reference_module("Helper");

    assert!(
        world.demand(Job::DefineModule(point)),
        "Point definition should be demandable"
    );
    assert!(
        world.demand(Job::DefineModule(helper)),
        "Helper definition should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "third drive should define both modules",
    );

    let point_defined = outputs
        .take(Job::DefineModule(point))
        .expect("DefineModule job effects for Point");
    let helper_defined = outputs
        .take(Job::DefineModule(helper))
        .expect("DefineModule job effects for Helper");

    // A `defstruct`-carrying module body still publishes `ModuleDefined` as
    // usual, but also publishes `StructDefined` as its own distinct fact —
    // not folded into, or standing in for, `ModuleDefined`.
    assert!(
        point_defined.contains(&presence(FactKey::ModuleDefined(point), true)),
        "Point's defstruct-carrying body should still publish ModuleDefined"
    );
    assert!(
        point_defined.contains(&presence(FactKey::StructDefined(point), true)),
        "a module body containing defstruct settling should publish its own StructDefined fact"
    );

    // A module with no `defstruct` publishes `ModuleDefined` but never
    // `StructDefined` — proof that `StructDefined` is not an overbroad proxy
    // riding every module settle.
    assert!(
        helper_defined.contains(&presence(FactKey::ModuleDefined(helper), true)),
        "Helper's defstruct-free body should still publish ModuleDefined"
    );
    assert!(
        !helper_defined
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::StructDefined(_))),
        "StructDefined must not fire for a module that never declares defstruct"
    );

    assert!(
        world.has_fact(&FactKey::StructDefined(point)),
        "StructDefined(Point) should be independently observable as settled"
    );
    assert!(
        !world.has_fact(&FactKey::StructDefined(helper)),
        "StructDefined(Helper) should never be recorded — Helper never declares defstruct"
    );

    // The StructDef store captures the defstruct's field names in source
    // order — the exact ordered schema slices .10-.13 build layout on. Only
    // Point's struct-bearing body publishes a def; Helper's never does.
    assert_eq!(
        *published_fields.borrow(),
        vec![(point.as_u32(), vec!["x".to_string(), "y".to_string()])],
        "the store should hold Point's `defstruct [:x, :y]` fields in source order, and nothing for Helper"
    );
}

#[test]
fn compiler2_struct_duplicate_defstruct_diagnoses_instead_of_silently_picking_one() {
    // fz's grammar is one `defstruct` per module (Elixir parity). A second
    // `defstruct` in the same module body must not be silently resolved by
    // either "first wins" or "last wins" -- it is a genuine user error and
    // must diagnose at the SECOND defstruct's span.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_duplicate_defstruct.fz".to_string()),
        concat!(
            "defmodule Point do\n",
            "  defstruct [:a]\n",
            "  defstruct [:b]\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index the module",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope the module",
    );

    let point = world.reference_module("Point");
    assert!(
        world.demand(Job::DefineModule(point)),
        "Point definition should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Fatal { .. }
        ),
        "a module with two defstruct forms must diagnose rather than silently pick first-or-last"
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic for the duplicate defstruct");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_DUPLICATE_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `Point` already defines a struct"
    );

    // The first defstruct's fields are what the store keeps -- the guard
    // rejects the second form outright rather than letting it overwrite.
    assert_eq!(
        world.struct_def_fields(point),
        Some(["a".to_string()].as_slice()),
        "the store should retain the FIRST defstruct's fields; the duplicate must not overwrite it"
    );
}

#[test]
fn compiler2_struct_macro_emitted_duplicate_defstruct_diagnoses_even_with_identical_fields() {
    // fz macros ARE able to emit a top-level `defstruct`: an item macro can
    // return a bare `{:defstruct, meta, [fields]}` tuple (the same
    // compiler-shaped AST literal fixtures2/00124 uses for `{:fn, ...}`),
    // and `quoted_surface::build_form` recognizes the `:defstruct` head the
    // same way it would from source. When that macro's body writes the
    // fields as a literal (no `__fz_span__` key in its `meta` map), every
    // expansion gets `Span::DUMMY` (`quoted_surface::span_from_meta`'s
    // no-span fallback) -- so invoking the SAME macro twice in one module
    // produces two `StructDef`s that are not just same-span but
    // byte-IDENTICAL whenever the macro's argument repeats. Before this
    // guard, `publish_struct_def`'s content-comparison gate (fz-rh2.17.5.6.8.1)
    // treated that as indistinguishable from an idempotent job re-run and
    // silently kept the first -- a genuine duplicate-defstruct module going
    // undiagnosed. The occurrence check now catches it regardless of
    // content.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_macro_emitted_duplicate_defstruct.fz".to_string()),
        concat!(
            "defmacro make_struct(fields) do\n",
            "  {:defstruct, %{}, [fields]}\n",
            "end\n",
            "\n",
            "defmodule Point do\n",
            "  make_struct([:a, :b])\n",
            "  make_struct([:a, :b])\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index the module",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope the module",
    );

    let point = world.reference_module("Point");
    assert!(
        world.demand(Job::DefineModule(point)),
        "Point definition should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Fatal { .. }
        ),
        "two macro-emitted defstruct forms with identical fields must still diagnose as a duplicate, \
         not be silently treated as an idempotent re-run"
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic for the macro-emitted duplicate defstruct");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_DUPLICATE_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `Point` already defines a struct"
    );

    // The FIRST macro-emitted defstruct's fields are what the store keeps,
    // matching the literal-duplicate keep-first behavior above.
    assert_eq!(
        world.struct_def_fields(point),
        Some(["a".to_string(), "b".to_string()].as_slice()),
        "the store should retain the first macro-emitted defstruct's fields"
    );
}

// fz-go4.53's adversarial audit found `demand_function_scope`'s global-module
// branch (`World::demand_function_scope`) scans every submitted code for a
// `Certain` surface match and, via `certain_home.get_or_insert`, keeps only
// the FIRST code whose surface names the wanted top-level name+arity. Before
// .53 that scan raced (whichever `ScopeCode` job ran last won the single-slot
// pending-source stash); .53 made the choice deterministic (submission-order
// first-wins) but never added a diagnostic for the case that choice is
// papering over: two SEPARATE source files (codes) both defining the same
// top-level `name/arity` for real. Elixir raises `CompileError` ("... is
// already defined") on exactly this shape, so fz must diagnose it too instead
// of silently keeping one definition and dropping the other with no signal.
// This mirrors `compiler2_struct_duplicate_defstruct_diagnoses_instead_of_silently_picking_one`
// above: same-shaped bug (silent first/last-wins on a genuine duplicate
// definition), same fix shape (diagnose at the second occurrence instead of
// resolving).
#[test]
fn compiler2_duplicate_global_function_definition_diagnoses_instead_of_silently_picking_one() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("foo_first.fz".to_string()),
        text: "fn foo(), do: 1\n".to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("foo_second.fz".to_string()),
        text: "fn foo(), do: 2\n".to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "foo".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "two separate codes defining the same top-level foo/0 must diagnose rather than silently \
         resolving to whichever code was submitted first"
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic for the duplicate global function definition");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_DUPLICATE_FUNCTION.0);
    assert_eq!(metadata_str(&diagnostic, "message"), "`foo/0` is already defined");
}

#[test]
fn compiler2_struct_type_expression_waits_for_struct_defined_and_resolves_precise_order() {
    // `Q`'s `@type t` names `Point` (in reversed field order) before `Point`
    // is even processed. This proves three things at once
    // (fz-rh2.17.5.6.10): the reference walk records the obligation and the
    // `StructDefined` wait regardless of processing order; `DeriveTypeDef`
    // actually waits rather than resolving early against an absent schema;
    // and once `Point` settles, the resolved type uses schema field order
    // (x, y) rather than the literal, reversed write order (y, x).
    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_type_expression_out_of_order.fz".to_string()),
        concat!(
            "defmodule Q do\n",
            "  @type t :: %Point{y: integer, x: integer}\n",
            "end\n",
            "\n",
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let q = world.reference_module("Q");
    let point = world.reference_module("Point");
    let t = TypeName {
        module: q,
        name: "t".to_string(),
        arity: 0,
    };

    // Q's own body settles before Point's defstruct does.
    assert!(world.demand(Job::DefineModule(q)), "Q definition should be demandable");
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "third drive should settle Q without Point existing yet",
    );

    assert!(
        !world.has_fact(&FactKey::StructDefined(point)),
        "Point's defstruct should not have published yet"
    );
    assert_eq!(
        world.type_def_struct_refs(&t),
        &[point],
        "Q's @type t body should have recorded Point as its StructDefined wait"
    );
    assert!(
        world.type_def(&t).is_none(),
        "t/0 should not resolve before Point's defstruct publishes"
    );

    // Pulling the type derivation alone, with Point's `defstruct` still
    // unpublished, must wait rather than fabricate a field order from the
    // reversed literal write order -- the pull architecture demands Point's
    // own `DefineModule` as `StructDefined`'s producer to unblock it.
    assert!(
        world.demand(Job::DeriveTypeDef(t.clone())),
        "t/0 derivation should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "pulling t/0 should transitively pull Point's defstruct and resolve",
    );

    let def = world
        .type_def(&t)
        .cloned()
        .expect("t/0 should resolve once Point's defstruct publishes");
    let int_ty = world.types_mut().int();
    let expected = world.struct_value_ty(point, &["x".to_string(), "y".to_string()], &[int_ty, int_ty]);
    assert_eq!(
        def.ty, expected,
        "resolved struct-record type should use Point's schema order (x, y), not the reversed literal order (y, x)"
    );
}

#[test]
fn compiler2_struct_type_expression_diagnoses_unknown_field_instead_of_dropping_it() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_type_expression_unknown_field.fz".to_string()),
        concat!(
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
            "\n",
            "defmodule Q do\n",
            "  @type t :: %Point{x: integer, bogus: integer}\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let point = world.reference_module("Point");
    assert!(
        world.demand(Job::DefineModule(point)),
        "Point definition should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "third drive should define Point's defstruct",
    );

    let q = world.reference_module("Q");
    assert!(world.demand(Job::DefineModule(q)), "Q definition should be demandable");
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Fatal { .. }
        ),
        "an unknown struct field named in a type expression should diagnose rather than silently resolve",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic for the unknown struct field");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_UNKNOWN_STRUCT_FIELD.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "struct `Point` has no field `bogus`"
    );
}

#[test]
fn compiler2_struct_type_expression_out_of_order_unknown_field_diagnoses_when_struct_settles() {
    // Q references %Point{bogus: ...} before Point is even processed. The
    // obligation is recorded against Point regardless -- diagnosing it must
    // wait until Point's own `defstruct` settles (there is nothing to
    // validate against yet), and it must not be lost in the meantime.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_type_expression_out_of_order_unknown_field.fz".to_string()),
        concat!(
            "defmodule Q do\n",
            "  @type t :: %Point{bogus: integer}\n",
            "end\n",
            "\n",
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let q = world.reference_module("Q");
    assert!(world.demand(Job::DefineModule(q)), "Q definition should be demandable");
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "Q settling before Point exists should not itself fail -- there is nothing to validate yet",
    );
    assert!(
        capture.find(&["fz", "diag", "error"]).is_empty(),
        "no diagnostic should fire before Point settles"
    );

    let point = world.reference_module("Point");
    assert!(
        world.demand(Job::DefineModule(point)),
        "Point definition should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Fatal { .. }
        ),
        "Point settling should validate Q's outstanding obligation and diagnose the unknown field",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic once Point settles");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_UNKNOWN_STRUCT_FIELD.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "struct `Point` has no field `bogus`"
    );
}

#[test]
fn compiler2_struct_spec_type_diagnoses_unknown_field_instead_of_dropping_it() {
    // The `@spec` consumer reaches the SAME shared `TypeExpr::StructRecord`
    // arm as `@type`, but through `derive_function_contract`
    // (`resolve_spec_decl`) rather than `derive_type_def`. Before this slice
    // wired the function type-position walk, that arm silently dropped an
    // unknown field for `@spec`/guard (the schema-order read never re-included
    // it) and resolved -- worse than the old scan, which was available
    // earlier. This proves the obligation is now recorded for the function's
    // type positions too, so an unknown field is diagnosed at the spec's span,
    // not dropped. Non-vacuous: on the pre-fix code this drive Resolved.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("struct_spec_unknown_field.fz".to_string()),
        text: concat!(
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
            "\n",
            "defmodule M do\n",
            "  @spec run(%Point{bogus: integer}) :: integer\n",
            "  fn run(p), do: 0\n",
            "end\n",
        )
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "an unknown struct field named in an @spec should diagnose rather than silently drop",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic for the unknown @spec struct field");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_UNKNOWN_STRUCT_FIELD.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "struct `Point` has no field `bogus`"
    );
}

#[test]
fn compiler2_struct_spec_type_diagnoses_reference_to_non_struct_module() {
    // `%NotAStruct{...}` where NotAStruct is a real module that never declares
    // a defstruct: DefineModule(NotAStruct) settles ModuleDefined but never
    // StructDefined, so the contract's StructDefined wait survives to the
    // terminal frontier. Without the unresolved_issue arm this produced ZERO
    // diagnostics -- a silent stall (Unresolved with nothing to show). It must
    // terminate with a clear not-a-struct error at the referencing span. This
    // is the correct behaviour for `%NonStruct{}`: real structs still wait for
    // precise order; a non-struct now diagnoses instead of stalling silently.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("struct_spec_non_struct.fz".to_string()),
        text: concat!(
            "defmodule NotAStruct do\n",
            "  fn hello(), do: 0\n",
            "end\n",
            "\n",
            "defmodule M do\n",
            "  @spec run(%NotAStruct{x: integer}) :: integer\n",
            "  fn run(p), do: 0\n",
            "end\n",
        )
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Unresolved { .. }),
        "an @spec naming a non-struct module should terminate with a diagnostic, not silently stall",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a not-a-struct diagnostic rather than a silent stall");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_NOT_A_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `NotAStruct` is not a struct"
    );
}

#[test]
fn compiler2_zero_field_struct_spec_type_diagnoses_non_struct_module_at_reference_span() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    let source = concat!(
        "defmodule NotAStruct do\n",
        "  fn hello(), do: 0\n",
        "end\n",
        "\n",
        "defmodule M do\n",
        "  @spec run(%NotAStruct{}) :: integer\n",
        "  fn run(p), do: 0\n",
        "end\n",
    )
    .to_string();
    compiler.submit_code(CodeSubmission {
        name: Some("zero_field_struct_spec_non_struct.fz".to_string()),
        text: source.clone(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Unresolved { .. }),
        "a zero-field struct type naming a non-struct module should diagnose instead of reporting a generated span",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a not-a-struct diagnostic for the zero-field @spec struct type");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_NOT_A_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `NotAStruct` is not a struct"
    );
    let diagnostic = diagnostic
        .diagnostic
        .as_ref()
        .expect("expected the not-a-struct diagnostic payload to be captured");
    assert_primary_span_contains(diagnostic, &source, "%NotAStruct{}");
}

#[test]
fn compiler2_struct_param_annotation_diagnoses_unknown_field_instead_of_dropping_it() {
    // The guard/entry-dispatch consumer reaches the shared StructRecord arm
    // through `plan_entry_dispatch` (`resolve_type_expr_body`) when a param
    // carries a `%Mod{...}` annotation. Proves the param-annotation walk in
    // record_function_type_refs records the obligation so an unknown field is
    // diagnosed at the annotation's span, not silently dropped -- the guard
    // sibling of the @spec test.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("struct_param_annotation_unknown_field.fz".to_string()),
        text: concat!(
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
            "\n",
            "defmodule M do\n",
            "  fn run(p :: %Point{bogus: integer}), do: 0\n",
            "end\n",
        )
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "an unknown struct field in a param annotation should diagnose rather than silently drop",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic for the unknown param-annotation struct field");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_UNKNOWN_STRUCT_FIELD.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "struct `Point` has no field `bogus`"
    );
}

#[test]
fn compiler2_extern_struct_param_waits_on_struct_defined_not_literal_order() {
    // The extern-contract path resolves its `%Mod{...}` param through the same
    // shared arm via `resolve_extern_signature`/`resolve_spec_decl` inside
    // `lower_function`. Demanding LowerFunction ALONE (which never pulls the
    // contract job) isolates lower_function's own wait-set: with the
    // StructDefined wait, a `%NotAStruct{...}` extern param cannot resolve to a
    // literal-order type -- it waits, the wait never settles (NotAStruct has no
    // defstruct), and the drive terminates with the not-a-struct diagnostic.
    // Non-vacuous for lower_function's wait: without it, lower_function would
    // resolve the extern signature immediately in literal order and the drive
    // would Resolve with no diagnostic.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("extern_struct_param.fz".to_string()),
        concat!(
            "extern \"C\" fn takes(p :: %NotAStruct{x: integer}) :: integer\n",
            "\n",
            "defmodule NotAStruct do\n",
            "  fn hello(), do: 0\n",
            "end\n",
        )
        .to_string(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index the code",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope the code, indexing NotAStruct's body",
    );

    let takes = world.reference_function(ModuleId::GLOBAL, "takes", 1);
    assert!(
        world.demand(Job::LowerFunction(takes)),
        "lowering the extern function should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Unresolved { .. }
        ),
        "lowering an extern whose struct param names a non-struct should terminate, not resolve in literal order",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a not-a-struct diagnostic from the extern lowering wait");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_NOT_A_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `NotAStruct` is not a struct"
    );
}

#[test]
fn compiler2_struct_literal_and_pattern_lowering_wait_out_of_order_then_use_schema_field_order() {
    // The body-lowering sibling of `compiler2_struct_type_expression_waits_for_struct_defined_and_resolves_precise_order`:
    // `B.convert/1`'s struct *pattern* param and struct
    // *literal* return both name `Point` in reversed (y, x) write order.
    // Demanding LowerFunction alone -- without ever separately demanding
    // Point's DefineModule -- proves the pull architecture itself demands
    // Point's DefineModule as `StructDefined`'s producer to unblock the
    // wait, exactly like the `@type t` test: it must not fabricate an order
    // from the literal/pattern's own field list while Point is unprocessed,
    // and it must not fatally diagnose on the way. Once the drive resolves,
    // both the pattern's FieldAccess destructuring and the literal's
    // MakeStruct must use Point's schema order (x, y), not the source's
    // reversed order -- proving the lowering consumes `StructDefined`, not a
    // `ModuleDefined`/source scan.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_literal_pattern_out_of_order.fz".to_string()),
        concat!(
            "defmodule B do\n",
            "  fn convert(%Point{y: y, x: x}), do: %Point{y: y, x: x}\n",
            "end\n",
            "\n",
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
        )
        .to_string(),
    );

    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let b = world.reference_module("B");
    let point = world.reference_module("Point");
    let convert = world.reference_function(b, "convert", 1);

    assert!(
        !world.has_fact(&FactKey::StructDefined(point)),
        "Point's defstruct should not have published yet"
    );
    assert!(
        world.demand(Job::LowerFunction(convert)),
        "lowering convert/1 should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "pulling convert/1's lowering should transitively pull Point's defstruct and resolve",
    );
    assert!(
        capture.find(&["fz", "diag", "error"]).is_empty(),
        "an out-of-order struct reference that resolves cleanly must not have diagnosed along the way"
    );

    let body = lowered_body(&bodies, convert);
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        panic!("convert/1 should lower as clauses");
    };

    let field_access_order = clauses[0]
        .projections
        .iter()
        .filter_map(|step| match step {
            LoweredStep::FieldAccess { field, .. } => Some(field.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        field_access_order,
        vec!["x".to_string(), "y".to_string()],
        "the struct pattern should destructure fields in Point's schema order (x, y), not the pattern's own reversed write order (y, x)"
    );

    let struct_fields = entries
        .iter()
        .flat_map(|entry| entry.steps.iter())
        .find_map(|step| match step {
            LoweredStep::Struct { module, fields, .. } if *module == point => {
                Some(fields.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>())
            }
            _ => None,
        })
        .expect("convert/1 should lower a MakeStruct step for %Point{}");
    assert_eq!(
        struct_fields,
        vec!["x".to_string(), "y".to_string()],
        "MakeStruct should use Point's schema field order (x, y), not the literal's reversed write order (y, x)"
    );
}

#[test]
fn compiler2_struct_literal_unknown_field_diagnoses_at_settle_not_synchronously() {
    // The struct-literal sibling of `compiler2_struct_param_annotation_diagnoses_unknown_field_instead_of_dropping_it`:
    // `bogus` is not one of `Point`'s declared fields.
    // Lowering `make/0`'s literal never synchronously fails with the old
    // `LOWER_UNSUPPORTED` "does not define field" check -- the obligation is
    // recorded during the pre-pass and validated once `Point`'s defstruct
    // settles, so the diagnostic that surfaces is the durable
    // `RESOLVE_UNKNOWN_STRUCT_FIELD` from the obligation store, at the
    // literal's own span, not a local synchronous check in `lower_struct_expr`.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_literal_unknown_field.fz".to_string()),
        concat!(
            "defmodule B do\n",
            "  fn make(), do: %Point{x: 1, bogus: 2}\n",
            "end\n",
            "\n",
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
        )
        .to_string(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let b = world.reference_module("B");
    let make = world.reference_function(b, "make", 0);

    assert!(
        world.demand(Job::LowerFunction(make)),
        "lowering make/0 should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Fatal { .. }
        ),
        "an unknown field on a struct literal should diagnose once Point settles, not resolve cleanly",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected an unknown-struct-field diagnostic once Point settles");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::RESOLVE_UNKNOWN_STRUCT_FIELD.0,
        "the unknown field must be diagnosed through the durable obligation store, not the killed synchronous LOWER_UNSUPPORTED path"
    );
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "struct `Point` has no field `bogus`"
    );
}

#[test]
fn compiler2_struct_pattern_unknown_field_diagnoses_at_settle_not_synchronously() {
    // The struct-pattern sibling of the literal test above: an unknown field
    // named in a struct *pattern* is diagnosed through the same durable
    // obligation store once `Point` settles, not by a local synchronous
    // check in `lower_struct_pattern`.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_pattern_unknown_field.fz".to_string()),
        concat!(
            "defmodule B do\n",
            "  fn take(%Point{x: x, bogus: b}), do: {x, b}\n",
            "end\n",
            "\n",
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "end\n",
        )
        .to_string(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let b = world.reference_module("B");
    let take = world.reference_function(b, "take", 1);

    assert!(
        world.demand(Job::LowerFunction(take)),
        "lowering take/1 should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Fatal { .. }
        ),
        "an unknown field on a struct pattern should diagnose once Point settles, not resolve cleanly",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected an unknown-struct-field diagnostic once Point settles");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::RESOLVE_UNKNOWN_STRUCT_FIELD.0,
        "the unknown field must be diagnosed through the durable obligation store, not the killed synchronous LOWER_UNSUPPORTED path"
    );
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "struct `Point` has no field `bogus`"
    );
}

#[test]
fn compiler2_struct_literal_lowering_diagnoses_reference_to_non_struct_module() {
    // The struct-literal-in-body sibling of `compiler2_extern_struct_param_waits_on_struct_defined_not_literal_order`:
    // `%NotAStruct{...}` waits on `StructDefined(NotAStruct)`;
    // the drive engine pulls `NotAStruct`'s own `DefineModule` as that fact's
    // producer; `NotAStruct`'s body settles `ModuleDefined` without ever
    // declaring `defstruct`; the wait survives to the terminal frontier and
    // the settled-absent diagnostic fires instead of silently stalling.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_literal_non_struct.fz".to_string()),
        concat!(
            "defmodule NotAStruct do\n",
            "  fn hello(), do: 0\n",
            "end\n",
            "\n",
            "defmodule B do\n",
            "  fn make(), do: %NotAStruct{x: 1}\n",
            "end\n",
        )
        .to_string(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let b = world.reference_module("B");
    let make = world.reference_function(b, "make", 0);
    assert!(
        world.demand(Job::LowerFunction(make)),
        "lowering make/0 should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Unresolved { .. }
        ),
        "lowering a struct literal naming a non-struct module should terminate, not resolve in literal order",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a not-a-struct diagnostic from the struct-literal lowering wait");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_NOT_A_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `NotAStruct` is not a struct"
    );
}

#[test]
fn compiler2_zero_field_struct_literal_lowering_diagnoses_non_struct_module_at_reference_span() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let source = concat!(
        "defmodule NotAStruct do\n",
        "  fn hello(), do: 0\n",
        "end\n",
        "\n",
        "defmodule B do\n",
        "  fn make(), do: %NotAStruct{}\n",
        "end\n",
    )
    .to_string();
    let code_id = world.submit_code(
        Some("zero_field_struct_literal_non_struct.fz".to_string()),
        source.clone(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let b = world.reference_module("B");
    let make = world.reference_function(b, "make", 0);
    assert!(
        world.demand(Job::LowerFunction(make)),
        "lowering make/0 should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Unresolved { .. }
        ),
        "lowering a zero-field struct literal naming a non-struct module should diagnose at the literal",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a not-a-struct diagnostic from the zero-field struct-literal lowering wait");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_NOT_A_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `NotAStruct` is not a struct"
    );
    let diagnostic = diagnostic
        .diagnostic
        .as_ref()
        .expect("expected the not-a-struct diagnostic payload to be captured");
    assert_primary_span_contains(diagnostic, &source, "%NotAStruct{}");
}

#[test]
fn compiler2_struct_pattern_lowering_diagnoses_reference_to_non_struct_module() {
    // The struct-*pattern* sibling of
    // `compiler2_struct_literal_lowering_diagnoses_reference_to_non_struct_module`:
    // a `%NotAStruct{...}` in a fn-clause param pattern, where NotAStruct is a
    // real module that never declares a defstruct, waits on
    // `StructDefined(NotAStruct)`; the drive pulls NotAStruct's own
    // `DefineModule` as that fact's producer; NotAStruct settles
    // `ModuleDefined` without ever declaring `defstruct`; the wait survives to
    // the terminal frontier and the settled-absent diagnostic fires. Both the
    // literal and pattern paths share `record_struct_reference` and the generic
    // `unresolved_struct_issue`, so they SHOULD behave identically -- this test
    // proves it (rather than assuming it), pinning the pattern path against a
    // silent divergence. Non-vacuous: the pattern-path wait is what turns this
    // from a silent terminal stall into a RESOLVE_NOT_A_STRUCT diagnostic; a
    // pattern lowering that skipped the obligation/wait would resolve or stall
    // with no diagnostic.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let code_id = world.submit_code(
        Some("struct_pattern_non_struct.fz".to_string()),
        concat!(
            "defmodule NotAStruct do\n",
            "  fn hello(), do: 0\n",
            "end\n",
            "\n",
            "defmodule B do\n",
            "  fn take(%NotAStruct{x: x}), do: x\n",
            "end\n",
        )
        .to_string(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let b = world.reference_module("B");
    let take = world.reference_function(b, "take", 1);
    assert!(
        world.demand(Job::LowerFunction(take)),
        "lowering take/1 should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Unresolved { .. }
        ),
        "lowering a struct pattern naming a non-struct module should terminate, not resolve in literal order",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a not-a-struct diagnostic from the struct-pattern lowering wait");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_NOT_A_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `NotAStruct` is not a struct"
    );
}

#[test]
fn compiler2_zero_field_struct_pattern_lowering_diagnoses_non_struct_module_at_reference_span() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = crate::compiler2::World::new();
    let source = concat!(
        "defmodule NotAStruct do\n",
        "  fn hello(), do: 0\n",
        "end\n",
        "\n",
        "defmodule B do\n",
        "  fn take(%NotAStruct{}), do: 0\n",
        "end\n",
    )
    .to_string();
    let code_id = world.submit_code(
        Some("zero_field_struct_pattern_non_struct.fz".to_string()),
        source.clone(),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive should index both modules",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "second drive should scope both modules",
    );

    let b = world.reference_module("B");
    let take = world.reference_function(b, "take", 1);
    assert!(
        world.demand(Job::LowerFunction(take)),
        "lowering take/1 should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Unresolved { .. }
        ),
        "lowering a zero-field struct pattern naming a non-struct module should diagnose at the pattern",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a not-a-struct diagnostic from the zero-field struct-pattern lowering wait");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_NOT_A_STRUCT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `NotAStruct` is not a struct"
    );
    let diagnostic = diagnostic
        .diagnostic
        .as_ref()
        .expect("expected the not-a-struct diagnostic payload to be captured");
    assert_primary_span_contains(diagnostic, &source, "%NotAStruct{}");
}

#[test]
fn compiler2_import_of_undefined_module_diagnoses_at_the_import_site() {
    // The module-reference sibling of the struct-pattern span tests above:
    // `import Missing` records a bare module-reference expectation
    // (`World::note_module_reference_expectation`) before `Missing` is known
    // to resolve; `Missing` never gets any source, so the drive's terminal
    // `ModuleIndexed(Missing)` wait survives to `unresolved_module_issue`,
    // which now reads that recorded expectation instead of emitting
    // `Span::DUMMY`.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    let source = concat!(
        "defmodule User do\n",
        "  import Missing\n",
        "  fn run(), do: nil\n",
        "end\n",
    )
    .to_string();
    compiler.submit_code(CodeSubmission {
        name: Some("import_undefined_module_span.fz".to_string()),
        text: source.clone(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Unresolved { .. }),
        "import of an undefined module should stay unresolved until the missing provider exists, got {outcome:?}",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected an unknown-module diagnostic for `import Missing`");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_UNKNOWN_MODULE.0);
    assert_eq!(metadata_str(&diagnostic, "message"), "module `Missing` is not defined");
    let diagnostic = diagnostic
        .diagnostic
        .as_ref()
        .expect("expected the unknown-module diagnostic payload to be captured");
    assert_primary_span_contains(diagnostic, &source, "import");
}

#[test]
fn compiler2_dotted_call_to_a_name_a_settled_module_does_not_export_diagnoses_at_the_call_site() {
    // The function-export sibling: `Math.subtract/2` is referenced only
    // *after* `Math`'s own interface has already settled (with just
    // `add/2`), so `validate_module_interface_expectations` -- which runs
    // once, inside Math's own interface-defining job -- never sees this
    // late obligation. It survives unvalidated to the terminal frontier,
    // exercising `unresolved_function_issue`'s `Export` fallback, which now
    // reads the `InterfaceExpectation` `resolve_runtime_function` recorded
    // for `subtract/2` instead of emitting `Span::DUMMY`.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);

    compiler.submit_code(CodeSubmission {
        name: Some("math_export_span_math.fz".to_string()),
        text: concat!("defmodule Math do\n", "  fn add(a, b), do: a + b\n", "end\n").to_string(),
    });
    assert_resolved(compiler.drive(), "Math should settle its own interface on its own");

    let source = concat!(
        "defmodule User do\n",
        "  alias Math\n",
        "  fn run(), do: Math.subtract(1, 2)\n",
        "end\n",
    )
    .to_string();
    compiler.submit_code(CodeSubmission {
        name: Some("math_export_span_user.fz".to_string()),
        text: source.clone(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Unresolved { .. }),
        "calling an export Math never defines should terminate unresolved, not resolve or panic, got {outcome:?}",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected an unknown-import diagnostic for Math.subtract");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::RESOLVE_UNKNOWN_IMPORT.0);
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `Math` does not export `subtract/2`"
    );
    let diagnostic = diagnostic
        .diagnostic
        .as_ref()
        .expect("expected the unknown-import diagnostic payload to be captured");
    assert_primary_span_contains(diagnostic, &source, "Math.subtract");
}

#[test]
fn compiler2_backend_struct_schemas_are_fed_from_struct_def_facts_not_a_source_scan() {
    // Two structs reached through different backend consumers prove the root
    // product packages exact `StructDefined` dependencies rather than a source
    // or World inventory:
    // `Point` is only ever dot-field-accessed (`Prim::StructField`'s named
    // lookup), and its schema field ORDER must match the `defstruct`
    // declaration (x, y), not construction-site literal order (the literal
    // below writes y before x); `Pair` is only ever pattern-destructured
    // (`Prim::TupleField`/`AssertStruct`'s schema-identity check), never
    // dot-accessed, proving the map serves both consumers.
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("struct_backend_schema_from_facts.fz".to_string()),
        text: concat!(
            "defmodule Point do\n",
            "  defstruct [:x, :y]\n",
            "\n",
            "  fn new(x, y), do: %Point{y: y, x: x}\n",
            "end\n",
            "\n",
            "defmodule Pair do\n",
            "  defstruct [:first, :second]\n",
            "end\n",
            "\n",
            "fn describe(%Pair{first: f, second: s}), do: f + s\n",
            "\n",
            "fn main() do\n",
            "  point = Point.new(3, 4)\n",
            "  dbg(point.x)\n",
            "  dbg(point.y)\n",
            "  dbg(describe(%Pair{first: 10, second: 20}))\n",
            "end\n",
        )
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "struct construction/field-access/pattern should settle",
    );

    let program = backend.last(root_id).program;
    assert_eq!(
        program.schema("Point").map(Vec::as_slice),
        Some(["x".to_string(), "y".to_string()].as_slice()),
        "Point's schema should be the declared defstruct order, not the literal's write order"
    );
    assert_eq!(
        program.schema("Pair").map(Vec::as_slice),
        Some(["first".to_string(), "second".to_string()].as_slice()),
        "Pair's schema should be present from the fact store even though it is only ever pattern-destructured"
    );
}

#[test]
fn compiler2_backend_keeps_a_struct_named_only_by_a_retained_type_predicate() {
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    backend.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("struct_schema_from_type_predicate.fz".to_string()),
        text: concat!(
            "defmodule Packet do\n",
            "  defstruct [:value]\n",
            "  @type t :: %Packet{value: integer}\n",
            "  fn pass(x :: t), do: x\n",
            "end\n",
        )
        .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: Some("Packet".to_string()),
        name: "pass".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root);
    assert_resolved(
        compiler.drive(),
        "a typed root whose body never constructs or destructures Packet should still settle",
    );

    assert_eq!(
        backend.last(root).program.schema("Packet").map(Vec::as_slice),
        Some(["value".to_string()].as_slice()),
        "the retained entry predicate must carry Packet's typed schema dependency even without a Struct step"
    );
}

#[test]
fn compiler2_main_root_keeps_its_struct_schema_independent_of_a_macro_root() {
    // A macro owns an independent compile-time root. Its integer-only product
    // must neither contribute to nor suppress the runtime root's exact Widget
    // dependency; the runtime root packages Widget because its own pruned body
    // constructs and reads it.
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("struct_schema_complete_alongside_macro_root.fz".to_string()),
        text: concat!(
            "defmacro triple(x) do\n",
            "  quote do: unquote(x) * 3\n",
            "end\n",
            "\n",
            "defmodule Widget do\n",
            "  defstruct [:label, :count]\n",
            "end\n",
            "\n",
            "fn main() do\n",
            "  w = %Widget{count: triple(2), label: \"a\"}\n",
            "  dbg(w.label)\n",
            "  dbg(w.count)\n",
            "end\n",
        )
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "the main root's struct construction/field-access should settle alongside the macro root's own build",
    );

    let program = backend.last(root_id).program;
    assert_eq!(
        program.schema("Widget").map(Vec::as_slice),
        Some(["label".to_string(), "count".to_string()].as_slice()),
        "the runtime root must retain its exact Widget schema (in declaration order) even though an \
         independently driven macro root touches no structs in the shared World",
    );
}

#[test]
fn compiler2_index_code_defines_owned_functions_without_lowering_or_activating_bodies() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let source = include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string();

    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: source,
    });

    assert_eq!(
        outputs.stops_matching(|job| matches!(job, Job::IndexCode(_))).len(),
        0,
        "submit_code should not index eagerly"
    );

    assert_resolved(compiler.drive(), "first drive should index quicksort plus foo");

    let indexed_stop = outputs.stop(Job::IndexCode(code_id));
    assert!(indexed_stop.effects_present, "indexing job should finish with effects");

    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for quicksort plus foo"
    );
    assert_resolved(compiler.drive(), "second drive should define quicksort plus foo");

    let mut names = functions
        .all()
        .into_iter()
        .filter(|record| {
            !matches!(
                record.function_ref.name.as_str(),
                "fn" | "fnp" | "defmacro" | "defmodule" | "defprotocol" | "defimpl"
            )
        })
        .map(|record| {
            (
                record.function_ref.name.clone(),
                record.arity,
                function_module_name(&record, &modules),
                function_fq_name(&record, &modules),
                if record.owner_function_id.is_some() {
                    "generated".to_string()
                } else {
                    "function".to_string()
                },
                record.clauses,
            )
        })
        .collect::<Vec<_>>();
    names.sort_by(|left, right| left.0.cmp(&right.0).then(left.1.cmp(&right.1)));
    assert_eq!(
        names
            .iter()
            .map(|(name, arity, module, fq_name, kind, clauses)| {
                (
                    name.as_str(),
                    *arity,
                    module.as_str(),
                    fq_name.as_str(),
                    kind.as_str(),
                    *clauses,
                )
            })
            .collect::<Vec<_>>(),
        vec![
            ("append", 2, "<top-level>", "append", "function", 2),
            ("foo", 0, "<top-level>", "foo", "function", 1),
            ("main", 0, "<top-level>", "main", "function", 1),
            ("partition", 4, "<top-level>", "partition", "function", 3),
            ("qsort", 1, "<top-level>", "qsort", "function", 2),
        ],
        "scoping should note the expected user-defined top-level function surfaces once compiler definition macros are filtered out"
    );

    assert!(
        capture
            .find(&["fz", "compiler2", "function", "defined"])
            .into_iter()
            .all(|event| {
                event
                    .metadata
                    .get("function_ref")
                    .and_then(|value| value.downcast_ref::<FunctionRef>())
                    .is_none_or(|function_ref| {
                        matches!(
                            function_ref.name.as_str(),
                            "fn" | "fnp" | "defmacro" | "defmodule" | "defprotocol" | "defimpl"
                        )
                    })
            }),
        "scoping should not eagerly materialize user function definitions"
    );
    assert_eq!(
        names.len(),
        5,
        "scoping should note one user function-source fact per top-level function"
    );
    assert!(
        capture
            .find(&["fz", "compiler2", "function", "source", "noted"])
            .into_iter()
            .all(|event| event.metadata.len() == 0),
        "generic capture should not durable-copy synthesized function-source metadata"
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "code", "indexed"]),
        0,
        "indexing should not emit a separate code.indexed event"
    );
    assert_eq!(
        outputs
            .stops_matching(|job| matches!(job, Job::IndexCode(id) if *id == code_id))
            .len(),
        1,
        "indexing should close one IndexCode job span for the user submission"
    );
    let user_function_ids = [
        function_id(&functions, "append", 2),
        function_id(&functions, "foo", 0),
        function_id(&functions, "main", 0),
        function_id(&functions, "partition", 4),
        function_id(&functions, "qsort", 1),
    ];
    assert!(
        user_function_ids.into_iter().all(|function| {
            outputs
                .stops_matching(|job| matches!(job, Job::LowerFunction(id) if *id == function))
                .is_empty()
        }),
        "indexing should not lower any user function bodies"
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "fact", "published"]),
        0,
        "indexing should not emit redundant fact.published telemetry"
    );

    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "indexing should stay above lowering"
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "indexing should stay above planning"
    );

    let outputs = outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects");
    assert_eq!(
        outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::FunctionDefined(_)))
            .count(),
        0,
        "index_code outputs should stay in discovery and not define functions directly"
    );
    assert_eq!(
        outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleDefined(_)))
            .count(),
        0,
        "top-level quicksort indexing should not define modules directly"
    );
    assert_eq!(
        outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleIndexed(_)))
            .count(),
        0,
        "top-level quicksort indexing should not discover nested modules"
    );
    assert!(
        outputs.contains(&presence(FactKey::CodeIndexed(code_id), true)),
        "IndexCode outputs should include the final code-indexed fact"
    );
}

#[test]
fn compiler2_submit_root_pulls_scope_and_seeds_entry_semantics_without_warming_foo() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let submitted_roots = Rc::new(RefCell::new(Vec::new()));
    let submitted_root_sink = Rc::clone(&submitted_roots);
    tel.attach_raw_event2::<crate::compiler2::World, crate::compiler2::RootId, _>(
        &["fz", "compiler2", "root", "submitted"],
        move |_, _, _, _, root| submitted_root_sink.borrow_mut().push(*root),
    );
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let _code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "root submission should pull the source surface through to the entry seed",
    );

    let root_submitted = capture
        .last(&["fz", "compiler2", "root", "submitted"])
        .expect("root submitted event");
    assert_eq!(submitted_roots.borrow().as_slice(), &[root_id]);
    assert_eq!(
        root_submitted.metadata.len(),
        0,
        "generic capture should not durable-copy opaque root submission metadata",
    );

    let main_id = function_id(&functions, "main", 0);
    let foo_id = function_id(&functions, "foo", 0);

    let lower_outputs = outputs
        .take(Job::LowerFunction(main_id))
        .expect("LowerFunction job effects for main/0");
    assert!(
        lower_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::LoweredBody(main_id)),
        "submitting a root should lower the entry function body"
    );
    assert!(
        !lower_outputs
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::LoweredBody(function) if *function == foo_id)),
        "lowering the entry function should keep uncalled foo/0 cold"
    );

    let seed_outputs = outputs.take(Job::SeedRoot(root_id)).expect("SeedRoot job effects");
    let entry_activation = ActivationKey::from_inputs(root_id, main_id, &[], compiler.types_mut_for_test());
    assert!(
        seed_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::RootEntry(root_id)),
        "SeedRoot should publish the root entry fact"
    );
    assert!(
        seed_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::Activation(entry_activation.clone())),
        "SeedRoot should publish the entry activation"
    );
    assert!(
        seed_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::ActivationInputs(entry_activation.clone())),
        "SeedRoot should publish the entry activation-input evidence fact",
    );
    assert!(
        seed_outputs.iter().any(|(fact, _)| {
            *fact
                == FactKey::Executable(ExecutableKey {
                    activation: entry_activation.clone(),
                    need: ExecutableNeed::Value,
                })
        }),
        "SeedRoot should publish the entry executable request"
    );

    assert!(
        !outputs
            .stops_matching(|job| matches!(job, Job::ScopeCode(_)))
            .is_empty(),
        "root submission should pull the source surface work it needs"
    );
    assert!(
        outputs.stops_matching(|job| matches!(job, Job::SeedRoot(_))).len() >= 2,
        "root submission should let SeedRoot retry while the entry definition and keying facts settle"
    );
    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::LowerFunction(function) if *function == foo_id))
            .is_empty(),
        "root submission should keep uncalled foo/0 cold through lowering"
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "root seeding should not invoke lowering yet"
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "root seeding should not invoke the production planner"
    );
    assert_eq!(
        capture.find(&["fz", "type_infer"]).len(),
        0,
        "root seeding should not invoke the legacy type inference pipeline"
    );
}

#[test]
fn compiler2_root_scopes_only_the_code_that_can_publish_its_entry() {
    let tel = ConfiguredTelemetry::new();
    let source_notes = SourceNoteCapture::new();
    source_notes.install(&tel);
    let outputs = OutputCapture::new();
    outputs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let main_code = compiler.submit_code(CodeSubmission {
        name: Some("main_only.fz".to_string()),
        text: "fn main(), do: 1\n".to_string(),
    });
    let unrelated_code = compiler.submit_code(CodeSubmission {
        name: Some("foo_only.fz".to_string()),
        text: "fn foo(), do: 2\n".to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "root demand should scope the code that can publish main/0 without sweeping unrelated code",
    );

    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::ScopeCode(id) if *id == main_code))
            .iter()
            .any(|stop| {
                stop.effects
                    .as_ref()
                    .is_some_and(|effects| effects.outputs.contains(&FactKey::CodeScoped(main_code)))
            }),
        "the root entry's code should publish its scoped source fact"
    );
    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::ScopeCode(id) if *id == unrelated_code))
            .is_empty(),
        "an unrelated submitted code contribution should stay unscoped when the root cannot reach it"
    );
    assert_eq!(
        source_notes.count("main", 0),
        1,
        "the entry function source should be noted exactly once"
    );
    assert_eq!(
        source_notes.count("foo", 0),
        0,
        "unrelated function source should not be noted merely because a root exists"
    );
}

// fz-go4.53: `demand_function_scope`'s global-module branch used to name
// EVERY code containing an opaque item-macro call as a `CodeScoped` wait
// alongside the code that actually, definitely defines the wanted function
// (the fn-form home). Because the scheduler's waiter wake is AND-semantics
// (`enqueue_dependents`), that bundled the certain home together with every
// unrelated opaque candidate: resolving `main/0` would force-expand every
// custom item-macro call in the program before the job could even re-check
// whether `main/0` had already resolved. This test proves the fix: a certain
// fn-form home rules out the unrelated opaque candidates entirely, so
// resolving `main/0` never `ScopeCode`s the files whose only surface is an
// unrelated custom-macro call.
#[test]
fn compiler2_resolving_a_global_name_does_not_scope_unrelated_opaque_macro_calls() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let main_code = compiler.submit_code(CodeSubmission {
        name: Some("main_only.fz".to_string()),
        text: "fn main(), do: 1\n".to_string(),
    });
    let unrelated_macro_call = |macro_name: &str, produced_atom: &str| {
        format!(
            "defmacro {macro_name}(name_atom, [do: body]) do\n  \
             {{:fn, %{{}}, [{{name_atom, %{{}}, []}}, [{{:do, body}}]]}}\nend\n\n\
             {macro_name}(:{produced_atom}) do\n  1\nend\n"
        )
    };
    let unrelated_code_a = compiler.submit_code(CodeSubmission {
        name: Some("unrelated_a.fz".to_string()),
        text: unrelated_macro_call("dsl_a", "produced_a"),
    });
    let unrelated_code_b = compiler.submit_code(CodeSubmission {
        name: Some("unrelated_b.fz".to_string()),
        text: unrelated_macro_call("dsl_b", "produced_b"),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "resolving main/0's certain fn-form home should not require expanding unrelated item macros",
    );

    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::ScopeCode(id) if *id == main_code))
            .iter()
            .any(|stop| {
                stop.effects
                    .as_ref()
                    .is_some_and(|effects| effects.outputs.contains(&FactKey::CodeScoped(main_code)))
            }),
        "main/0's own code should still be scoped to publish it"
    );
    for unrelated in [unrelated_code_a, unrelated_code_b] {
        assert!(
            outputs
                .stops_matching(|job| matches!(job, Job::ScopeCode(id) if *id == unrelated))
                .is_empty(),
            "a file whose only surface is an unrelated opaque item-macro call must stay unscoped \
             when a certain fn-form home already resolves the wanted name, got a ScopeCode({unrelated:?})"
        );
    }
}

#[test]
fn compiler2_root_source_publication_is_once_per_code_fact() {
    let tel = ConfiguredTelemetry::new();
    // Scope publication is demand-addressed (fz-f98.14.5): the per-code-fact,
    // once-each identity surface is the eager `stashed` event; `noted` now only
    // fires for bodies that are actually pulled. This test asserts the
    // per-code-fact publication identity, so it observes `stashed`.
    let stashed_event: &'static [&'static str] = &["fz", "compiler2", "function", "source", "stashed"];
    let source_notes = SourceNoteCapture::for_event(stashed_event);
    source_notes.install(&tel);
    let outputs = OutputCapture::new();
    outputs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let user_code = compiler.submit_code(CodeSubmission {
        name: Some("no_runtime.fz".to_string()),
        text: include_str!("../../fixtures2/00009_no_runtime.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "a tiny root should publish each required source surface once",
    );

    let prelude_code = crate::compiler2::CodeId::ZERO;
    for code in [prelude_code, user_code] {
        let published = outputs
            .stops_matching(|job| matches!(job, Job::ScopeCode(id) if *id == code))
            .into_iter()
            .filter(|stop| {
                stop.effects
                    .as_ref()
                    .is_some_and(|effects| effects.outputs.contains(&FactKey::CodeScoped(code)))
            })
            .count();
        assert_eq!(
            published, 1,
            "CodeScoped({code:?}) should be published by exactly one ScopeCode completion"
        );
    }

    for (name, arity) in [
        ("fn", 1),
        ("fnp", 1),
        ("defmacro", 1),
        ("defmodule", 2),
        ("defprotocol", 2),
        ("defimpl", 2),
    ] {
        assert_eq!(
            source_notes.count(name, arity),
            1,
            "prelude macro source {name}/{arity} should be stashed exactly once per code fact"
        );
    }
    assert_eq!(
        source_notes.count("main", 0),
        1,
        "user entry source should be stashed exactly once per code fact"
    );
}

#[test]
fn compiler2_macro_executable_runs_quote_unquote_on_the_source_heap() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("macro_inc.fz".to_string()),
        text: "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n\ndefmacro quoted_var() do\n  quote do: x\nend\n\ndefmacro forward_define(source) do\n  quote do: Fz.Compiler.define(unquote(source), unquote(__CALLER__))\nend\n"
            .to_string(),
    });
    assert!(compiler.demand(Job::ScopeCode(code_id)));
    assert_resolved(
        compiler.drive(),
        "scoping should publish the macro source without lowering it",
    );

    let inc = function_id(&functions, "inc", 1);
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let arg = builder.int(41);
    let caller = builder.map(&[]).expect("caller env map");
    let carrier_root = builder.list(&[caller, arg]).expect("carrier source root");
    let carrier = builder.root(carrier_root).expect("carrier source");

    let expanded = compiler
        .run_macro_on_source(inc, &carrier, caller, &[arg])
        .expect("macro should run over the source heap");
    assert_eq!(
        expanded.key().heap_id,
        carrier.key().heap_id,
        "macro expansion must return a root in the same quoted source heap"
    );
    let node = expanded
        .cursor()
        .ast_node()
        .expect("expanded cursor")
        .expect("expanded AST node");
    assert_eq!(node.head.atom_name().expect("expanded head"), "+");
    let args = node.tail.list_items().expect("expanded args");
    assert_eq!(args.len(), 2, "inc should expand to a binary + call");
    assert_eq!(args[0].int_value().expect("spliced arg"), 41);
    assert_eq!(args[1].int_value().expect("literal increment"), 1);

    let quoted_var = function_id(&functions, "quoted_var", 0);
    let quoted = compiler
        .run_macro_on_source(quoted_var, &carrier, caller, &[])
        .expect("macro should return the quoted variable");
    assert_eq!(
        quoted.key().heap_id,
        carrier.key().heap_id,
        "quoted variables should stay rooted in the same source heap"
    );
    let var_node = quoted
        .cursor()
        .ast_node()
        .expect("quoted variable cursor")
        .expect("quoted variable AST node");
    assert_eq!(var_node.head.atom_name().expect("quoted variable head"), "x");
    assert_eq!(
        var_node.tail.atom_name().expect("quoted variable context"),
        "nil",
        "quote lowering should use the canonical no-context variable shape"
    );

    let forward_define = function_id(&functions, "forward_define", 1);
    let forwarded_source = builder
        .call(
            "fn",
            &QuotedSourceMetadata::default(),
            &[
                builder
                    .call("answer", &QuotedSourceMetadata::default(), &[])
                    .expect("head"),
                builder
                    .list(&[builder.keyword("do", builder.int(42)).expect("do keyword")])
                    .expect("kw list"),
            ],
        )
        .expect("forwarded function source");
    let forwarded = compiler
        .run_macro_on_source(forward_define, &carrier, caller, &[forwarded_source])
        .expect("macro should return a quoted compiler-service call");
    let forwarded_node = forwarded
        .cursor()
        .ast_node()
        .expect("forwarded cursor")
        .expect("forwarded AST node");
    let callee = forwarded_node
        .head
        .ast_node()
        .expect("forwarded callee")
        .expect("forwarded callee node");
    assert_eq!(
        callee.head.atom_name().expect("forwarded callee head"),
        ".",
        "quote lowering should preserve remote-call callee shape for compiler services",
    );
    let callee_parts = callee.tail.list_items().expect("forwarded callee parts");
    assert_eq!(
        callee_parts[1].atom_name().expect("forwarded function name"),
        "define",
        "quoted compiler-service call should target define/2",
    );
    let forwarded_args = forwarded_node.tail.list_items().expect("forwarded args");
    assert_eq!(
        forwarded_args[0].root(),
        forwarded_source,
        "unquote(source) should splice the grouped source fragment itself, not re-render it",
    );

    let long_doc_source = parse_quoted_program(
        "long_doc_forwarded.fz",
        r#"
@doc "Removes the first matching left-side item for each item in the right list."
@spec subtract([a], [a]) :: [a]
fn subtract(left, []), do: left
fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
        "#,
        crate::compiler2::CodeId::ZERO,
        compiler.telemetry(),
    )
    .expect("long-doc quoted parse");
    let long_doc_items = long_doc_source.cursor().list_items().expect("long-doc items");
    let long_doc_group = long_doc_source
        .interned_list_subroot(&long_doc_items.iter().map(|item| item.root()).collect::<Vec<_>>())
        .expect("long-doc grouped function root");
    let forwarded_long_doc = compiler
        .run_macro_on_source(forward_define, &carrier, caller, &[long_doc_group.root()])
        .expect("macro should forward long-doc grouped source");
    let forwarded_long_doc_node = forwarded_long_doc
        .cursor()
        .ast_node()
        .expect("forwarded long-doc cursor")
        .expect("forwarded long-doc AST node");
    let forwarded_long_doc_args = forwarded_long_doc_node
        .tail
        .list_items()
        .expect("forwarded long-doc args");
    assert_eq!(
        forwarded_long_doc_args[0].root(),
        long_doc_group.root(),
        "unquote(source) should preserve procbin-backed grouped source fragments by identity too",
    );
    let forwarded_group = long_doc_group.subroot(forwarded_long_doc_args[0].root());
    crate::compiler2::quoted_function::derive_function_surface(&forwarded_group)
        .expect("forwarded long-doc grouped source should still decode");

    let module_source = parse_quoted_program(
        "forwarded_module.fz",
        r#"
defmodule M do
  @doc "Removes the first matching left-side item for each item in the right list."
  @spec subtract([a], [a]) :: [a]
  fn subtract(left, []), do: left
  fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
end
        "#,
        crate::compiler2::CodeId::ZERO,
        compiler.telemetry(),
    )
    .expect("module quoted parse");
    let module_items = module_source.cursor().list_items().expect("module items");
    assert_eq!(module_items.len(), 1, "test module should have one top-level form");
    let forwarded_module = compiler
        .run_macro_on_source(forward_define, &carrier, caller, &[module_items[0].root()])
        .expect("macro should forward a whole module source node");
    let forwarded_module_node = forwarded_module
        .cursor()
        .ast_node()
        .expect("forwarded module cursor")
        .expect("forwarded module AST node");
    let forwarded_module_args = forwarded_module_node.tail.list_items().expect("forwarded module args");
    assert_eq!(
        forwarded_module_args[0].root(),
        module_items[0].root(),
        "unquote(source) should preserve whole defmodule source nodes by identity too",
    );
    let forwarded_module_root = module_source
        .interned_list_subroot(&[forwarded_module_args[0].root()])
        .expect("wrap forwarded module form as a top-level source list");
    let forwarded_module_surface = crate::compiler2::quoted_surface::read_scope_surface(&forwarded_module_root)
        .expect("forwarded whole-module source should still read as scope surface");
    let nested_surface = match forwarded_module_surface
        .forms
        .first()
        .expect("forwarded module surface should contain one form")
    {
        crate::compiler2::quoted_surface::ScopeForm::MacroCall(macro_call) => {
            let compiler_fragment_root = macro_call
                .source
                .interned_list_subroot(&[macro_call.source.root()])
                .expect("wrap forwarded compiler fragment as a grouped source list");
            let compiler_fragment =
                crate::compiler2::quoted_surface::read_compiler_fragment_surface(&compiler_fragment_root)
                    .expect("forwarded macro-call source should still decode as compiler fragment");
            let module_form = match compiler_fragment
                .forms
                .first()
                .expect("forwarded compiler fragment should contain one form")
            {
                crate::compiler2::quoted_surface::ScopeForm::Module(module) => module,
                other => panic!("expected compiler fragment module form, got {other:?}"),
            };
            crate::compiler2::quoted_surface::read_module_body_surface(module_form)
                .expect("forwarded module body should still decode")
        }
        other => panic!("expected forwarded module form, got {other:?}"),
    };
    let function = match nested_surface
        .forms
        .first()
        .expect("forwarded nested module body should contain one grouped function")
    {
        crate::compiler2::quoted_surface::ScopeForm::MacroCall(function) => function,
        other => panic!("expected grouped function macro call, got {other:?}"),
    };
    crate::compiler2::quoted_function::derive_function_surface(&function.source)
        .expect("whole-module forwarding should preserve nested procbin-backed @doc payloads too");
}

#[test]
fn compiler2_runtime_roots_reject_macro_entries() {
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    backend.install(&tel);
    let exceptions = Rc::new(RefCell::new(Vec::new()));
    let exception_sink = Rc::clone(&exceptions);
    tel.attach_raw_span0_1::<DriveOutcome<Job, DependencyKey>, _, _, _>(
        &["fz", "compiler2", "drive"],
        |_, _, _| {},
        |_, _, _, _, _| {},
        |_, _, _, _| {},
    );
    tel.attach_raw_span1_0::<Job, _, _, _>(
        &["fz", "compiler2", "job"],
        |_, _, _, _| {},
        |_, _, _, _| {},
        move |_, span_id, parent_span_id, _| exception_sink.borrow_mut().push((span_id, parent_span_id)),
    );

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_root.fz".to_string()),
        text: "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "inc".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });

    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { job } if job == Job::SeedRoot(root)),
        "runtime root seeding should reject macro entries before backend/native execution can gain compiler authority"
    );
    assert!(
        backend.records(root).is_empty(),
        "rejected runtime roots must not produce backend content"
    );
    assert_eq!(exceptions.borrow().len(), 1);
    assert_ne!(exceptions.borrow()[0].1, 0);
}

#[test]
fn compiler2_runtime_refs_pull_only_the_reached_runtime_modules() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("runtime_refs.fz".to_string()),
        text: include_str!("../../fixtures2/00007_runtime_refs.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "first drive should only index the user code before any root asks for runtime work",
    );

    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "rooted runtime refs should pull only the reached runtime modules through ordinary jobs",
    );

    let kernel_id = module_id(&modules, "Kernel");
    let process_id = module_id(&modules, "Process");
    let main_id = function_id(&functions, "main", 0);
    let dbg_id = function_id_in_module(&functions, &modules, "Kernel", "dbg", 1);
    let dbg_prim_id = function_id_in_module(&functions, &modules, "Kernel", "fz_dbg_value", 1);
    let heap_stats_id = function_id_in_module(&functions, &modules, "Process", "heap_alloc_stats", 0);
    let heap_stats_prim_id = function_id_in_module(&functions, &modules, "Process", "fz_process_heap_alloc_stats", 0);
    let spawn_id = function_id_in_module(&functions, &modules, "Kernel", "spawn", 1);

    assert_eq!(
        sorted_strings(modules.defined_names()),
        vec!["Kernel".to_string(), "Process".to_string()],
        "runtime root should define only the reached runtime modules"
    );
    assert!(
        !outputs
            .stops_matching(|job| matches!(job, Job::DefineModule(module) if *module == kernel_id))
            .is_empty(),
        "Kernel should be defined through the ordinary module job"
    );
    assert!(
        !outputs
            .stops_matching(|job| matches!(job, Job::DefineModule(module) if *module == process_id))
            .is_empty(),
        "Process should be defined through the ordinary module job"
    );

    assert!(matches!(lowered_body(&bodies, main_id), LoweredBody::Clauses { .. }));
    assert!(matches!(lowered_body(&bodies, dbg_id), LoweredBody::Clauses { .. }));
    assert!(matches!(
        lowered_body(&bodies, heap_stats_id),
        LoweredBody::Clauses { .. }
    ));
    assert!(matches!(lowered_body(&bodies, dbg_prim_id), LoweredBody::Extern { .. }));
    assert!(matches!(
        lowered_body(&bodies, heap_stats_prim_id),
        LoweredBody::Extern { .. }
    ));
    assert!(
        bodies.take(spawn_id).is_none(),
        "unreached Kernel.spawn/1 should stay cold even though Kernel is defined"
    );
    assert!(
        functions
            .all()
            .into_iter()
            .all(|record| function_fq_name(&record, &modules) != "Enum.reduce"),
        "unreached Enum functions should stay undefined"
    );
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty(),
        "runtime pull-through should still avoid the legacy type inference pipeline"
    );
    assert!(
        capture.find(&["fz", "planner"]).is_empty(),
        "runtime pull-through should still avoid the legacy planner pipeline"
    );
    let _ = root_id;
}

#[test]
fn compiler2_analyze_activation_publishes_one_whole_callsite_fact_per_call() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/callsite_fact_surface.fz".to_string()),
        text: include_str!("../../fixtures2/00008_callsite_fact_surface.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "a direct call root should settle through one whole callsite fact per reached call",
    );

    let main_id = function_id(&functions, "main", 0);
    let activation = ActivationKey::from_inputs(root_id, main_id, &[], compiler.types_mut_for_test());
    let activation_job = Job::AnalyzeActivation(activation.clone());
    let effects = outputs.effects(activation_job.clone());
    let outputs = outputs
        .take(activation_job)
        .expect("AnalyzeActivation job effects for main/0");
    let callsite_facts = outputs
        .iter()
        .filter(|(fact, _)| matches!(fact, FactKey::CallSiteSummary(_)))
        .count();
    let callsite_target_facts = outputs
        .iter()
        .filter(|(fact, _)| matches!(fact, FactKey::CallSiteTargets(_)))
        .count();

    assert_eq!(
        callsite_facts, 1,
        "an activation with one reached direct call should publish one whole callsite-summary fact",
    );
    assert_eq!(
        callsite_target_facts, 1,
        "an activation with one reached direct call should publish one target-only membership fact",
    );
    assert!(
        effects
            .reads
            .contains(&FactUse::current(FactKey::ActivationInputs(activation))),
        "AnalyzeActivation should read the activation-input evidence fact rather than the key's canonical input alone",
    );
}

#[test]
fn compiler2_unused_runtime_library_stays_cold() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("no_runtime.fz".to_string()),
        text: include_str!("../../fixtures2/00009_no_runtime.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "a root that never mentions runtime names should keep runtime modules cold",
    );

    let main_id = function_id(&functions, "main", 0);
    assert!(matches!(lowered_body(&bodies, main_id), LoweredBody::Clauses { .. }));
    assert!(
        modules.defined_names().is_empty(),
        "runtime modules should not be defined when no path reaches them"
    );
    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::ScopeCode(_)))
            .iter()
            .any(|stop| stop.job == Job::ScopeCode(code_id)),
        "the user code should scope even though runtime modules stay cold"
    );
    assert_eq!(
        outputs.stops_matching(|job| matches!(job, Job::DefineModule(_))).len(),
        0,
        "runtime modules should not be pulled through module definition jobs"
    );
    let _ = root_id;
}

#[test]
fn compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let callsites = CallsiteCapture::new();
    callsites.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);
    let analyzed = ActivationAnalysisCapture::new();
    analyzed.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_runtime_graph.fz".to_string()),
        text: include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "Enum.reduce should settle runtime protocol dispatch and closure calls in one semantic closure",
    );

    let function_records = functions.all();
    let defined_function_ids = function_records
        .iter()
        .map(|record| record.function_id)
        .collect::<HashSet<_>>();
    let lowered_functions = outputs
        .stops_matching(|job| matches!(job, Job::LowerFunction(_)))
        .into_iter()
        .filter_map(|stop| match stop.job {
            Job::LowerFunction(function) => Some(function),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        lowered_functions
            .iter()
            .all(|function| defined_function_ids.contains(function)),
        "Enum.reduce should only demand lowering for real function definitions, not protocol callback placeholders",
    );

    let main_id = function_id(&functions, "main", 0);
    let enum_reduce_id = function_id_in_module(&functions, &modules, "Enum", "reduce", 3);
    let enumerable_list_id = module_id(&modules, "Enumerable.List");

    let main_generated = generated_functions_owned_by(&functions, main_id);
    assert_eq!(
        main_generated.len(),
        1,
        "lowering main/0 should mint exactly one user reducer lambda",
    );
    let user_reducer_id = main_generated[0].function_id;

    let enum_generated = generated_functions_owned_by(&functions, enum_reduce_id);
    assert_eq!(
        enum_generated.len(),
        1,
        "lowering Enum.reduce/3 should mint exactly one bridge reducer lambda",
    );
    let bridge_reducer_id = enum_generated[0].function_id;

    let list_impl_reduce = function_records
        .iter()
        .cloned()
        .into_iter()
        .find(|record| {
            record.function_ref.name == "reduce" && record.arity == 3 && record.module_id == enumerable_list_id
        })
        .unwrap_or_else(|| panic!("function.defined for the selected List-backed protocol callback"));
    let list_impl_reduce_id = list_impl_reduce.function_id;

    let main_lowered = outputs
        .take(Job::LowerFunction(main_id))
        .expect("LowerFunction job effects for main/0");
    assert!(
        main_lowered
            .iter()
            .any(|(fact, _)| *fact == FactKey::FunctionDefined(user_reducer_id)),
        "lowering main/0 should surface its generated reducer function through job effects",
    );
    let enum_lowered = outputs
        .take(Job::LowerFunction(enum_reduce_id))
        .expect("LowerFunction job effects for Enum.reduce/3");
    assert!(
        enum_lowered
            .iter()
            .any(|(fact, _)| *fact == FactKey::FunctionDefined(bridge_reducer_id)),
        "lowering Enum.reduce/3 should surface its bridge reducer function through job effects",
    );

    let callsites = callsites.all();
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == enum_reduce_id
                && summary_is_single_callee(&record.summary, SelectedCallee::Function(list_impl_reduce_id))
        }),
        "Enum.reduce/3 should devirtualize Enumerable.reduce/3 to the List-backed protocol callback",
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == bridge_reducer_id
                && summary_is_single_callee(&record.summary, SelectedCallee::Function(user_reducer_id))
        }),
        "the bridge reducer should activate the user reducer closure directly",
    );

    // The settled root keeps the whole reached reduce path live and leaves
    // unrelated Enum functions cold. Observed through the per-activation
    // `activation_analysis.defined` signal: a reached activation publishes it,
    // while a defined-but-unreached function never does.
    let analyzed_functions = analyzed
        .keys_for_root(root_id)
        .into_iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    for (function, label) in [
        (main_id, "main/0"),
        (enum_reduce_id, "Enum.reduce/3"),
        (list_impl_reduce_id, "the selected List-backed protocol impl"),
        (bridge_reducer_id, "the bridge reducer lambda"),
        (user_reducer_id, "the user reducer lambda"),
    ] {
        assert!(
            analyzed_functions.contains(&function),
            "the settled root should keep {label} in the analyzed activation frontier",
        );
    }
    let enum_map_id = function_id_in_module(&functions, &modules, "Enum", "map", 2);
    let enum_reverse_id = function_id_in_module(&functions, &modules, "Enum", "reverse", 1);
    assert!(
        !analyzed_functions.contains(&enum_map_id) && !analyzed_functions.contains(&enum_reverse_id),
        "unrelated Enum functions must stay outside the settled activation frontier",
    );

    let defined_modules = sorted_strings(modules.defined_names());
    assert!(
        !defined_modules.contains(&"Map".to_string()) && !defined_modules.contains(&"Range".to_string()),
        "list-backed Enum.reduce should not pull unrelated runtime implementation modules through definition",
    );

    let main_return = returns.last_for_function(root_id, main_id).return_ty;
    let enum_reduce_return = returns.last_for_function(root_id, enum_reduce_id).return_ty;
    let list_impl_return = returns.last_for_function(root_id, list_impl_reduce_id).return_ty;
    let bridge_return = returns.last_for_function(root_id, bridge_reducer_id).return_ty;
    let user_reducer_return = returns.last_for_function(root_id, user_reducer_id).return_ty;
    assert!(
        compiler.types_equivalent_for_test(main_return, enum_reduce_return),
        "the selected reduce path should settle main/0 and Enum.reduce/3 to one return type, got main={} reduce={}",
        compiler.display_ty_for_test(main_return),
        compiler.display_ty_for_test(enum_reduce_return),
    );
    assert!(
        !compiler.types_equivalent_for_test(list_impl_return, main_return),
        "the selected List-backed protocol callback should keep a distinct wrapper return from the reduced accumulator value, got impl={} main={}",
        compiler.display_ty_for_test(list_impl_return),
        compiler.display_ty_for_test(main_return),
    );
    assert_eq!(
        compiler.display_ty_for_test(main_return),
        "int",
        "the selected reduce path should settle to an integer accumulator value",
    );
    assert_eq!(
        compiler.display_ty_for_test(bridge_return),
        "{:cont, int}",
        "the reducer bridge should carry the integer accumulator through its continuation tuple",
    );
    assert_eq!(
        compiler.display_ty_for_test(user_reducer_return),
        "int",
        "the user reducer callable should settle to the same integer value it feeds back into reduce",
    );
}

#[test]
fn compiler2_return_type_event_reports_only_actual_fact_movement() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "quicksort should settle to one semantic closure");

    let main_id = function_id(&functions, "main", 0);
    let records = returns.records_for_function(root_id, main_id);
    assert!(
        !records.is_empty(),
        "main/0 should publish at least one return_type.defined record",
    );
    for pair in records.windows(2) {
        assert!(
            !compiler.types_equivalent_for_test(pair[0].return_ty, pair[1].return_ty),
            "return_type.defined must not report an equivalent re-publication for main/0",
        );
    }

    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "re-submitting byte-identical code should resolve without changing the settled shape",
    );
    let after_replay = returns.records_for_function(root_id, main_id);
    assert_eq!(
        after_replay.len(),
        records.len(),
        "a byte-identical re-publication must not emit return_type.defined",
    );
}

#[test]
fn compiler2_enum_reduce_operator_ref_activates_kernel_plus() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let callsites = CallsiteCapture::new();
    callsites.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);
    let analyzed = ActivationAnalysisCapture::new();
    analyzed.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_operator_ref.fz".to_string()),
        text: include_str!("fixtures/enum_reduce_operator_ref.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "Enum.reduce operator refs should settle through the same protocol and callable path",
    );

    let main_id = function_id(&functions, "main", 0);
    let enum_reduce_id = function_id_in_module(&functions, &modules, "Enum", "reduce", 3);
    let kernel_plus_id = function_id_in_module(&functions, &modules, "Kernel", "+", 2);
    let enumerable_list_id = module_id(&modules, "Enumerable.List");
    let list_impl_reduce = functions
        .all()
        .into_iter()
        .find(|record| {
            record.function_ref.name == "reduce" && record.arity == 3 && record.module_id == enumerable_list_id
        })
        .unwrap_or_else(|| panic!("function.defined for the selected List-backed protocol callback"));
    let list_impl_reduce_id = list_impl_reduce.function_id;

    let callsites = callsites.all();
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == enum_reduce_id
                && summary_is_single_callee(&record.summary, SelectedCallee::Function(list_impl_reduce_id))
        }),
        "Enum.reduce/3 should still devirtualize through the List-backed protocol callback for operator refs",
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && summary_is_single_callee(&record.summary, SelectedCallee::Function(kernel_plus_id))
        }),
        "function-ref reducers should surface Kernel.+/2 as an ordinary callable edge",
    );

    // The operator-ref root keeps Kernel.+/2 live alongside the selected reduce
    // path and leaves unrelated Enum functions cold — read off the settled
    // per-activation `activation_analysis.defined` frontier.
    let analyzed_functions = analyzed
        .keys_for_root(root_id)
        .into_iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    for (function, label) in [
        (main_id, "main/0"),
        (enum_reduce_id, "Enum.reduce/3"),
        (list_impl_reduce_id, "the selected List-backed protocol impl"),
        (kernel_plus_id, "Kernel.+/2"),
    ] {
        assert!(
            analyzed_functions.contains(&function),
            "the settled operator-ref root should keep {label} in the analyzed activation frontier",
        );
    }
    let enum_map_id = function_id_in_module(&functions, &modules, "Enum", "map", 2);
    assert!(
        !analyzed_functions.contains(&enum_map_id),
        "unrelated Enum functions must stay outside the operator-ref activation frontier",
    );

    let main_return = returns.last_for_function(root_id, main_id).return_ty;
    let enum_reduce_return = returns.last_for_function(root_id, enum_reduce_id).return_ty;
    let kernel_plus_return = returns.last_for_function(root_id, kernel_plus_id).return_ty;
    assert!(
        !compiler.types_equivalent_for_test(main_return, kernel_plus_return),
        "main/0 should keep a distinct tuple-shaped return from the reducer callback's scalar return, got main={} kernel_plus={}",
        compiler.display_ty_for_test(main_return),
        compiler.display_ty_for_test(kernel_plus_return),
    );
    assert!(
        compiler.types_equivalent_for_test(enum_reduce_return, kernel_plus_return),
        "Enum.reduce/3 should settle to the same scalar return as the reached Kernel.+/2 reducer callback, got reduce={} kernel_plus={}",
        compiler.display_ty_for_test(enum_reduce_return),
        compiler.display_ty_for_test(kernel_plus_return),
    );
    assert_eq!(
        compiler.display_ty_for_test(main_return),
        "{int, int}",
        "the qualified and bare operator-ref reducers should both settle to integer results",
    );
    assert_eq!(
        compiler.display_ty_for_test(enum_reduce_return),
        "int",
        "the protocol-selected reduce path should settle to int for operator refs",
    );
    assert_eq!(
        compiler.display_ty_for_test(kernel_plus_return),
        "int",
        "the reached Kernel.+ activation should stay on the integer lane",
    );
}

#[test]
fn compiler2_lowering_rejects_unbound_local_function_refs_before_artifact_planning() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/unresolved_callable_boundary.fz".to_string()),
        text: include_str!("../../fixtures2/00014_unresolved_callable_boundary.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let job = match compiler.drive() {
        DriveOutcome::Fatal { job } => job,
        other => panic!("unbound local fn refs should fail during lowering: {other:?}"),
    };
    assert!(
        matches!(job, Job::LowerFunction(_)),
        "the fatal should come from lowering the root body, got {job:?}",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("callable-boundary diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::LOWER_UNBOUND.0,
        "unbound local fn refs should surface as lowering-time unbound diagnostics",
    );
    let message = metadata_str(&diagnostic, "message");
    assert!(
        message.contains("missing/1"),
        "the lowering diagnostic should identify the unresolved function reference, got: {message}",
    );
}

#[test]
fn compiler2_import_only_exact_fn_refs_lower_as_function_ids_without_provider_bodies() {
    let tel = ConfiguredTelemetry::new();
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only_exact_fn_ref.fz".to_string()),
        text: "import Math, only: [add: 2]\nfn main(), do: &add/2\n".to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index the exact fn-ref fixture");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "fixture scope should be demandable"
    );
    assert_resolved(compiler.drive(), "second drive should define the importing module");

    let main_id = function_id(&functions, "main", 0);
    assert!(
        compiler.demand(Job::LowerFunction(main_id)),
        "main/0 lowering should be demandable"
    );
    assert_resolved(
        compiler.drive(),
        "lowering the imported fn-ref fixture should not need the provider body",
    );

    let body = lowered_body(&bodies, main_id);
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        panic!("main/0 should lower as clauses");
    };
    let has_function_ref = clauses
        .iter()
        .flat_map(|clause| clause.projections.iter())
        .chain(entries.iter().flat_map(|entry| entry.steps.iter()))
        .any(|step| matches!(step, LoweredStep::FunctionRef { .. }));
    assert!(
        has_function_ref,
        "exact imported fn refs should lower directly as FunctionRef steps backed by FunctionId",
    );
}

#[test]
fn compiler2_seed_root_does_not_depend_on_its_own_root_fact() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("seed_root_no_self_edge.fz".to_string()),
        text: "fn main(), do: 0\n".to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "simple root should resolve so SeedRoot effects are captured",
    );

    let seed = outputs.effects(Job::SeedRoot(root_id));
    assert!(
        !seed.reads.contains(&settled_fact(FactKey::RootEntry(root_id))),
        "SeedRoot must not subscribe to the settled transition of its own RootEntry output: {seed:?}",
    );
}

#[test]
fn compiler2_backend_program_keeps_only_the_closed_quicksort_inventory() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "backend lowering should keep only the closed quicksort frontier and attach settled call targets",
    );

    let program = backend.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);

    let executable_ids = program
        .executables()
        .iter()
        .map(|executable| executable.key.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        program.entry().activation.function,
        main_id,
        "the backend-program entry should still name the main/0 executable",
    );
    assert!(
        executable_ids.contains(&main_id)
            && executable_ids.contains(&qsort_id)
            && executable_ids.contains(&partition_id)
            && executable_ids.contains(&append_id),
        "backend lowering should keep the closed quicksort executable frontier",
    );
    assert!(
        !executable_ids.contains(&foo_id),
        "backend lowering should keep cold foo/0 out of the backend handoff",
    );
    assert!(
        program.construction_wrappers().is_empty(),
        "quicksort should not manufacture callable constructions in the backend handoff",
    );

    let (_, main_exec) = backend_executable(&program, main_id);
    let call = backend_direct_call(main_exec, qsort_id);
    match call {
        BackendTail::DirectCall { target, args, .. } => {
            let CallEdge::Direct(direct) = target else {
                panic!("expected backend direct edge for main/0 -> qsort/1");
            };
            assert_eq!(
                local_call_target(&direct.callee).activation.function,
                qsort_id,
                "backend direct-call steps should name settled executable identities",
            );
            assert_eq!(
                args.len(),
                1,
                "the main/0 quicksort call should carry one plain argument"
            );
        }
        other => panic!("expected backend direct-call step to qsort/1, got {other:?}"),
    }

    assert!(
        capture.find(&["fz", "planner"]).is_empty() && capture.find(&["fz", "codegen"]).is_empty(),
        "backend lowering should not wake the legacy planner or codegen pipelines",
    );
    let settlements = capture.find(&["fz", "compiler2", "pull", "product", "settled"]);
    assert!(!settlements.is_empty(), "backend compilation must settle products");
    assert!(
        settlements.into_iter().all(|event| event.metadata.len() == 0),
        "generic capture should not durable-copy opaque product payloads",
    );
}

#[test]
fn compiler2_backend_program_carries_tail_return_flow_from_transport_facts() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("backend_tail_return_flow.fz".to_string()),
        text: r#"
fn inc(x), do: x + 1
fn main(), do: inc(41)
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "backend lowering should carry settled tail return-flow facts",
    );

    let program = backend.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let inc_id = function_id(&functions, "inc", 1);
    let (_, main_exec) = backend_executable(&program, main_id);
    let call = backend_direct_call(main_exec, inc_id);
    let BackendTail::DirectCall {
        target: CallEdge::Direct(target),
        ..
    } = call
    else {
        panic!("main/0 should tail-call inc/1, got {call:?}");
    };
    let BackendReturnFlow::Tail = &target.return_flow else {
        panic!(
            "same-contract direct return should be classified as Tail, got {:?}",
            target.return_flow
        );
    };
}

#[test]
fn compiler2_backend_dispatch_preserves_divergent_target_as_no_return() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("receive_after_divergent_dispatch.fz".to_string()),
        text: RECEIVE_AFTER_DIVERGENT_DISPATCH.to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "receive-after arithmetic should preserve the divergent dispatch member in the backend product",
    );

    let program = backend.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let (_, main) = backend_executable(&program, main_id);
    let BackendBody::Clauses { entries, .. } = &main.body else {
        panic!("main/0 should lower as clauses");
    };
    let dispatch = entries
        .iter()
        .find_map(|entry| match &entry.tail {
            BackendTail::DirectCall {
                target: CallEdge::Dispatch(dispatch),
                ..
            } if dispatch.arms.len() == 2 => Some(dispatch),
            _ => None,
        })
        .expect("post-receive arithmetic should lower as a two-member direct dispatch");

    assert_eq!(
        dispatch
            .arms
            .iter()
            .filter(|arm| matches!(arm.return_flow, BackendReturnFlow::Deliver { .. }))
            .count(),
        1,
        "the numeric member should deliver its result to the post-call resume",
    );
    assert_eq!(
        dispatch
            .arms
            .iter()
            .filter(|arm| matches!(arm.return_flow, BackendReturnFlow::NoReturn))
            .count(),
        1,
        "the no-matching-clause member must preserve its settled no-return authority",
    );
}

#[test]
fn compiler2_backend_program_carries_return_payload_flow_before_native_lowering() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/multi_relay.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/multi_relay.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    let drive = compiler.drive();
    if !matches!(drive, DriveOutcome::Resolved) {
        let diagnostic = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "backend lowering should classify multi_relay return flow before native lowering: {drive:?}; diagnostic={diagnostic}"
        );
    }

    let program = backend.last(root_id).program;
    let mut saw_return_payload_flow = false;
    for executable in program.executables() {
        let crate::compiler2::BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries {
            match &entry.tail {
                BackendTail::DirectCall {
                    target: CallEdge::Direct(target),
                    ..
                } => {
                    if return_flow_is_distinct_return_payload(&target.return_flow, &executable.abi.return_layout) {
                        saw_return_payload_flow = true;
                    }
                }
                BackendTail::ClosureCall {
                    return_flow: Some(return_flow),
                    ..
                } if return_flow_is_distinct_return_payload(return_flow, &executable.abi.return_layout) => {
                    saw_return_payload_flow = true;
                }
                _ => {}
            }
        }
    }

    assert!(
        saw_return_payload_flow,
        "multi_relay should carry at least one non-tail ReturnPayload flow in BackendProgram"
    );
}

#[test]
fn compiler2_backend_program_keeps_direct_only_enum_reduce_out_of_callable_inventory() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_runtime_graph.fz".to_string()),
        text: include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "backend lowering should keep direct-only Enum.reduce reducers out of first-class callable inventory",
    );

    let main_id = function_id(&functions, "main", 0);
    let enum_reduce_id = function_id_in_module(&functions, &modules, "Enum", "reduce", 3);
    let user_reducer_id = generated_functions_owned_by(&functions, main_id)
        .into_iter()
        .next()
        .expect("generated user reducer")
        .function_id;
    let bridge_reducer_id = generated_functions_owned_by(&functions, enum_reduce_id)
        .into_iter()
        .next()
        .expect("generated bridge reducer")
        .function_id;

    let program = backend.last(root_id).program;
    assert!(
        program.construction_wrappers().is_empty(),
        "backend construction-wrapper inventory should stay empty for direct-only reducer transport",
    );
    let executable_functions = program
        .executables()
        .iter()
        .map(|executable| executable.key.activation.function)
        .collect::<HashSet<_>>();
    assert!(
        executable_functions.is_superset(&HashSet::from([user_reducer_id, bridge_reducer_id])),
        "the user reducer and bridge reducer should still survive in the backend executable inventory",
    );
}

// fz-hwn.23: the Halt-specialized-DeliveredResume regression guard once aggravated by
// `00010_enum_reduce_main` is RETIRED. Its precondition — a resume continuation whose
// body specialized to `Halt` because its delivered value was a value-template (absent)
// — is no longer constructible: cross-activation surface grounding replaces the dead
// generic reducer (whose result was absent) with its ground sibling (which returns a
// real `int`), so no resume continuation receives an absent delivered value. Proven by a
// whole-matrix scan (337 fixtures, 0 Halt-specialized DeliveredResume targets). The
// surviving, legitimate zero-width resume payload (an IGNORED call result) is guarded by
// `compiler2_native_program_does_not_fabricate_nil_for_zero_width_resume_payloads`.

#[test]
fn compiler2_native_program_does_not_fabricate_nil_for_zero_width_resume_payloads() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        // `Enum.each` discards each element's mapped result, so the per-element
        // call delivers an IGNORED value to its resume continuation — a genuinely
        // zero-width resume payload (`Nothing` shape by demand, not by a missing
        // type). This is the durable subject for the no-nil-fabrication invariant.
        // (It previously used `Enum.reduce([1..5], 0, …)`, whose zero-width
        // continuation was a redundant-generic artifact that fz-hwn.23 grounds
        // away — see ground_surface_for_template; that shape is no longer emitted.)
        name: Some("fixtures/enum_each_zero_width_payload.fz".to_string()),
        text: r#"fn main(), do: Enum.each([1, 2, 3], fn (x) -> x end)"#.to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should settle before inspecting zero-width resume payloads: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let zero_width_continuations = program
        .bodies
        .iter()
        .filter(|body| body.entry_abi == NativeEntryAbi::Continuation { extra_params: 0 })
        .collect::<Vec<_>>();
    assert!(
        !zero_width_continuations.is_empty(),
        "enum_reduce should expose at least one structurally retained zero-width continuation"
    );
    let fabricated_nil_continuations = zero_width_continuations
        .iter()
        .filter(|body| native_function_contains_nil_const(&program, body.fn_id))
        .collect::<Vec<_>>();
    assert!(
        fabricated_nil_continuations.is_empty(),
        "zero-width resume payloads are absent by construction; native must not fabricate nil values for them: {:?}",
        fabricated_nil_continuations
            .iter()
            .map(|body| (&body.origin, program.module.fn_by_id(body.fn_id)))
            .collect::<Vec<_>>()
    );
}

// fz-hwn.23: the `BackendStep::Omitted` (fact-proven-absent tuple build) regression
// guard once aggravated by `00278_enum_count_predicate` is RETIRED. Its precondition
// — a tuple whose field is a value-template (transport-absent) value — is no longer
// constructible: cross-activation surface grounding (ground_surface_for_template)
// replaces the dead generic activation that produced the absent field with its ground
// sibling, so no tuple field reaches the backend absent. Proven by a whole-matrix scan
// (337 fixtures, 0 omitted tuple builds). The stronger invariant — no value-template
// activation reaches lowering — is now guarded directly by
// `compiler2_interp_runs_enum_with_index_mapper_from_backend_artifacts`.

#[test]
fn compiler2_backend_program_preserves_variadic_extern_wire_classes() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/variadic_open_compiler2.fz".to_string()),
        text: include_str!("../../fixtures2/00013_variadic_open.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "backend lowering should preserve the settled variadic extern signature and wire classes",
    );

    let program = backend.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let open_id = function_id(&functions, "libc::open", 2);
    let (_, open_exec) = backend_executable(&program, open_id);
    let (_, main_exec) = backend_executable(&program, main_id);

    match &open_exec.body {
        crate::compiler2::BackendBody::Extern { signature } => {
            assert_eq!(signature.symbol, "open");
            assert_eq!(signature.params, vec![ExternTy::CString, ExternTy::I64]);
            assert!(signature.variadic);
            assert_eq!(signature.ret, ExternTy::I64);
        }
        other => panic!("expected backend extern body for libc::open, got {other:?}"),
    }

    let call = backend_direct_call(main_exec, open_id);
    match call {
        BackendTail::DirectCall { target, args, .. } => {
            let CallEdge::Direct(direct) = target else {
                panic!("expected backend direct edge for libc::open");
            };
            assert_eq!(
                local_call_target(&direct.callee).activation.function,
                open_id,
                "backend extern calls should still target the settled extern executable identity",
            );
            assert_eq!(
                direct.extern_marshals.as_deref(),
                Some(&[ExternTy::CString, ExternTy::I64, ExternTy::I64][..]),
                "backend direct-call steps should carry the exact settled C wire classes for a variadic extern site",
            );
            assert_eq!(
                args.len(),
                3,
                "plain variadic extern calls should carry every source value argument without callable side-channel obligations"
            );
        }
        other => panic!("expected backend direct-call step to libc::open/2, got {other:?}"),
    }

    assert!(
        capture.find(&["fz", "planner"]).is_empty() && capture.find(&["fz", "codegen"]).is_empty(),
        "backend lowering should not wake the legacy planner or codegen pipelines",
    );
}

#[test]
fn compiler2_native_program_keeps_only_the_closed_quicksort_inventory() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should keep only the closed quicksort executable frontier: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);

    let executable_ids = native_executable_functions(&program);
    assert_eq!(
        native_executable_fn(&program, main_id),
        program.entry,
        "the native-program entry should still point at the main/0 executable body",
    );
    assert!(
        executable_ids.contains(&main_id)
            && executable_ids.contains(&qsort_id)
            && executable_ids.contains(&partition_id)
            && executable_ids.contains(&append_id),
        "native lowering should keep the closed quicksort executable frontier",
    );
    assert!(
        !executable_ids.contains(&foo_id),
        "native lowering should keep cold foo/0 out of the native handoff",
    );
    assert!(
        program.callable_boundaries.is_empty(),
        "quicksort should not manufacture callable-boundary inventory in the native handoff",
    );
}

/// fz-go4.18.3 schedule-independence guard for the producer-sourced resume
/// shape. A destination-passing (`TupleFields`) callee physically delivers every
/// field of its return ABI into the caller's continuation, so the delivered
/// resume payload's structure is owned by the PRODUCER, never by the caller's
/// (possibly under-demanding) value-demand. Before the keystone, the caller's
/// `TupleFields([Whole, Ignore])` demand drove `project_callsite_return`, which
/// projected the ignored field to `Nothing` and erased it from the continuation
/// ABI -- so the tuple-field continuation collapsed to zero fields and native
/// fatally materialized the absent delivered field. The keystone sources the
/// delivered DATA return's structure from the callee `ExecutableReturn` ABI, so
/// every delivered field survives.
///
/// In isolation this fixture collapses deterministically (the field is dropped
/// on every drive), so this is primarily a structural-completeness guard; the
/// schedule-dependence that made the regression intermittent bites suite-wide,
/// where per-HashMap/per-process hash-seed variance picks job wake order. Either
/// way the asserted invariant is the same: on EVERY drive, partition/4's
/// tuple-field continuation is structurally complete -- it accepts both
/// delivered fields (`extra_params: 2`), never a field erased to absent. The
/// repeated drives also confirm the producer-sourced shape is stable across the
/// fresh-`Compiler2` hash seeds. Observed through the `native_program`
/// telemetry product, not an internal projection hook.
#[test]
fn compiler2_native_program_resume_payload_shape_is_schedule_independent() {
    let delivered_tuple_field_continuation_arities = || -> Vec<usize> {
        let tel = ConfiguredTelemetry::new();
        let native = NativeProgramCapture::new();
        native.install(&tel);

        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
            text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
        });
        let root_id = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        settle_native_product(&mut compiler, root_id);
        assert_resolved(
            compiler.drive(),
            "quicksort native lowering should settle when reading the delivered resume payload shape",
        );

        let program = native.last(root_id).program;
        let qsort_owners = program
            .bodies
            .iter()
            .filter_map(|body| match &body.origin {
                NativeBodyOrigin::Executable(_) if program.module.fn_by_id(body.fn_id).name.starts_with("qsort__e") => {
                    Some(body.fn_id)
                }
                _ => None,
            })
            .collect::<HashSet<_>>();
        program
            .bodies
            .iter()
            .filter_map(|body| match body.origin {
                NativeBodyOrigin::Continuation { owner, .. } if qsort_owners.contains(&owner) => match body.entry_abi {
                    NativeEntryAbi::Continuation { extra_params } => Some(extra_params),
                    NativeEntryAbi::Direct => None,
                },
                _ => None,
            })
            .collect()
    };

    // Three in-process drives under varying wake order: the delivered tuple-field
    // continuation must be present and carry BOTH fields every time. A
    // demand-sourced (oscillating) shape would erase the ignored field on some
    // schedules, dropping the continuation to zero `extra_params` or omitting it.
    for run in 1..=3 {
        let arities = delivered_tuple_field_continuation_arities();
        let tuple_field_conts = arities.iter().filter(|&&extra| extra == 2).count();
        assert_eq!(
            tuple_field_conts, 1,
            "partition/4 delivers a two-field tuple, so the rooted quicksort frontier must keep exactly one \
             structurally complete two-field continuation on every schedule (run {run}); saw continuation \
             arities {arities:?}",
        );
    }
}

/// fz-go4.18.3.2.3 -- the reliable CONSUMPTION SIGNAL must draw exactly one
/// distinction, the same way on every schedule: a delivered resume whose value
/// the body consumes (or which a destination-passing callee physically fills)
/// keeps its full structure, while a genuinely-discarded by-value resume stays
/// zero-width and is never fabricated into a nil.
///
/// `partition/4` in quicksort delivers a two-field tuple continuation the
/// recursive sort then reads (destination-passing -> `extra_params == 2`).
/// `Enum.each`'s element call discards its mapped result (by-value, read
/// nowhere -> a zero-width `extra_params == 0` continuation with no nil const).
/// The signal is derived from the static lowered body, so the distinction holds
/// across repeated in-process drives -- a demand-`is_ignore`-sourced shape would
/// flip one of these on some schedule (collapsing the consumed tuple field to
/// `Nothing`, or erasing the discarded zero-width continuation).
#[test]
fn compiler2_native_program_resume_shape_distinguishes_destination_passing_from_ignored_by_value() {
    let destination_passing_tuple_field_arities = || -> Vec<usize> {
        let tel = ConfiguredTelemetry::new();
        let native = NativeProgramCapture::new();
        native.install(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
            text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
        });
        let root_id = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        settle_native_product(&mut compiler, root_id);
        assert_resolved(compiler.drive(), "quicksort native lowering should settle");
        let program = native.last(root_id).program;
        let qsort_owners = program
            .bodies
            .iter()
            .filter_map(|body| match &body.origin {
                NativeBodyOrigin::Executable(_) if program.module.fn_by_id(body.fn_id).name.starts_with("qsort__e") => {
                    Some(body.fn_id)
                }
                _ => None,
            })
            .collect::<HashSet<_>>();
        program
            .bodies
            .iter()
            .filter_map(|body| match body.origin {
                NativeBodyOrigin::Continuation { owner, .. } if qsort_owners.contains(&owner) => match body.entry_abi {
                    NativeEntryAbi::Continuation { extra_params } => Some(extra_params),
                    NativeEntryAbi::Direct => None,
                },
                _ => None,
            })
            .collect()
    };

    let discarded_by_value_zero_width = || -> (usize, bool) {
        let tel = ConfiguredTelemetry::new();
        let native = NativeProgramCapture::new();
        native.install(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/enum_each_zero_width_payload.fz".to_string()),
            text: r#"fn main(), do: Enum.each([1, 2, 3], fn (x) -> x end)"#.to_string(),
        });
        let root_id = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        settle_native_product(&mut compiler, root_id);
        assert_resolved(compiler.drive(), "Enum.each native lowering should settle");
        let program = native.last(root_id).program;
        let zero_width = program
            .bodies
            .iter()
            .filter(|body| body.entry_abi == NativeEntryAbi::Continuation { extra_params: 0 })
            .collect::<Vec<_>>();
        let fabricated = zero_width
            .iter()
            .any(|body| native_function_contains_nil_const(&program, body.fn_id));
        (zero_width.len(), fabricated)
    };

    for run in 1..=3 {
        let dp = destination_passing_tuple_field_arities();
        assert_eq!(
            dp.iter().filter(|&&extra| extra == 2).count(),
            1,
            "a CONSUMED destination-passing tuple continuation must stay structurally complete on every schedule \
             (run {run}); saw {dp:?}",
        );
        let (zero_width, fabricated) = discarded_by_value_zero_width();
        assert!(
            zero_width >= 1,
            "a genuinely-discarded by-value resume must retain its zero-width continuation on every schedule (run {run})",
        );
        assert!(
            !fabricated,
            "a retained zero-width continuation must never fabricate a nil value (run {run})",
        );
    }
}

#[test]
fn compiler2_native_program_matches_tuple_field_call_continuations_to_the_callee_return_abi() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should preserve tuple-field call contracts in quicksort continuations: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let qsort_owners = program
        .bodies
        .iter()
        .filter_map(|body| match &body.origin {
            NativeBodyOrigin::Executable(_) if program.module.fn_by_id(body.fn_id).name.starts_with("qsort__e") => {
                Some(body.fn_id)
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let tuple_field_conts = program
        .bodies
        .iter()
        .filter(|body| {
            matches!(
                body.origin,
                NativeBodyOrigin::Continuation { owner, .. } if qsort_owners.contains(&owner)
            ) && body.entry_abi == NativeEntryAbi::Continuation { extra_params: 2 }
        })
        .collect::<Vec<_>>();
    assert_eq!(
        tuple_field_conts.len(),
        1,
        "the rooted quicksort frontier reaches one collapsed qsort executable, and it should own one tuple-field continuation from partition/4",
    );
    for tuple_field_cont in tuple_field_conts {
        let function = program.module.fn_by_id(tuple_field_cont.fn_id);
        let entry_block = function
            .blocks
            .first()
            .expect("tuple-field continuation should have an entry block");
        assert_eq!(
            tuple_field_cont.entry_abi,
            NativeEntryAbi::Continuation { extra_params: 2 },
            "the continuation fed by partition/4's tuple-field executable should accept both returned fields explicitly",
        );
        assert_eq!(
            tuple_field_cont.param_reprs[..2],
            [AbiValueRepr::ValueRef, AbiValueRepr::ValueRef],
            "the tuple-field continuation should expose both returned field lanes first",
        );
        let semantic_entry_params = function.semantic_entry_params();
        assert_eq!(
            semantic_entry_params.len(),
            3,
            "the tuple-field continuation should still carry exactly one semantic pivot capture after the returned fields",
        );
        assert_eq!(
            semantic_entry_params,
            entry_block.params[..3].to_vec(),
            "semantic continuation params should be the two delivered tuple fields followed by the pivot capture",
        );
        assert_eq!(
            function.physical_entry_params.len(),
            1,
            "the quicksort continuation should also carry the reusable-cons source as one physical capability param",
        );
        assert_eq!(
            entry_block.params.len(),
            tuple_field_cont.param_reprs.len(),
            "native raw entry params should still line up with the raw ABI repr inventory",
        );
        assert_eq!(
            entry_block.params.last().copied(),
            function.physical_entry_params.first().copied(),
            "the extra raw entry param should be the physical reusable-cons source capability",
        );
        assert_eq!(
            function.physical_capabilities,
            vec![crate::fz_ir::PhysicalCapabilityFact {
                source: function.physical_entry_params[0],
                capability: crate::fz_ir::PhysicalCapability::ReusableConsCell {
                    rebuilt_head: semantic_entry_params[2],
                },
            }],
            "the physical param should restore the reusable-cons capability for the captured pivot head",
        );
    }
}

#[test]
fn compiler2_native_program_keeps_direct_only_enum_reduce_out_of_callable_inventory() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_runtime_graph.fz".to_string()),
        text: include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should keep direct-only Enum.reduce reducers out of first-class callable inventory: {outcome:?}; diagnostic={message}"
        );
    }

    let main_id = function_id(&functions, "main", 0);
    let enum_reduce_id = function_id_in_module(&functions, &modules, "Enum", "reduce", 3);
    let user_reducer_id = generated_functions_owned_by(&functions, main_id)
        .into_iter()
        .next()
        .expect("generated user reducer")
        .function_id;
    let bridge_reducer_id = generated_functions_owned_by(&functions, enum_reduce_id)
        .into_iter()
        .next()
        .expect("generated bridge reducer")
        .function_id;

    let program = native.last(root_id).program;
    assert_eq!(
        program.callable_boundaries,
        Vec::new(),
        "native callable-boundary inventory should stay empty for direct-only reducer transport",
    );
    let executable_functions = program
        .bodies
        .iter()
        .filter_map(|body| match &body.origin {
            crate::compiler2::artifact::NativeBodyOrigin::Executable(key) => Some(key.activation.function),
            _ => None,
        })
        .collect::<HashSet<_>>();
    assert!(
        executable_functions.is_superset(&HashSet::from([user_reducer_id, bridge_reducer_id])),
        "the user reducer and bridge reducer should still survive as native executable bodies",
    );
}

#[test]
fn compiler2_native_program_shares_boxed_callable_cps_without_erasing_semantic_identity() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let before_sharing = Rc::new(RefCell::new(Vec::<NativeProgram>::new()));
    let before_sharing_sink = Rc::clone(&before_sharing);
    tel.attach_raw_event2::<crate::compiler2::RootId, NativeProgram, _>(
        &["fz", "compiler2", "native_program", "before_sharing"],
        move |_, _, _, _, program| before_sharing_sink.borrow_mut().push(program.clone()),
    );

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/boxed_callable_cps_sharing.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/boxed_callable_cps_sharing.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    settle_native_product(&mut compiler, root_id);
    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should preserve reducer behavior when the same boxed surface captures different predicates: {outcome:?}; diagnostic={message}"
        );
    }

    let make_reducer_id = function_id(&functions, "make_reducer", 1);
    let predicate_functions = HashSet::from([
        function_id(&functions, "gt2", 1).as_u32(),
        function_id(&functions, "even", 1).as_u32(),
    ]);
    let reducer_id = generated_functions_owned_by(&functions, make_reducer_id)
        .into_iter()
        .find(|record| record.arity == 2)
        .expect("make_reducer/1 should generate the reducer lambda")
        .function_id;

    let mut unshared_program = before_sharing
        .borrow()
        .last()
        .cloned()
        .expect("native lowering should expose its complete graph before physical sharing");
    let unshared_reducers = unshared_program
        .executable_entries
        .iter()
        .filter(|entry| entry.key.activation.function == reducer_id)
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        unshared_reducers
            .iter()
            .map(|entry| entry.fn_id)
            .collect::<HashSet<_>>()
            .len(),
        2,
        "the comparison proof must begin with distinct physical reducer graphs",
    );
    let left_graph = unshared_program.native_graph_fn_ids(&unshared_reducers[0].key);
    let right_graph = unshared_program.native_graph_fn_ids(&unshared_reducers[1].key);
    assert!(
        left_graph.len() > 1 && left_graph.len() == right_graph.len() && left_graph.is_disjoint(&right_graph),
        "the distinct proof pair must include equally sized, disjoint owned continuation graphs",
    );
    let body = |fn_id| {
        unshared_program
            .bodies
            .iter()
            .find(|body| body.fn_id == fn_id)
            .expect("executable native body")
    };
    let left_body = body(unshared_reducers[0].fn_id);
    let right_body = body(unshared_reducers[1].fn_id);
    let differing_value_types = left_body
        .value_types
        .iter()
        .filter_map(|(var, left_ty)| (right_body.value_types.get(var) != Some(left_ty)).then_some(*var))
        .collect::<HashSet<_>>();
    let left_callee_only = crate::compiler2::artifact::indirect_callee_only_vars(
        unshared_program.module.fn_by_id(unshared_reducers[0].fn_id),
    );
    let right_callee_only = crate::compiler2::artifact::indirect_callee_only_vars(
        unshared_program.module.fn_by_id(unshared_reducers[1].fn_id),
    );
    assert!(
        !differing_value_types.is_empty()
            && differing_value_types.iter().all(|var| {
                left_callee_only.contains(var)
                    && right_callee_only.contains(var)
                    && left_body.block_param_reprs.get(var) == Some(&AbiValueRepr::ValueRef)
                    && right_body.block_param_reprs.get(var) == Some(&AbiValueRepr::ValueRef)
            }),
        "the positive pair must exercise only the proven ValueRef indirect-callee type exception",
    );
    assert!(
        unshared_program.native_cps_graphs_equivalent(&unshared_reducers[0].key, &unshared_reducers[1].key),
        "the distinct boxed reducer and full continuation graphs should normalize as equivalent",
    );
    let mut opposite_construction_order = unshared_program.clone();
    opposite_construction_order.bodies.reverse();
    opposite_construction_order.module.fns.reverse();
    opposite_construction_order.module.fn_idx = opposite_construction_order
        .module
        .fns
        .iter()
        .enumerate()
        .map(|(index, function)| (function.id, index))
        .collect();
    assert!(
        opposite_construction_order.native_cps_graphs_equivalent(&unshared_reducers[0].key, &unshared_reducers[1].key),
        "structurally equal graphs must compare equally after opposite body construction order",
    );
    let mut broken_structure = unshared_program.clone();
    let mut detached = None;
    'functions: for function in &mut broken_structure.module.fns {
        if !right_graph.contains(&function.id) {
            continue;
        }
        for block in &mut function.blocks {
            let continuation = match &mut block.terminator {
                IrTerm::Call { continuation, .. } | IrTerm::CallClosure { continuation, .. } => {
                    Some(&mut continuation.fn_id)
                }
                _ => None,
            };
            if let Some(continuation) = continuation.filter(|continuation| right_graph.contains(continuation)) {
                detached = Some(*continuation);
                *continuation = unshared_reducers[0].fn_id;
                break 'functions;
            }
        }
    }
    let detached = detached.expect("the structural-role control needs a continuation control edge in the right graph");
    assert!(
        !broken_structure.native_cps_graphs_equivalent(&unshared_reducers[0].key, &unshared_reducers[1].key),
        "an owned continuation detached from the completed IR control graph must make sharing ineligible",
    );
    broken_structure.deduplicate_equivalent_sibling_graphs();
    assert_eq!(
        unshared_reducers
            .iter()
            .map(|entry| broken_structure.executable_fn(&entry.key).expect("reducer executable"))
            .collect::<HashSet<_>>()
            .len(),
        2,
        "an incomplete ownership graph must not enter equivalence during the sharing fixed point",
    );
    let detached_owner = broken_structure
        .bodies
        .iter()
        .find_map(|body| {
            (body.fn_id == detached).then(|| match body.origin {
                NativeBodyOrigin::Continuation { owner } => owner,
                _ => panic!("the detached body must remain a continuation"),
            })
        })
        .expect("an ineligible continuation must not be removed by an unrelated representative remap");
    assert!(
        broken_structure.module.fn_idx.contains_key(&detached)
            && broken_structure.module.fn_idx.contains_key(&detached_owner),
        "an ineligible continuation and its owner must remain internally valid after other graph remaps",
    );
    let representative = unshared_reducers[0].fn_id;
    let sharing_work = unshared_program.deduplicate_equivalent_sibling_graphs();
    assert_eq!(
        sharing_work,
        NativeGraphSharingWork {
            passes: 2,
            indexed_bodies: 95,
            owned_graph_bodies: 84,
            graph_comparisons: 3,
            body_comparisons: 7,
        },
        "sharing work must be a deterministic function of indexed graph ownership",
    );
    assert!(
        unshared_reducers
            .iter()
            .all(|entry| unshared_program.executable_fn(&entry.key) == Some(representative)),
        "fixed-point sharing should deterministically retain the first semantic entry's physical graph",
    );
    assert!(
        left_graph
            .iter()
            .all(|fn_id| unshared_program.module.fn_idx.contains_key(fn_id))
            && right_graph
                .iter()
                .all(|fn_id| !unshared_program.module.fn_idx.contains_key(fn_id)),
        "sharing must retain every representative continuation and remove every redundant continuation",
    );
    assert!(
        unshared_program.bodies.iter().all(|body| match body.origin {
            NativeBodyOrigin::Continuation { owner } => unshared_program.module.fn_idx.contains_key(&owner),
            _ => true,
        }),
        "representative remapping must not leave any retained continuation with a removed owner",
    );

    let program = native.last(root_id).program;
    let reducer_executables = program
        .executable_entries
        .iter()
        .filter(|entry| entry.key.activation.function == reducer_id)
        .collect::<Vec<_>>();
    let types = compiler.types_for_test();
    assert!(
        reducer_executables
            .iter()
            .all(|entry| entry.key.activation.input_len(types) != 0),
        "the reducer executable should still carry a captured predicate identity lane",
    );

    let capture_identities = reducer_executables
        .iter()
        .map(|entry| entry.key.activation.inputs(types)[..1].to_vec())
        .collect::<HashSet<_>>();
    assert_eq!(
        capture_identities.len(),
        2,
        "the reducer lambda should preserve both semantic activation identities",
    );
    assert_eq!(
        reducer_executables
            .iter()
            .map(|entry| entry.fn_id)
            .collect::<HashSet<_>>()
            .len(),
        1,
        "equivalent boxed reducer activations should share one native body graph",
    );
    let predicate_words = program
        .callable_boundaries
        .iter()
        .filter(|boundary| {
            boundary
                .shape
                .as_ref()
                .is_some_and(|shape| predicate_functions.contains(&shape.target.0))
        })
        .map(|boundary| boundary.identity_fn)
        .collect::<HashSet<_>>();
    assert_eq!(
        predicate_words.len(),
        2,
        "even and gt2 must keep distinct runtime construction words",
    );
    let emitted_predicate_words = program
        .module
        .fns
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.stmts)
        .filter_map(|stmt| match stmt {
            IrStmt::Let(_, IrPrim::MakeFnRef(_, identity_fn) | IrPrim::MakeClosure(_, identity_fn, _))
                if predicate_words.contains(identity_fn) =>
            {
                Some(*identity_fn)
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        emitted_predicate_words, predicate_words,
        "sharing reducer code must not merge the predicate construction words it dispatches through",
    );
    let reducer_graph = program.native_graph_fn_ids(&reducer_executables[0].key);
    assert_eq!(
        reducer_graph
            .iter()
            .flat_map(|fn_id| &program.module.fn_by_id(*fn_id).blocks)
            .filter(|block| matches!(
                block.terminator,
                IrTerm::CallClosure { .. } | IrTerm::TailCallClosure { .. }
            ))
            .count(),
        1,
        "the shared reducer graph must still invoke its captured predicate through the boxed callable word",
    );
}

#[test]
fn compiler2_native_program_keeps_direct_callable_specializations_inequivalent() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/direct_callable_capture_identity.fz".to_string()),
        text: r#"
fn double(n), do: n * 2
fn triple(n), do: n * 3
fn mk(g), do: fn (n) -> g.(n) end
fn main(), do: mk(double).(4) + mk(triple).(4)
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!("direct callable control should lower: {outcome:?}; diagnostic={message}");
    }

    let mk_id = function_id(&functions, "mk", 1);
    let double_id = function_id(&functions, "double", 1);
    let triple_id = function_id(&functions, "triple", 1);
    let lambda_id = generated_functions_owned_by(&functions, mk_id)
        .into_iter()
        .find(|record| record.arity == 1)
        .expect("mk/1 should generate its returned lambda")
        .function_id;
    let program = native.last(root_id).program;
    let lambda_executables = program
        .executable_entries
        .iter()
        .filter(|entry| entry.key.activation.function == lambda_id)
        .collect::<Vec<_>>();
    assert_eq!(
        lambda_executables.len(),
        2,
        "double and triple should mint two semantic activations"
    );
    assert!(
        !program.native_cps_graphs_equivalent(&lambda_executables[0].key, &lambda_executables[1].key),
        "the direct-carrier lambda bodies ground to different call targets and must remain inequivalent",
    );
    assert_eq!(
        lambda_executables
            .iter()
            .map(|entry| entry.fn_id)
            .collect::<HashSet<_>>()
            .len(),
        2,
        "inequivalent direct specializations must retain separate native bodies",
    );
    let direct_target = |entry: &crate::compiler2::artifact::NativeExecutableEntry| {
        program
            .native_graph_fn_ids(&entry.key)
            .into_iter()
            .flat_map(|fn_id| program.module.fn_by_id(fn_id).blocks.iter())
            .filter_map(|block| match block.terminator {
                IrTerm::Call {
                    callee: crate::fz_ir::DirectCallTarget::Local(target),
                    ..
                }
                | IrTerm::TailCall {
                    callee: crate::fz_ir::DirectCallTarget::Local(target),
                    ..
                } => Some(target),
                _ => None,
            })
            .find(|target| {
                program.executable_entries.iter().any(|candidate| {
                    candidate.fn_id == *target
                        && matches!(candidate.key.activation.function, function if function == double_id || function == triple_id)
                })
            })
            .expect("each direct-carrier lambda should ground its captured call")
    };
    let grounded_targets = lambda_executables
        .iter()
        .map(|entry| direct_target(entry))
        .collect::<HashSet<_>>();
    let expected_targets = program
        .executable_entries
        .iter()
        .filter(
            |entry| matches!(entry.key.activation.function, function if function == double_id || function == triple_id),
        )
        .map(|entry| entry.fn_id)
        .collect::<HashSet<_>>();
    assert_eq!(
        grounded_targets, expected_targets,
        "double and triple must remain distinct grounded direct targets",
    );
}

/// Regenerate `.agent/measurements/fz-kdt.163-native-cps-sharing.txt` with:
///
/// `cargo test --lib compiler2::drive_test::measure_native_cps_sharing_corpus -- --ignored --exact --nocapture`
#[test]
#[ignore = "full-corpus fz-kdt.163 native CPS sharing census"]
fn measure_native_cps_sharing_corpus() {
    #[derive(Default, Debug)]
    struct Totals {
        candidates: usize,
        resolved: usize,
        codegen_pairs: usize,
        semantic_executables: usize,
        before_physical_executables: usize,
        after_physical_executables: usize,
        sibling_groups: usize,
        equivalent_groups: usize,
        redundant_executables: usize,
        before_bodies: usize,
        after_bodies: usize,
        before_continuations: usize,
        after_continuations: usize,
        before_native_bytes: usize,
        after_native_bytes: usize,
        before_constructions: usize,
        after_constructions: usize,
        before_codegen_millis: u128,
        after_codegen_millis: u128,
        sharing_passes: usize,
        indexed_bodies: usize,
        owned_graph_bodies: usize,
        graph_comparisons: usize,
        body_comparisons: usize,
        sharing_micros: u128,
    }
    #[derive(Debug)]
    struct Mover {
        fixture: String,
        initial_classes: usize,
        initially_redundant_roots: usize,
        removed_roots: usize,
        removed_bodies: usize,
        removed_native_bytes: usize,
    }

    let mut paths = ["fixtures2", "fixtures2/behavior"]
        .into_iter()
        .flat_map(|directory| {
            std::fs::read_dir(directory)
                .unwrap_or_else(|error| panic!("read {directory}: {error}"))
                .map(|entry| entry.expect("fixture directory entry").path())
        })
        .filter(|path| path.extension().is_some_and(|extension| extension == "fz"))
        .collect::<Vec<_>>();
    paths.sort();

    let mut totals = Totals::default();
    let mut drive_panics = Vec::new();
    let mut unresolved = Vec::new();
    let mut codegen_failures = Vec::new();
    let mut movers = Vec::new();
    for path in paths {
        let source = std::fs::read_to_string(&path).expect("fixture source");
        if !source.contains("fn main()") {
            continue;
        }
        totals.candidates += 1;

        let tel = ConfiguredTelemetry::new();
        let before_sharing = Rc::new(RefCell::new(Vec::<NativeProgram>::new()));
        let before_sharing_sink = Rc::clone(&before_sharing);
        tel.attach_raw_event2::<crate::compiler2::RootId, NativeProgram, _>(
            &["fz", "compiler2", "native_program", "before_sharing"],
            move |_, _, _, _, program| before_sharing_sink.borrow_mut().push(program.clone()),
        );
        let after_sharing = NativeProgramCapture::new();
        after_sharing.install(&tel);
        let compiled_bytes = Rc::new(RefCell::new(HashMap::<FnId, usize>::new()));
        let compiling_functions = Rc::new(RefCell::new(HashMap::<u64, FnId>::new()));
        let compiling_functions_start = Rc::clone(&compiling_functions);
        let compiling_functions_stop = Rc::clone(&compiling_functions);
        let compiled_bytes_sink = Rc::clone(&compiled_bytes);
        tel.attach_raw_span1_1::<FnId, cranelift_codegen::Context, _, _, _>(
            &["fz", "codegen", "define_function"],
            move |_, span_id, _, fn_id| {
                compiling_functions_start.borrow_mut().insert(span_id, *fn_id);
            },
            move |_, span_id, _, _, context| {
                if let Some(code) = context.compiled_code() {
                    let fn_id = compiling_functions_stop
                        .borrow_mut()
                        .remove(&span_id)
                        .expect("define stop should pair with its function start");
                    compiled_bytes_sink.borrow_mut().insert(fn_id, code.code_buffer().len());
                }
            },
            |_, _, _, _| {},
        );

        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some(path.display().to_string()),
            text: source,
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        settle_native_product(&mut compiler, root);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| compiler.drive()));
        let Ok(outcome) = outcome else {
            drive_panics.push(path.display().to_string());
            continue;
        };
        if !matches!(outcome, DriveOutcome::Resolved) {
            unresolved.push((path.display().to_string(), format!("{outcome:?}")));
            continue;
        }
        totals.resolved += 1;
        let before = before_sharing
            .borrow()
            .last()
            .cloned()
            .expect("pre-sharing native program");
        let after = after_sharing.last(root).program;
        let mut reproduced = before.clone();
        let sharing_started = std::time::Instant::now();
        let sharing_work = reproduced.deduplicate_equivalent_sibling_graphs();
        totals.sharing_micros += sharing_started.elapsed().as_micros();
        totals.sharing_passes += sharing_work.passes;
        totals.indexed_bodies += sharing_work.indexed_bodies;
        totals.owned_graph_bodies += sharing_work.owned_graph_bodies;
        totals.graph_comparisons += sharing_work.graph_comparisons;
        totals.body_comparisons += sharing_work.body_comparisons;
        assert_eq!(reproduced.entry, after.entry);
        assert_eq!(reproduced.executable_entries, after.executable_entries);
        assert_eq!(reproduced.bodies, after.bodies);
        assert_eq!(reproduced.callable_boundaries, after.callable_boundaries);
        assert_eq!(reproduced.module.fns, after.module.fns);
        assert_eq!(
            before
                .executable_entries
                .iter()
                .map(|entry| &entry.key)
                .collect::<Vec<_>>(),
            after
                .executable_entries
                .iter()
                .map(|entry| &entry.key)
                .collect::<Vec<_>>(),
            "physical sharing must preserve the semantic executable inventory",
        );

        let count_constructions = |program: &NativeProgram| {
            program
                .module
                .fns
                .iter()
                .flat_map(|function| &function.blocks)
                .flat_map(|block| &block.stmts)
                .filter(|stmt| matches!(stmt, IrStmt::Let(_, IrPrim::MakeClosure(..))))
                .count()
        };
        let before_physical_executables = before
            .executable_entries
            .iter()
            .map(|entry| entry.fn_id)
            .collect::<HashSet<_>>()
            .len();
        let after_physical_executables = after
            .executable_entries
            .iter()
            .map(|entry| entry.fn_id)
            .collect::<HashSet<_>>()
            .len();
        totals.semantic_executables += after.executable_entries.len();
        totals.before_physical_executables += before_physical_executables;
        totals.after_physical_executables += after_physical_executables;
        totals.before_bodies += before.bodies.len();
        totals.after_bodies += after.bodies.len();
        totals.before_continuations += before
            .bodies
            .iter()
            .filter(|body| matches!(body.origin, NativeBodyOrigin::Continuation { .. }))
            .count();
        totals.after_continuations += after
            .bodies
            .iter()
            .filter(|body| matches!(body.origin, NativeBodyOrigin::Continuation { .. }))
            .count();
        totals.before_constructions += count_constructions(&before);
        totals.after_constructions += count_constructions(&after);

        let mut siblings = HashMap::<FunctionId, Vec<&crate::compiler2::artifact::NativeExecutableEntry>>::new();
        for entry in &before.executable_entries {
            siblings.entry(entry.key.activation.function).or_default().push(entry);
        }
        let mut fixture_groups = 0;
        let mut fixture_redundant = 0;
        for entries in siblings.values().filter(|entries| entries.len() > 1) {
            totals.sibling_groups += 1;
            let mut classes: Vec<Vec<&crate::compiler2::artifact::NativeExecutableEntry>> = Vec::new();
            for entry in entries {
                if let Some(class) = classes
                    .iter_mut()
                    .find(|class| before.native_cps_graphs_equivalent(&class[0].key, &entry.key))
                {
                    class.push(entry);
                } else {
                    classes.push(vec![entry]);
                }
            }
            for class in classes.into_iter().filter(|class| class.len() > 1) {
                totals.equivalent_groups += 1;
                totals.redundant_executables += class.len() - 1;
                fixture_groups += 1;
                fixture_redundant += class.len() - 1;
            }
        }

        let mut compile = |label: &str, program: &NativeProgram| {
            compiled_bytes.borrow_mut().clear();
            let started = std::time::Instant::now();
            let result = compiler.compile_native_program_jit_for_test(program);
            let elapsed = started.elapsed().as_millis();
            let bytes = compiled_bytes.borrow().values().sum::<usize>();
            if result.is_err() {
                codegen_failures.push((path.display().to_string(), label.to_string()));
            }
            (result.is_ok(), bytes, elapsed)
        };
        let (before_ok, before_bytes, before_millis) = compile("before", &before);
        let (after_ok, after_bytes, after_millis) = compile("after", &after);
        if before_ok && after_ok {
            totals.codegen_pairs += 1;
            totals.before_native_bytes += before_bytes;
            totals.after_native_bytes += after_bytes;
            totals.before_codegen_millis += before_millis;
            totals.after_codegen_millis += after_millis;
        }
        if fixture_groups != 0 {
            movers.push(Mover {
                fixture: path.display().to_string(),
                initial_classes: fixture_groups,
                initially_redundant_roots: fixture_redundant,
                removed_roots: before_physical_executables - after_physical_executables,
                removed_bodies: before.bodies.len() - after.bodies.len(),
                removed_native_bytes: before_bytes.saturating_sub(after_bytes),
            });
        }
    }

    let mover_lines = movers
        .iter()
        .map(|mover| {
            format!(
                "{}: initial_classes={} initially_redundant_roots={} removed_roots={} removed_bodies={} removed_native_bytes={}",
                mover.fixture,
                mover.initial_classes,
                mover.initially_redundant_roots,
                mover.removed_roots,
                mover.removed_bodies,
                mover.removed_native_bytes,
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    eprintln!(
        "fz-kdt.163 census: {totals:#?}\ndrive_panics={drive_panics:#?}\nunresolved={unresolved:#?}\ncodegen_failures={codegen_failures:#?}\nmovers:\n{mover_lines}"
    );
}

#[test]
fn compiler2_native_program_joins_callable_resume_before_materializing_closure_call() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/opaque_fn_value_join.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!("opaque joined function values should settle before native lowering: {outcome:?}; diagnostic={message}");
    }

    let add_a_id = function_id(&functions, "add_a", 2);
    let add_b_id = function_id(&functions, "add_b", 2);
    let program = native.last(root_id).program;
    let callable_functions = program
        .callable_boundaries
        .iter()
        .flat_map(|boundary| boundary.members.iter())
        .map(|member| member.target.activation.function)
        .collect::<HashSet<_>>();
    assert!(
        callable_functions.contains(&add_a_id) && callable_functions.contains(&add_b_id),
        "native callable inventory should include both concrete functions flowing through the case join",
    );

    assert!(
        native_closure_call_count(&program) > 0,
        "opaque joined function values should stay explicit closure-call seams instead of collapsing to direct calls",
    );
}

#[test]
fn compiler2_opaque_callable_each_uses_a_boxed_return_boundary() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/opaque_fn_each_discarded_return.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/opaque_fn_each_discarded_return.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(compiler.drive(), "opaque mapper should lower");
    let each_a_id = function_id(&functions, "each_a", 1);
    let each_b_id = function_id(&functions, "each_b", 1);
    let program = native.last(root_id).program;
    let boundaries = program
        .callable_boundaries
        .iter()
        .filter(|boundary| {
            boundary
                .members
                .iter()
                .any(|member| [each_a_id, each_b_id].contains(&member.target.activation.function))
        })
        .collect::<Vec<_>>();
    let boundary_ids = boundaries.iter().map(|boundary| boundary.id).collect::<HashSet<_>>();
    let member_functions = boundaries
        .iter()
        .flat_map(|boundary| boundary.members.iter())
        .map(|member| member.target.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(boundary_ids.len(), 2);
    assert_eq!(member_functions, HashSet::from([each_a_id, each_b_id]));
    // `Enum.each` throws the mapper's result away, but these members are
    // reached through the boxed apply seam, whose wrapper always hands a value
    // back. The member's own return has to supply it, so it carries the one
    // boxed lane the wrapper returns -- the caller drops it (fz-kdt.155).
    assert!(boundaries.iter().all(|boundary| {
        boundary
            .members
            .iter()
            .all(|member| member.target_return.layout.reprs.len() == 1)
    }));
    assert!(
        native_closure_call_count(&program) > 0,
        "opaque each callables should dispatch through indirect closure-call seams",
    );
    for boundary in &boundaries {
        let wrapper = program
            .module
            .fns
            .iter()
            .find(|function| function.id == boundary.wrapper_fn)
            .expect("boxed-return boundary wrapper");
        assert!(wrapper.blocks.iter().all(|block| {
            matches!(
                block.terminator,
                IrTerm::Call {
                    callee: crate::fz_ir::DirectCallTarget::Local(_),
                    ..
                }
            )
        }));
    }
    compiler.run_root_interp(root_id).unwrap();
    compiler.run_root_jit(root_id).unwrap();
    assert_eq!(dbg.lines().as_slice(), ["1", "2", "3", "1", "2", "3"]);
}

// This test used to pin the all-divergent callable boundary's lowering and
// runtime fate (no continuation, function_clause halt).
// Kernel arithmetic contracts reject the program outright now: every join
// member's body adds `1`/`2` to `:bad`, each a provable spec violation at a
// user callsite, so compilation fails before lowering and no output escapes
// on any path.
#[test]
fn compiler2_all_divergent_public_callable_is_rejected_at_compile_time() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/opaque_fn_all_divergent.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/opaque_fn_all_divergent.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "an all-divergent callable built from ill-typed arithmetic must reject at compile time"
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("the ill-typed join members should surface as a diagnostic");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::SPEC_VIOLATION.0);
    assert!(dbg.lines().is_empty(), "no output may escape a rejected program");
}

#[test]
fn compiler2_mixed_public_callable_adapts_only_its_returning_member() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/opaque_fn_mixed_return.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/opaque_fn_mixed_return.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(compiler.drive(), "mixed public callable should lower");

    let program = native.last(root_id).program;
    let boundary = program
        .callable_boundaries
        .iter()
        .find(|boundary| {
            boundary.members.len() == 2
                && boundary
                    .members
                    .iter()
                    .filter(|member| member.target_return.diverges)
                    .count()
                    == 1
        })
        .expect("mixed returning/divergent callable boundary");
    let wrapper = program
        .module
        .fns
        .iter()
        .find(|function| function.id == boundary.wrapper_fn)
        .expect("mixed callable wrapper");
    assert_eq!(
        program
            .bodies
            .iter()
            .filter(|body| {
                matches!(&body.origin, NativeBodyOrigin::Continuation { owner, .. } if *owner == boundary.wrapper_fn)
            })
            .count(),
        1
    );
    for member in &boundary.members {
        let has_call = wrapper.blocks.iter().any(|block| {
            matches!(
                block.terminator,
                IrTerm::Call {
                    callee: crate::fz_ir::DirectCallTarget::Local(target),
                    ..
                } if target == member.target_fn
            )
        });
        let has_tail_call = wrapper.blocks.iter().any(|block| {
            matches!(
                block.terminator,
                IrTerm::TailCall {
                    callee: crate::fz_ir::DirectCallTarget::Local(target),
                    ..
                } if target == member.target_fn
            )
        });
        assert_eq!(
            (has_call, has_tail_call),
            (!member.target_return.diverges, member.target_return.diverges)
        );
    }
    compiler.run_root_interp(root_id).unwrap();
    compiler.run_root_jit(root_id).unwrap();
    assert_eq!(dbg.lines().as_slice(), ["2", "2"]);
}

#[test]
fn compiler2_native_program_marks_settled_singleton_closure_flows_with_exact_targets() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/closure_typed_captures.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/closure_typed_captures.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "settled singleton closure values should lower with an explicit exact direct target: {outcome:?}; diagnostic={message}"
        );
    }

    let add_to_id = function_id(&functions, "add_to", 2);
    let lambda_id = generated_functions_owned_by(&functions, add_to_id)
        .into_iter()
        .find(|record| record.arity == 1)
        .expect("add_to/2 should generate the singleton closure body")
        .function_id;
    let program = native.last(root_id).program;
    assert!(
        native_exact_call_targets(&program)
            .into_iter()
            .filter_map(|fn_id| {
                program.bodies.iter().find_map(|body| match &body.origin {
                    NativeBodyOrigin::Executable(key) if body.fn_id == fn_id => Some(key.activation.function),
                    _ => None,
                })
            })
            .any(|function| function == lambda_id),
        "singleton closure flows should carry the exact generated lambda target through native lowering, even when the closure call itself collapses to a direct call",
    );
}

#[test]
fn compiler2_native_codegen_keeps_callable_boundary_surface_authoritative_for_range_reduce_bridge() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/fz_f98_range_reduce_scalar.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/fz_f98_range_reduce_scalar.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Range reduce scalar bridge should settle before native codegen consumes it: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    // The defect this test used to guard -- a closure call re-inferring a
    // boundary wrapper's surface through a `direct_target` hint -- became
    // unrepresentable when that field was deleted: a `CallClosure` term is
    // indirect by construction and the boundary owns its surface. What
    // remains observable is that the bridge settles and codegen consumes
    // the boundary-owned program.
    jit_compile_native_program(&mut compiler, &program);
}

#[test]
fn compiler2_interp_runs_range_reduce_scalar_bridge_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/fz_f98_range_reduce_scalar.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/fz_f98_range_reduce_scalar.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = dbg.lines().join("\n");
        panic!(
            "Compiler2 backend interpreter should run the Range reduce scalar bridge fixture: {error}; dbg={diagnostic}"
        );
    });
    assert_eq!(
        dbg.lines().as_slice(),
        ["6", "{6, 3}"],
        "Range Enum.reduce/3 should keep scalar and tuple accumulator calls on the settled callable boundary",
    );
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_jit_runs_range_reduce_scalar_bridge_from_native_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/fz_f98_range_reduce_scalar.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/fz_f98_range_reduce_scalar.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler
        .run_root_jit(root_id)
        .unwrap_or_else(|error| panic!("Compiler2 JIT should run the Range reduce scalar bridge: {error}"));
    assert_eq!(
        dbg.lines().as_slice(),
        ["6", "{6, 3}"],
        "Range Enum.reduce/3 should adapt the callable wrapper's boxed result at the native caller seam",
    );
}

#[test]
fn compiler2_interp_runs_range_reduce2_first_acc_bridge_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/fz_f98_range_reduce2.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/fz_f98_range_reduce2.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = dbg.lines().join("\n");
        panic!("Compiler2 backend interpreter should run Range Enum.reduce/2: {error}; dbg={diagnostic}");
    });
    assert_eq!(
        dbg.lines().as_slice(),
        ["105"],
        "Range Enum.reduce/2 should thread the :first | {{:acc, value}} state through the bridge",
    );
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_jit_runs_range_reduce2_first_acc_bridge_from_native_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/fz_f98_range_reduce2.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/fz_f98_range_reduce2.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler
        .run_root_jit(root_id)
        .unwrap_or_else(|error| panic!("Compiler2 JIT should run Range Enum.reduce/2: {error}"));
    assert_eq!(
        dbg.lines().as_slice(),
        ["105"],
        "Range Enum.reduce/2 should keep the first-accumulator bridge valid on the native path",
    );
}

#[test]
fn compiler2_interp_preserves_range_reduce3_halt_and_suspend_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/range_reduce3_halt_suspend.fz".to_string()),
        text: r#"
fn main() do
  dbg(Enumerable.reduce(1..5, {:cont, 0}, fn (x, acc) ->
    if x > 2 do
      {:halt, acc}
    else
      {:cont, acc + x}
    end
  end))
  dbg(Enumerable.reduce(1..5, {:suspend, 9}, fn (x, acc) -> {:cont, acc + x} end))
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler
        .run_root_interp(root_id)
        .unwrap_or_else(|error| panic!("Compiler2 interpreter should preserve Range reduce/3 commands: {error}"));
    let lines = dbg.lines();
    assert_eq!(lines.first().map(String::as_str), Some("{:halted, 3}"));
    assert!(
        lines
            .get(1)
            .is_some_and(|line| line.starts_with("{:suspended, 9, #fn<")),
        "Range reduce/3 suspend should preserve the initial accumulator and continuation, got {lines:?}",
    );
}

#[test]
fn compiler2_jit_preserves_range_reduce3_halt_and_suspend_from_native_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/range_reduce3_halt_suspend.fz".to_string()),
        text: r#"
fn main() do
  dbg(Enumerable.reduce(1..5, {:cont, 0}, fn (x, acc) ->
    if x > 2 do
      {:halt, acc}
    else
      {:cont, acc + x}
    end
  end))
  dbg(Enumerable.reduce(1..5, {:suspend, 9}, fn (x, acc) -> {:cont, acc + x} end))
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler
        .run_root_jit(root_id)
        .unwrap_or_else(|error| panic!("Compiler2 JIT should preserve Range reduce/3 commands: {error}"));
    let lines = dbg.lines();
    assert_eq!(lines.first().map(String::as_str), Some("{:halted, 3}"));
    assert!(
        lines
            .get(1)
            .is_some_and(|line| line.starts_with("{:suspended, 9, #fn<")),
        "Range reduce/3 suspend should preserve the initial accumulator and continuation, got {lines:?}",
    );
}

#[test]
fn compiler2_interp_runs_range_and_map_to_list_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/fz_f98_range_map_converges.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/fz_f98_range_map_converges.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = dbg.lines().join("\n");
        panic!(
            "Compiler2 backend interpreter should run Range and Map Enum.to_list through protocol dispatch: {error}; dbg={diagnostic}"
        );
    });
    assert_eq!(
        dbg.lines().as_slice(),
        ["[1, 3, 5, 7]", "[{1, :a}]"],
        "Range and Map Enum.to_list calls should keep their protocol impl identities distinct",
    );
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_runtime_demand_settles_the_f98_orbit_fixture_without_cycling() {
    let tel = ConfiguredTelemetry::new();
    let derivations = Rc::new(RefCell::new(Vec::<ExecutableKey>::new()));
    let derivation_sink = Rc::clone(&derivations);
    tel.attach_raw_event2::<World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _, completion| {
            if let Job::DeriveRuntimeDemand(executable) = &completion.job {
                derivation_sink.borrow_mut().push(executable.clone());
            }
        },
    );
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/fz_f98_range_map_converges.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/fz_f98_range_map_converges.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root_id)
        .expect("the orbit fixture should settle and run");
    assert_eq!(dbg.lines().as_slice(), ["[1, 3, 5, 7]", "[{1, :a}]"]);

    let derivations = derivations.borrow();
    let distinct_executables = derivations.iter().collect::<HashSet<_>>();
    assert!(
        distinct_executables.len() >= 8,
        "the fixture should exercise a nontrivial RuntimeDemand fact graph, got {} executables",
        distinct_executables.len(),
    );
    for executable in distinct_executables {
        let fact = FactKey::RuntimeDemand(executable.clone());
        assert!(compiler.world().fact_is_settled(&fact), "{fact:?} must settle");
        assert!(
            compiler.world().runtime_demand(executable).is_some(),
            "{fact:?} must have a value"
        );
    }
}

#[test]
fn compiler2_native_program_preserves_variadic_extern_wrappers_and_marshals() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/variadic_open_compiler2.fz".to_string()),
        text: include_str!("../../fixtures2/00013_variadic_open.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should preserve the settled variadic extern wrapper and wire classes: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let open_id = function_id(&functions, "libc::open", 2);
    let body = native_executable_body(&program, open_id);
    assert_eq!(
        program.module.externs.len(),
        1,
        "native lowering should publish one extern declaration for libc::open"
    );
    let decl = &program.module.externs[0];
    assert_eq!(decl.symbol, "open");
    assert_eq!(decl.params, vec![ExternTy::CString, ExternTy::I64]);
    assert!(decl.variadic);
    assert_eq!(decl.ret, ExternTy::I64);
    assert_eq!(
        sorted_extern_marshals(body),
        vec![ExternTy::CString, ExternTy::I64, ExternTy::I64],
        "native extern wrapper bodies should carry the exact settled C wire classes for a variadic site",
    );
}

#[test]
fn compiler2_native_program_jit_runs_quicksort_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00020_quicksort_jit_entry.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "entry".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle before compiler2-owned codegen consumes quicksort: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let halt = compiled.run_with_output(compiler.telemetry(), &dbg, program.entry);
    assert_eq!(
        halt, 42,
        "compiler2-owned native codegen should preserve the Compiler2 quicksort entry result"
    );
    assert_eq!(
        dbg.lines().first().map(String::as_str),
        Some("[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]"),
        "compiler2-owned native codegen should preserve Compiler2 quicksort dbg output",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native quicksort JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_native_codegen_brackets_every_phase_under_one_compile_span() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let code_bytes = Rc::new(RefCell::new(Vec::new()));
    let code_bytes_sink = Rc::clone(&code_bytes);
    tel.attach_raw_span1_1::<crate::fz_ir::FnId, cranelift_codegen::Context, _, _, _>(
        &["fz", "codegen", "define_function"],
        |_, _, _, _| {},
        move |_, _, _, _, context| {
            let Some(code) = context.compiled_code() else {
                return;
            };
            code_bytes_sink.borrow_mut().push(code.code_buffer().len());
        },
        |_, _, _, _| {},
    );

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_entry.fz".to_string()),
        text: include_str!("../../fixtures2/00019_quicksort_entry.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "entry".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved),
        "native lowering should settle before codegen consumes it: {outcome:?}"
    );

    let program = native.last(root_id).program;
    let _compiled = jit_compile_native_program(&mut compiler, &program);

    // Intent: codegen telemetry mirrors the surface's own phase structure under
    // a single enclosing `compile` span. Because the bus threads parent linkage
    // from the open-span stack, every phase nests under `compile`, so wall time
    // accounts as compile = declare + per-spec(lower + define) + emit_runtime +
    // finalize, with no unattributed gaps left at the codegen layer.
    let starts = |name: &[&str]| {
        capture
            .find(name)
            .into_iter()
            .filter(|e| e.kind == EventKind::SpanStart)
            .collect::<Vec<_>>()
    };

    let compile = starts(&["fz", "codegen", "compile"]);
    assert_eq!(
        compile.len(),
        1,
        "exactly one enclosing codegen `compile` span per compile"
    );
    let compile_id = compile[0].span_id;

    for phase in [
        ["fz", "codegen", "declare"],
        ["fz", "codegen", "emit_runtime"],
        ["fz", "codegen", "finalize"],
    ] {
        let phase_starts = starts(&phase);
        assert_eq!(phase_starts.len(), 1, "phase {phase:?} is spanned exactly once");
        assert_eq!(
            phase_starts[0].parent_span_id, compile_id,
            "phase {phase:?} nests under the compile span"
        );
    }

    let lowered = starts(&["fz", "codegen", "lower_function"]);
    let defined = starts(&["fz", "codegen", "define_function"]);
    assert!(!lowered.is_empty(), "quicksort lowers at least one spec body");
    assert_eq!(
        lowered.len(),
        defined.len(),
        "every lowered spec is also native-compiled: one define per lower"
    );
    for span_start in lowered.iter().chain(defined.iter()) {
        assert_eq!(
            span_start.parent_span_id, compile_id,
            "per-spec codegen spans nest under the compile span"
        );
    }

    let define_stops = capture
        .find(&["fz", "codegen", "define_function"])
        .into_iter()
        .filter(|e| e.kind == EventKind::SpanStop)
        .collect::<Vec<_>>();
    assert_eq!(
        define_stops.len(),
        defined.len(),
        "each define span closes exactly once"
    );
    assert_eq!(code_bytes.borrow().len(), defined.len());
    assert!(code_bytes.borrow().iter().all(|bytes| *bytes >= 1));
}

#[test]
fn compiler2_null_telemetry_stays_concrete_through_frontdoors_and_runtimes() {
    crate::telemetry::jsonl::reset_codegen_projection_count();
    let mut compiler = Compiler2::new(NullTelemetry);
    compiler.submit_code(CodeSubmission {
        name: Some("null_telemetry_codegen.fz".to_string()),
        text: "fn main(), do: 42\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(
        compiler
            .run_root_interp(root)
            .expect("null-telemetry interpreter run should succeed"),
        42,
    );
    compiler
        .run_root_jit(root)
        .expect("null-telemetry native compile should succeed");
    assert_eq!(crate::telemetry::jsonl::codegen_projection_count(), 0);
    for source in [
        include_str!("native_codegen/function.rs"),
        include_str!("native_codegen/env.rs"),
        include_str!("native_codegen/prim.rs"),
        include_str!("native_codegen/support.rs"),
        include_str!("native_codegen/driver.rs"),
    ] {
        assert!(!source.contains("CodegenFnStats"));
        assert!(!source.contains("reusable_cons_candidate_count"));
        assert!(!source.contains("reusable_cons_consumed_count"));
    }
}

#[test]
fn compiler2_native_program_jit_runs_spawn_then_receive_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_spawn_then_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00016_spawn_then_receive.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle spawn+receive before compiler2-owned codegen consumes it: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let child_id = function_id(&functions, "child", 0);
    let spawn_id = function_id(&functions, "spawn", 1);
    let fz_spawn_id = function_id(&functions, "fz_spawn", 1);
    assert_eq!(
        native_executable_body(&program, spawn_id).param_reprs,
        vec![AbiValueRepr::ValueRef],
        "spawn/1 should accept callable values through the boxed closure-ref lane",
    );
    assert_eq!(
        native_executable_body(&program, fz_spawn_id).param_reprs,
        vec![AbiValueRepr::ValueRef],
        "fz_spawn/1 should preserve the boxed closure-ref lane at the extern seam",
    );
    let callable_targets = native_callable_boundary_uses(&program)
        .into_iter()
        .flat_map(|boundary_id| {
            program
                .callable_boundaries
                .iter()
                .find(|entry| entry.id() == boundary_id)
                .unwrap_or_else(|| {
                    panic!(
                        "native callable boundary {:?} missing from callable inventory",
                        boundary_id
                    )
                })
                .members
                .iter()
                .map(|member| member.target.activation.function)
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_targets,
        HashSet::from([child_id]),
        "native closure values should resolve to the one closed callable boundary for child/0",
    );

    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run(compiler.telemetry(), program.entry),
        42,
        "compiler2-owned native codegen should preserve Compiler2 spawn/receive behavior through the callable-entry seam",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native spawn/receive JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_spawned_tuple_return_uses_exact_member_lanes_and_task_halt_repr() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_spawn_tuple_return.fz".to_string()),
        text: r#"
fn child(parent) do
  send(parent, :ran)
  {1, 2}
end

fn main() do
  parent = self()
  spawn(fn () -> child(parent) end)
  receive do
    :ran -> 0
  end
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(compiler.drive(), "spawned tuple-returning closure should lower");

    let program = native.last(root_id).program;
    let boundary = program
        .callable_boundaries
        .iter()
        .find(|boundary| boundary.call_arity == 0)
        .expect("spawned zero-argument callable boundary");
    let [member] = boundary.members.as_ref() else {
        panic!("spawned zero-argument callable should have one exact member")
    };
    assert_eq!(
        member.target_return.layout.reprs.as_ref(),
        [AbiValueRepr::RawInt, AbiValueRepr::RawInt]
    );
    assert_eq!(boundary.task_halt_repr, Some(AbiValueRepr::RawInt));

    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(compiled.run(compiler.telemetry(), program.entry), 0);
}

#[test]
fn compiler2_native_program_jit_runs_spawn_receive_and_assert_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_spawn_receive_assert.fz".to_string()),
        text: include_str!("../../fixtures2/00017_spawn_receive_assert.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle spawn+receive+assert before compiler2-owned codegen consumes it: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run(compiler.telemetry(), program.entry),
        0,
        "compiler2-owned native codegen should preserve Compiler2 spawn/receive/assert behavior through the continuation seam",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native spawn/receive/assert JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_native_program_jit_runs_enum_reduce_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_runtime_graph.fz".to_string()),
        text: include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle before compiler2-owned codegen consumes Enum.reduce: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run(compiler.telemetry(), program.entry),
        15,
        "compiler2-owned native codegen should preserve the closed Enum.reduce result from Compiler2",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native Enum.reduce JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_native_program_jit_runs_enum_map_reduce_with_exact_reducer_lanes() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/enum_map_reduce_exact.fz".to_string()),
        text: "fn main() do\n  xs = [1, 2, 3, 4]\n  dbg(Enum.map_reduce(xs, 0, fn (x, acc) -> {x + acc, acc + x} end))\nend\n".to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle Enum.map_reduce before compiler2-owned codegen consumes direct reducer targets: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let _ = compiled.run_with_output(compiler.telemetry(), &dbg, program.entry);
    assert_eq!(
        dbg.lines(),
        vec!["{[1, 3, 6, 10], 10}".to_string()],
        "compiler2-owned native codegen should preserve Enum.map_reduce when exact reducer calls capture scalar lanes exactly",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native Enum.map_reduce JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_native_program_jit_runs_source_lambda_sugars_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/lambda_sugars.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/lambda_sugars.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle before compiler2-owned codegen consumes source lambda sugars: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    assert!(
        program.callable_boundaries.is_empty() && native_callable_boundary_uses(&program).is_empty(),
        "direct-only lambda sugars should stay out of native callable-boundary inventory when they never escape",
    );
    assert_eq!(
        native_closure_call_count(&program),
        0,
        "direct-only lambda sugars should lower every call as an exact direct call -- no indirect closure-call seam survives",
    );
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let _ = compiled.run_with_output(compiler.telemetry(), &dbg, program.entry);
    assert_eq!(
        dbg.lines(),
        vec!["42".to_string(), "{:zero, :pos, :other}".to_string()],
        "compiler2-owned native codegen should preserve capture and multi-clause lambda sugar behavior",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native source lambda sugar JIT should not reopen legacy planning or type inference",
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "Compiler2-native source lambda sugar JIT should not call the old frontend lowerer",
    );
}

#[test]
fn compiler2_native_program_jit_runs_variadic_extern_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/variadic_open_compiler2_jit.fz".to_string()),
        text: include_str!("../../fixtures2/00015_variadic_open_jit.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle before compiler2-owned codegen consumes variadic externs: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run(compiler.telemetry(), program.entry),
        -1,
        "compiler2-owned native codegen should preserve Compiler2 variadic extern calls and return the libc open error sentinel for a missing path",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native variadic extern JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_native_program_jit_runs_map_fixture_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/map_three_path_parity.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/map_three_path_parity.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle before compiler2-owned codegen consumes the map fixture: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let _compiled = jit_compile_native_program(&mut compiler, &program);
}

#[test]
fn compiler2_native_program_jit_keeps_tail_recursion_bounded() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/tail_recursion.fz".to_string()),
        text: include_str!("../../fixtures2/00018_tail_recursion.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 native lowering should settle before compiler2-owned codegen consumes tail recursion: {outcome:?}; diagnostic={message}"
        );
    }

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run(compiler.telemetry(), program.entry),
        100_000,
        "compiler2-owned native codegen should preserve Compiler2 tail recursion without stack growth",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native tail-recursive JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_cont_threaded_recursion_closes_with_a_back_edge() {
    // fz-rh2.25: count's recursion cycle is threaded through Call
    // continuations (count__clause_1 -Call-> kernel wrapper, whose cont
    // chain ends in a resume fn that TailCalls count's entry). A back-edge
    // graph built from TailCall edges alone cannot see that cycle, so the
    // closing tail call carried is_back_edge=false and the loop never spent
    // reductions — frame-flat starvation. The SCC graph must follow Call
    // callee and continuation edges too.
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/tail_recursion.fz".to_string()),
        text: include_str!("../../fixtures2/00018_tail_recursion.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(compiler.drive(), "tail recursion lowers to a native program");

    let program = native.last(root_id).program;
    let count_entry = program
        .module
        .fns
        .iter()
        .find(|function| function.name.starts_with("count__e"))
        .map(|function| function.id)
        .expect("count's entry fn is in the native module");
    let closing_back_edge = program.module.fns.iter().any(|function| {
        function.blocks.iter().any(|block| {
            matches!(
                &block.terminator,
                IrTerm::TailCall { callee, is_back_edge: true, .. }
                    if callee.local_fn_id() == Some(count_entry)
            )
        })
    });
    assert!(
        closing_back_edge,
        "the tail call closing the cont-threaded recursion onto count's entry must be a back edge",
    );
}

#[test]
fn compiler2_backend_program_keeps_heap_stats_resume_values_as_runtime_lanes() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00297_heap_alloc_stats.fz".to_string()),
        text: include_str!("../../fixtures2/00297_heap_alloc_stats.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved),
        "heap_alloc_stats backend capture should resolve: {outcome:?}",
    );

    let program = backend.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let (_, main_exec) = backend_executable(&program, main_id);
    let crate::compiler2::BackendBody::Clauses { entries, .. } = &main_exec.body else {
        panic!("expected clause body for heap_alloc_stats main/0");
    };

    let resume_entry = entries
        .iter()
        .find(|entry| match &entry.origin {
            BackendEntryOrigin::DeliveredResume { value, layout } => {
                let _shape = layout.layout.structural;
                entry.steps.iter().any(|step| {
                    matches!(
                        step,
                        BackendStep::FieldAccess { base, .. } if base == value
                    )
                })
            }
            _ => false,
        })
        .unwrap_or_else(|| {
            panic!(
                "expected a delivered-resume entry whose resumed heap-stats value feeds FieldAccess through one runtime lane: {:?}",
                entries
            )
        });

    match &resume_entry.origin {
        BackendEntryOrigin::DeliveredResume { layout, .. } => {
            let _shape = layout.layout.structural;
        }
        other => panic!("expected delivered-resume position for heap_alloc_stats continuation, got {other:?}"),
    }
}

#[test]
fn compiler2_backend_program_keeps_dbg_resumed_heap_stats_as_runtime_lanes() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("heap_stats_dbg_resume.fz".to_string()),
        text:
            "fn main() do\n  stats = Process.heap_alloc_stats()\n  dbg(stats)\n  dbg(stats[:list_cons_allocs])\nend\n"
                .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved),
        "heap_stats dbg-resume backend capture should resolve: {outcome:?}",
    );

    let program = backend.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let dbg_id = function_id(&functions, "dbg", 1);
    let (_, main_exec) = backend_executable(&program, main_id);
    let (_, dbg_exec) = backend_executable(&program, dbg_id);
    assert_eq!(
        dbg_exec.abi.param_reprs,
        vec![AbiValueRepr::ValueRef],
        "Kernel.dbg/1 should still require its input as one runtime lane even when callers ignore the returned value",
    );
    assert!(
        dbg_exec
            .abi
            .semantic_inputs
            .iter()
            .any(|input| input.semantic_index == 0 && !input.layout.reprs.is_empty()),
        "Kernel.dbg/1 should close its input as a non-empty executable contract",
    );
    let crate::compiler2::BackendBody::Clauses { entries, .. } = &main_exec.body else {
        panic!("expected clause body for heap_stats dbg-resume main/0");
    };

    // The continuation we care about is the one that consumes the captured
    // heap-stats: it carries a whole-value capture and reads a field off it.
    // We find it by that shape -- NOT by the resumed value's own lane -- because
    // the heap-stats survive through the capture, not through dbg/1's return.
    // dbg/1 settles a `Value` return, so its delivered-resume boundary still
    // receives one runtime lane; that lane is semantically ignored (received,
    // then dropped) rather than absent. Reception mirrors the callee's emission;
    // whether the value is used is a separate fact carried by the demand.
    let resume_entry = entries
        .iter()
        .find(|entry| {
            matches!(&entry.origin, BackendEntryOrigin::DeliveredResume { .. })
                && !entry.captures.is_empty()
                && entry
                    .steps
                    .iter()
                    .any(|step| matches!(step, BackendStep::FieldAccess { .. }))
        })
        .unwrap_or_else(|| {
            panic!(
                "expected a delivered-resume entry whose captured heap-stats value survives dbg/1 and feeds FieldAccess through one runtime lane: {:?}",
                entries
            )
        });

    match &resume_entry.origin {
        BackendEntryOrigin::DeliveredResume { value, layout } => {
            let _shape = layout.layout.structural;
            assert!(
                main_exec
                    .abi
                    .materialized
                    .runtime_demand
                    .value_demands
                    .get(value)
                    .map(|demand| demand.is_ignore())
                    .unwrap_or(true),
                "the dbg/1 return boundary lane should remain semantically ignored; the later field access must read the captured stats value instead",
            );
        }
        other => panic!("expected delivered-resume origin for dbg-resumed heap-stats continuation, got {other:?}"),
    }
    let field_base = resume_entry
        .steps
        .iter()
        .find_map(|step| match step {
            BackendStep::FieldAccess { base, .. } => Some(*base),
            _ => None,
        })
        .expect("the selected continuation should project from its captured heap stats");
    assert!(
        resume_entry
            .captures
            .iter()
            .any(|capture| capture.value == field_base && capture.layout.reprs.as_ref() == [AbiValueRepr::ValueRef]),
        "the continuation after dbg(stats) must preserve captured stats as a whole runtime value before atom-key projection: {:?}",
        resume_entry
    );
}

#[test]
fn compiler2_interp_runs_quicksort_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00020_quicksort_jit_entry.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "entry".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler
        .run_root_interp(root_id)
        .expect("Compiler2 backend interpreter should run quicksort entry/0");
    let qsort_id = function_id(&functions, "qsort", 1);
    let program = backend.last(root_id).program;
    let (_, qsort_exec) = backend_executable(&program, qsort_id);

    assert_eq!(
        halt, 42,
        "quicksort entry/0 should halt with its explicit scalar result"
    );
    assert_eq!(
        qsort_exec.abi.param_reprs,
        vec![AbiValueRepr::ValueRef],
        "entry matching and recursive descent should keep qsort/1's list input as a runtime lane",
    );
    assert!(
        qsort_exec
            .abi
            .semantic_inputs
            .iter()
            .any(|input| input.semantic_index == 0 && !input.layout.reprs.is_empty()),
        "qsort/1's list input should be closed as a non-empty executable contract",
    );
    assert_eq!(
        dbg.lines().first().map(String::as_str),
        Some("[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]"),
        "quicksort should emit the sorted list through the shared runtime dbg hook",
    );
    assert_eq!(dbg.lines().len(), 1, "quicksort entry/0 should emit one dbg line");
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_interp_runs_enum_reduce_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_runtime_graph.fz".to_string()),
        text: include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler
        .run_root_interp(root_id)
        .expect("Compiler2 backend interpreter should run Enum.reduce main/0");

    assert_eq!(halt, 15, "Enum.reduce should produce the folded integer result");
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_interp_runs_enum_reduce_while_halt_payload_with_distinct_type() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00284_enum_find_early_halt.fz".to_string()),
        text: include_str!("../../fixtures2/00284_enum_find_early_halt.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = dbg.lines().join("\n");
        panic!("Enum.reduce_while should stop on a halt payload whose type differs from the continue accumulator: {error}; dbg={diagnostic}");
    });
    assert_eq!(
        dbg.lines().as_slice(),
        ["1"],
        "Enum.find/3 should return the first matching element and must not call the reducer again after {{:halt, entry}}",
    );
}

#[test]
fn compiler2_semantic_preserves_enum_find_halt_payload_distinct_from_default() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("enum_find_semantic_halt_payload.fz".to_string()),
        text: r#"
fn main() do
  Enum.find([1, 2], :none, fn (_x) -> true end)
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    demand_backend_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "Enum.find semantic analysis should converge with runtime library activations",
    );

    let find_id = function_id_in_module(&functions, &modules, "Enum", "find", 3);
    let find_return = returns.last_for_function(root_id, find_id).return_ty;
    let int = compiler.types_mut_for_test().int();
    assert!(
        compiler.types_for_test().is_subtype(&int, &find_return),
        "Enum.find/3 should preserve the halted element payload alongside the default; got {}",
        compiler.display_ty_for_test(find_return),
    );
}

#[test]
fn compiler2_interp_runs_first_class_callable_captured_by_a_non_tail_continuation() {
    // The minimal shape of fz-hwn.22, free of the Enum stdlib: `maplist` is
    // non-tail recursive (`[f.(h) | maplist(t, f)]`), so its recursion is
    // captured in a continuation that closes over `f`. A phi of two lambdas
    // forces `f` to be a genuine first-class (boxed) callable rather than a
    // direct one. The boxed value must reach the continuation through a single
    // value lane; a zero-lane generic-callable contract drops the box and is
    // unmaterializable.
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/first_class_callable_non_tail_continuation.fz".to_string()),
        text: r#"
fn maplist([], _f), do: []
fn maplist([h | t], f), do: [f.(h) | maplist(t, f)]

fn main() do
  g = if true, do: (fn x -> x + 1 end), else: (fn x -> x + 2 end)
  dbg(maplist([1, 2], g))
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        panic!("Compiler2 backend interpreter should run a first-class callable captured by a non-tail continuation: {error}");
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["[2, 3]"],
        "a boxed first-class callable carried through a continuation capture must still apply to each element",
    );
}

#[test]
fn compiler2_interp_runs_distinct_surface_boxed_callables() {
    // Two opaque (boxed) callables with DIFFERENT invocation surfaces -- `(int)`
    // and `({int, int})`. Under the pure-layout shape model their boxed value
    // shapes may coincide (both are one ValueRef lane); the surface contract
    // lives on their distinct boundaries and the call-site arg encoding. Each
    // must still dispatch to its own body with the right argument shape.
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/distinct_surface_boxed_callables.fz".to_string()),
        text: r#"
fn apply_int(f), do: f.(10)
fn apply_tuple(g), do: g.({3, 4})

fn main() do
  a = if true, do: (fn x -> x + 1 end), else: (fn x -> x + 2 end)
  b = if true, do: (fn ({x, y}) -> x + y end), else: (fn ({x, y}) -> x * y end)
  dbg(apply_int(a))
  dbg(apply_tuple(b))
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        panic!("Compiler2 backend interpreter should run distinct-surface boxed callables: {error}");
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["11", "7"],
        "boxed callables sharing a value shape must still dispatch to their own bodies at their own surfaces",
    );
}

#[test]
fn compiler2_interp_runs_enum_with_index_mapper_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_with_index_mapper_backend_interp.fz".to_string()),
        text: r#"
fn main() do
  dbg(Enum.with_index(["a", "b"], fn (x, _index) -> x <> "!" end))
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        panic!("Compiler2 backend interpreter should run Enum.with_index/2 with a mapper closure: {error}");
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["[\"a!\", \"b!\"]"],
        "Enum.with_index/2 with a mapper should preserve the callback result for each element",
    );
}

// fz-9i4.4.5: a closure-call RESULT born inside the call (`apply(add3(10), 20)`
// returns the inner curried closure) must travel in the shape both sides agree
// on. The callee's specialized executable returns the nested closure in its
// grounded repr (two capture lanes); the caller's transport labels every
// ClosureCall result PublicCallableReturn and forces one boxed ValueRef. The
// two authorities describe the same wire differently, so native lowering
// cannot complete while interp (which dispatches by runtime closure identity)
// stays green. This is the checked-in curried_add fixture driven through both
// paths.
#[test]
fn compiler2_jit_grounds_curried_closure_call_returns() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/curried_add.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/curried_add.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root_id)
        .unwrap_or_else(|error| panic!("interp should run three-level currying: {error}"));
    compiler
        .run_root_jit(root_id)
        .unwrap_or_else(|error| panic!("JIT should run three-level currying: {error}"));
    assert_eq!(
        dbg.lines().as_slice(),
        Vec::<String>::new().as_slice(),
        "curried_add asserts internally; any output is a failed assertion",
    );
}

// fz-9i4.4.5 structural pin: `apply`'s `f.(x)` callee arrives in its exact
// (non-ValueRef) carrier with one settled target, so the callsite lowers as a
// DIRECT edge and its return claim aliases the target's own `ExecutableReturn`
// — no indirect closure call survives in `apply`'s lowered bodies. The
// sibling `compiler2_native_program_calls_published_callable_values_through_
// runtime_identity` pins the opposite pole: a boxed callee keeps the indirect
// call and the public boxed return claim.
#[test]
fn compiler2_native_program_grounds_exact_carrier_closure_call_returns() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/curried_add.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/curried_add.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "curried_add should settle before inspecting apply's closure calls",
    );

    let program = native.last(root_id).program;
    let apply_fns = program
        .module
        .fns
        .iter()
        .filter(|function| function.name.starts_with("apply__e"))
        .collect::<Vec<_>>();
    assert!(!apply_fns.is_empty(), "apply should lower at least one executable");
    let indirect_calls = apply_fns
        .iter()
        .flat_map(|function| function.blocks.iter())
        .filter(|block| {
            matches!(
                &block.terminator,
                IrTerm::CallClosure { .. } | IrTerm::TailCallClosure { .. }
            )
        })
        .count();
    assert_eq!(
        indirect_calls, 0,
        "an exact-carrier singleton closure call must lower as a direct edge with a grounded return",
    );
}

// fz-9i4.7.10.2: three `with_index` mappers coexist over one shared recursive
// reduce activation. Each callsite publishes one CORRELATED input row — its
// list, continuation, and reducer arrived together and may only be read
// together. Pointwise (column-by-column) joining of those rows invents
// Cartesian input combinations, and normalizing the unioned reducer column
// collapses same-function closure literals to one surviving target, routing
// every element family through that one mapper. This test is the coexistence
// pin: each `#[test]` sibling above proves one mapper in isolation (one row —
// a pointwise join of one row is the identity), so only this combination
// exposes the correlation loss.
#[test]
fn compiler2_jit_preserves_correlated_with_index_mapper_rows() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_with_index_mapper_correlated_rows.fz".to_string()),
        text: r#"
fn main() do
  dbg(Enum.with_index(["a", "b"], fn (x, _index) -> x <> "!" end))
  dbg(Enum.with_index([10, 20], fn (x, index) -> x + index end))
  dbg(Enum.with_index([:a, :b], fn (x, index) -> {index, x} end))
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("Compiler2 JIT should run coexisting Enum.with_index/2 mappers: {error}");
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["[\"a!\", \"b!\"]", "[10, 21]", "[{0, :a}, {1, :b}]"],
        "coexisting with_index mappers must each route their own element family through their own reducer",
    );
}

// fz-hwn.23 LANDED: the value-template phantom tombstone is retired. It used to pin
// that `Enum.with_index(…, mapper)` drove a value-template mapper activation into native
// lowering and panicked on `is_value_template`. Cross-activation surface grounding
// (ground_surface_for_template) now replaces that dead generic activation with its ground
// sibling before lowering, so the phantom never reaches the backend. The behaviour is
// guarded directly by `compiler2_interp_runs_enum_with_index_mapper_from_backend_artifacts`
// (re-enabled above), which asserts the real result `["a!", "b!"]`.

#[test]
fn compiler2_interp_runs_variadic_extern_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/variadic_printf_compiler2.fz".to_string()),
        text: include_str!("../../fixtures2/00021_variadic_printf.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler
        .run_root_interp(root_id)
        .expect("Compiler2 backend interpreter should run variadic printf main/0");

    assert_eq!(halt, 1, "printf(\"%d\", 7) should report one printed character");
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_interp_honors_typed_entry_dispatch_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/typed_dispatch_backend_interp.fz".to_string()),
        text: include_str!("../../fixtures2/00022_typed_dispatch.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler
        .run_root_interp(root_id)
        .expect("Compiler2 backend interpreter should honor typed entry dispatch");

    assert_eq!(
        halt, 12,
        "typed entry dispatch should select the integer clause only for integer activations"
    );
}

#[test]
fn compiler2_interp_retains_single_clause_dispatch_failure() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/single_clause_failure_backend_interp.fz".to_string()),
        text: r#"
extern "C" fn fz_dbg_value(any) :: any
fn choose(:a), do: 1
fn main(), do: choose(fz_dbg_value(:b))
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let error = compiler
        .run_root_interp(root_id)
        .expect_err("a nonmatching value should fail retained single-clause dispatch");

    assert!(
        error.contains("function_clause: no backend entry clause matched"),
        "the backend interpreter should report the retained dispatch failure: {error}",
    );
}

#[test]
fn compiler2_runtime_self_send_activations_keep_pid_boundary() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    let modules = ModuleCapture::new();
    let returns = ReturnTypeCapture::new();
    let inputs = ActivationInputCapture::new();
    functions.install(&tel);
    modules.install(&tel);
    returns.install(&tel);
    inputs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/backend_interp_self_send.fz".to_string()),
        text: include_str!("../../fixtures2/00023_backend_interp_self_send.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler
        .run_root_interp(root_id)
        .expect("Compiler2 backend interpreter should settle runtime self/send activations");
    assert_eq!(
        halt, 1,
        "the fixture should still exercise self() followed by send(self(), ...)"
    );

    let self_id = function_id_in_module(&functions, &modules, "Kernel", "self", 0);
    let send_id = function_id_in_module(&functions, &modules, "Kernel", "send", 2);
    let fz_send_id = function_id_in_module(&functions, &modules, "Kernel", "fz_send", 2);
    let types = compiler.types_for_test();
    let display_inputs =
        |record: ActivationInputRecord| record.inputs.iter().map(|ty| types.display(ty)).collect::<Vec<_>>();

    assert_eq!(
        types.display(&returns.last_for_function(root_id, self_id).return_ty),
        "pid",
        "Kernel.self/0 should keep the pid returned by the backend runtime intrinsic"
    );
    assert_eq!(
        display_inputs(inputs.last_for_function(root_id, send_id)),
        vec!["pid".to_string(), "int".to_string()],
        "Kernel.send/2 param0 should stay pid after applying the declared contract"
    );
    assert_eq!(
        display_inputs(inputs.last_for_function(root_id, fz_send_id)),
        vec!["pid".to_string(), "int".to_string()],
        "Kernel.fz_send/2 param0 should stay pid after applying the extern contract"
    );
}

#[test]
fn compiler2_interp_uses_backend_runtime_self_and_send_intrinsics() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/backend_interp_self_send.fz".to_string()),
        text: include_str!("../../fixtures2/00023_backend_interp_self_send.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler
        .run_root_interp(root_id)
        .expect("Compiler2 backend interpreter should route self/send through the runtime scheduler");

    assert_eq!(halt, 1, "self/0 should report pid 1 for the root backend task");
    assert!(
        capture.find(&["fz", "runtime", "send_to_unknown_pid"]).is_empty(),
        "send(self(), ...) should deliver to the live root task instead of falling through the unknown-pid path",
    );
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_interp_runs_spawned_children_from_backend_runtime_intrinsics() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/backend_interp_spawn.fz".to_string()),
        text: include_str!("../../fixtures2/00024_backend_interp_spawn.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!("Compiler2 backend interpreter should schedule spawned child tasks: {error}; diagnostic={diagnostic}");
    });

    assert_eq!(halt, 0, "spawn/1 should leave the root task's scalar result untouched");
    assert_eq!(
        dbg.lines().as_slice(),
        ["42"],
        "spawn/1 should enqueue the child on the backend interpreter run queue and let it reach dbg/1",
    );
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty()
            && capture.find(&["fz", "planner"]).is_empty()
            && capture.find(&["fz", "codegen"]).is_empty(),
        "Compiler2 interpreter runs should not reopen legacy type inference, planning, or codegen",
    );
}

#[test]
fn compiler2_interp_runs_spawn_opt_children_from_backend_runtime_intrinsics() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/backend_interp_spawn_opt.fz".to_string()),
        text: include_str!("../../fixtures2/00025_backend_interp_spawn_opt.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = dbg
            .lines()
            .first()
            .cloned()
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 backend interpreter should accept spawn/2 heap hints through fz_spawn_opt: {error}; dbg={diagnostic}"
        );
    });

    assert_eq!(halt, 0, "spawn/2 should preserve the root task's explicit result");
    assert_eq!(
        dbg.lines().as_slice(),
        ["7"],
        "spawn/2 should still enqueue the child even though the backend interpreter ignores the heap hint",
    );
}

#[test]
fn compiler2_interp_runs_selective_receive_with_make_ref_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/receive_selective_refs.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/receive_selective_refs.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        panic!("Compiler2 backend interpreter should run selective receive over make_ref identities: {error}");
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["3"],
        "selective receive should keep sender-side misses/hits and receiver scan order intact",
    );
}

#[test]
fn compiler2_native_receive_value_resumes_as_arithmetic_input() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("receive_resume_arith.fz".to_string()),
        text: r#"
fn main() do
  me = self()
  send(me, 1)
  value = receive do
    x -> x
  end
  dbg(value + 2)
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("compiler2 native selective receive should resume with an arithmetic-ready value: {error}");
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["3"],
        "a receive hit should resume through the outcome closure with the projected value ready for downstream arithmetic",
    );
}

#[test]
fn compiler2_native_receive_after_divergent_member_runs_numeric_path() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("receive_after_divergent_member.fz".to_string()),
        text: RECEIVE_AFTER_DIVERGENT_DISPATCH.to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("compiler2 native receive should not construct a delivery continuation for a divergent member: {error}");
    });

    assert_eq!(dbg.lines().as_slice(), ["3"]);

    let program = native.last(root_id).program;
    let bump = function_id(&functions, "bump", 1);
    let no_return_targets = program
        .bodies
        .iter()
        .filter_map(|body| match &body.origin {
            NativeBodyOrigin::Executable(key)
                if key.activation.function == bump && compiler.world().types().is_empty(&body.return_ty) =>
            {
                Some(body.fn_id)
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    assert_eq!(no_return_targets.len(), 1);

    let mut tail_calls = 0;
    let mut calls = 0;
    for block in program.module.fns.iter().flat_map(|function| &function.blocks) {
        match &block.terminator {
            IrTerm::TailCall {
                callee: crate::fz_ir::DirectCallTarget::Local(target),
                ..
            } if no_return_targets.contains(target) => tail_calls += 1,
            IrTerm::Call {
                callee: crate::fz_ir::DirectCallTarget::Local(target),
                ..
            } if no_return_targets.contains(target) => calls += 1,
            _ => {}
        }
    }
    assert_eq!(
        tail_calls, 1,
        "the divergent dispatch member should be emitted as a tail call"
    );
    assert_eq!(
        calls, 0,
        "the divergent dispatch member must not publish a delivery continuation"
    );
}

// This test used to pin the RUNTIME fate of the doomed member (interp
// function_clause abort, JIT function_clause halt). Kernel arithmetic
// contracts settle that fate at COMPILE time now: the receive-after join
// makes `value` exactly `:timeout` on the after path, `(:timeout, int)` is
// provably outside every `+/2` arrow, and the program is rejected before any
// backend runs — the same verdict on every path by construction.
#[test]
fn compiler2_receive_after_doomed_timeout_arithmetic_is_rejected_at_compile_time() {
    let source = r#"
fn main() do
  value = receive do
    x -> x
  after
    0 -> :timeout
  end
  dbg(value + 2)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("receive_after_timeout.fz".to_string()),
        text: source.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "the statically doomed :timeout member must reject the program at compile time"
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("the doomed timeout arithmetic should surface as a diagnostic");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::SPEC_VIOLATION.0);
}

#[test]
fn compiler2_native_program_routes_post_receive_resumes_through_delivered_continuations() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/receive_shared_tuple_arity.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/receive_shared_tuple_arity.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "receive_shared_tuple_arity should settle through native lowering before delivered-resume inspection",
    );

    let program = native.last(root_id).program;
    let receive_body_adapter_fns = program
        .module
        .fns
        .iter()
        .flat_map(|function| function.blocks.iter())
        .flat_map(|block| match &block.terminator {
            IrTerm::ReceiveMatched { clauses, .. } => clauses.iter().map(|clause| clause.body).collect::<Vec<_>>(),
            _ => Vec::new(),
        })
        .filter_map(|clause_body_fn| {
            let clause_body = program.module.fn_by_id(clause_body_fn);
            let block = clause_body
                .blocks
                .first()
                .expect("receive clause body should have one entry block");
            match &block.terminator {
                IrTerm::Call { continuation, .. } | IrTerm::CallClosure { continuation, .. } => {
                    Some(continuation.fn_id)
                }
                _ => None,
            }
        })
        .collect::<HashSet<_>>();

    assert_eq!(
        receive_body_adapter_fns.len(),
        6,
        "each receive clause body callsite should get its own delivered-call lane adapter",
    );
    let mut receive_body_resume_fns = HashSet::new();
    for adapter_fn in receive_body_adapter_fns {
        let body = program
            .bodies
            .iter()
            .find(|body| body.fn_id == adapter_fn)
            .unwrap_or_else(|| panic!("native body for receive adapter {adapter_fn:?}"));
        let function = program.module.fn_by_id(adapter_fn);
        assert!(
            matches!(body.entry_abi, NativeEntryAbi::Continuation { .. }),
            "code reached from a receive-arm call must be published as a delivered continuation, not a local direct entry: fn={adapter_fn:?} origin={:?} abi={:?}",
            body.origin,
            body.entry_abi,
        );
        assert!(
            function.name.starts_with("deliver_lanes__"),
            "receive-arm calls should first enter the explicit delivered-call lane adapter: fn={adapter_fn:?} name={}",
            function.name,
        );
        let target = function
            .blocks
            .iter()
            .find_map(|block| match &block.terminator {
                IrTerm::TailCall {
                    callee: crate::fz_ir::DirectCallTarget::Local(target),
                    ..
                } => Some(*target),
                _ => None,
            })
            .unwrap_or_else(|| panic!("receive adapter {adapter_fn:?} should tail-call the shared resume entry"));
        receive_body_resume_fns.insert(target);
    }
    assert_eq!(
        receive_body_resume_fns.len(),
        2,
        "the six receive-arm adapters should converge into one delivered post-receive resume per receive site",
    );
}

#[test]
fn compiler2_native_receive_body_call_resumes_once() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("receive_body_call_resume.fz".to_string()),
        text: r#"
fn main() do
  me = self()
  send(me, 20)
  x = receive do
    v -> v + 2
  end
  dbg(x)
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!(
            "compiler2 native receive-body call should resume once through the delivered continuation seam: {error}"
        );
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["22"],
        "a value produced by a receive-arm call should resume exactly once through the delivered continuation seam",
    );
}

#[test]
fn compiler2_native_receive_branch_call_resumes_once() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("receive_branch_call_resume.fz".to_string()),
        text: r#"
fn add2(x) do
  x + 2
end

fn main() do
  me = self()
  send(me, 20)
  x = receive do
    v ->
      if true do
        add2(v)
      else
        add2(v)
      end
  end
  dbg(x)
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!(
            "compiler2 native receive-arm branches that call before returning should still resume exactly once: {error}"
        );
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["22"],
        "receive outcome join mode must follow the reachable control graph, not just the entry tail",
    );
}

#[test]
fn compiler2_native_receive_mixed_branch_resume_once() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("receive_mixed_branch_resume.fz".to_string()),
        text: r#"
fn add2(x) do
  x + 2
end

fn main() do
  me = self()
  send(me, 20)
  x = receive do
    v ->
      if true do
        add2(v)
      else
        v + 2
      end
  end
  dbg(x)
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!(
            "compiler2 native receive-arm branches must resume exactly once even when one path returns directly and another resumes through an explicit continuation: {error}"
        );
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["22"],
        "receive outcome join mode must be stable across mixed direct-return and explicit-continuation paths",
    );
}

#[test]
fn compiler2_native_multi_relay_delivers_resume_values_through_continuation_abi() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/multi_relay.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/multi_relay.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("compiler2 native multi_relay should deliver receive results through continuation ABI: {error}");
    });
}

#[test]
fn compiler2_native_lowering_consumes_return_payload_flow_through_return_lanes() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/multi_relay.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/multi_relay.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    settle_native_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "multi_relay native handoff should settle before checking ReturnPayload continuations",
    );
    let program = native.last(root_id).program;
    let body_by_fn = program
        .bodies
        .iter()
        .map(|body| (body.fn_id, body))
        .collect::<HashMap<_, _>>();
    let mut saw_return_lanes_continuation = false;

    for body in &program.bodies {
        let function = program.module.fn_by_id(body.fn_id);
        if matches!(body.origin, NativeBodyOrigin::Continuation { .. })
            && function
                .blocks
                .iter()
                .any(|block| matches!(block.terminator, IrTerm::ReturnLanes(_)))
        {
            saw_return_lanes_continuation = true;
        }
        for block in &function.blocks {
            if let IrTerm::TailCall {
                callee: crate::fz_ir::DirectCallTarget::Local(callee),
                ..
            } = &block.terminator
            {
                let callee_body = body_by_fn
                    .get(callee)
                    .unwrap_or_else(|| panic!("native TailCall target {:?} should have a NativeBody", callee));
                assert!(
                    callee_body.return_reprs.is_empty() || body.return_reprs == callee_body.return_reprs,
                    "native TailCall must only forward an already-matching return ABI; non-tail return flow is carried by ReturnPayload continuations"
                );
            }
        }
    }

    assert!(
        saw_return_lanes_continuation,
        "multi_relay should contain at least one generated continuation that returns ReturnPayload lanes through the caller return ABI"
    );
}

#[test]
fn compiler2_native_actor_ring_delivers_resume_values_through_continuation_abi() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/actor_ring.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/actor_ring.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("compiler2 native actor_ring should deliver receive results through continuation ABI: {error}");
    });
}

#[test]
fn compiler2_interp_runs_resource_dtors_from_backend_runtime_intrinsics() {
    let _lock = tests_support_lock().lock().unwrap();
    tests_support_dtor_reset();

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/backend_interp_make_resource.fz".to_string()),
        text: include_str!("../../fixtures2/00026_make_resource.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let halt = compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "Compiler2 backend interpreter should route make_resource/2 through the shared runtime helper: {error}; diagnostic={diagnostic}"
        );
    });

    assert_eq!(
        halt, 0,
        "make_resource/2 should preserve the root task's explicit result"
    );
    assert_eq!(
        tests_support_dtor_fired(),
        1,
        "backend interpreter shutdown should drain the pending resource destructor exactly once",
    );
    assert_eq!(
        tests_support_dtor_last_payload(),
        42,
        "the backend interpreter should run the resource destructor body as real fz code and pass the payload through",
    );
    assert!(
        capture.find(&["fz", "runtime", "dtor_drain_failed"]).is_empty(),
        "resource destructor drain should complete cleanly on the backend interpreter path",
    );
}

#[test]
fn compiler2_native_program_reads_continuation_reprs_from_transport_seams() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("native_float_resume_reads_transport_seam.fz".to_string()),
        text: r#"
fn inc(x), do: x + 1.0

fn main() do
  y = inc(1.0)
  y + 2.0
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "native float-resume fixture should settle through native lowering",
    );

    let program = native.last(root_id).program;
    let adapter = program
        .bodies
        .iter()
        .find(|body| {
            program.module.fn_by_id(body.fn_id).name.starts_with("deliver_lanes__")
                && matches!(body.entry_abi, NativeEntryAbi::Continuation { extra_params: 1 })
        })
        .expect("the non-tail float call should first enter a callee-return lane adapter");
    assert_eq!(
        adapter.param_reprs[0],
        AbiValueRepr::RawF64,
        "the delivered-call adapter must expose the callee's physical RawF64 return lane",
    );

    let continuation = program
        .bodies
        .iter()
        .find(|body| {
            let function = program.module.fn_by_id(body.fn_id);
            matches!(body.origin, NativeBodyOrigin::Continuation { .. }) && function.name.contains("__resume_")
        })
        .expect("the non-tail float call should lower through a delivered continuation");

    assert_eq!(
        continuation.entry_abi,
        NativeEntryAbi::Continuation { extra_params: 1 },
        "the delivered float resume payload should occupy one continuation lane",
    );
    assert_eq!(
        continuation.param_reprs[0],
        AbiValueRepr::RawF64,
        "the resolved resume endpoint should preserve the callee's physical RawF64 result lane",
    );
}

#[test]
fn compiler2_native_program_adapts_delivered_calls_from_exact_callee_return_lanes() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("enum_take_delivered_lane_adapter.fz".to_string()),
        text: "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n".to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "Enum.take should settle before inspecting delivered-call native adapters",
    );

    let exact_result = RuntimeDemand::tuple_fields(vec![RuntimeDemand::ignore(), RuntimeDemand::whole()]);
    let backend_program = compiler.retained_backend_program(root_id);
    let count_result = backend_program
        .executables()
        .iter()
        .find(|executable| {
            compiler.world().function_ref(executable.key.activation.function).name == "count_result"
                && executable.abi.materialized.runtime_demand.input_demands.first() == Some(&exact_result)
        })
        .expect("the selected count-result clause should need only the integer payload");
    assert!(
        compiler
            .world()
            .executable_facts(&count_result.key)
            .expect("count-result executable facts should be settled")
            .entry_dispatch_inputs
            .is_empty(),
        "the directly selected ok clause must not consume the omitted variant tag",
    );

    let count_resume = backend_program
        .executables()
        .iter()
        .filter(|executable| {
            compiler.world().function_ref(executable.key.activation.function).name == "count"
                && executable
                    .abi
                    .materialized
                    .runtime_demand
                    .call_arg_demands
                    .values()
                    .flatten()
                    .any(|demand| demand == &exact_result)
        })
        .flat_map(|executable| match &executable.body {
            BackendBody::Clauses { entries, .. } => entries.iter().collect::<Vec<_>>(),
            BackendBody::Extern { .. } => Vec::new(),
        })
        .find_map(|entry| match &entry.origin {
            BackendEntryOrigin::DeliveredResume { layout, .. }
                if layout.layout.reprs.as_ref() == [AbiValueRepr::RawInt] =>
            {
                Some(layout)
            }
            _ => None,
        })
        .expect("the exact count-result demand should project one delivered integer lane");
    assert_eq!(count_resume.layout.carrier, TransportCarrier::Absent);

    let program = native.last(root_id).program;
    let adapter = program
        .bodies
        .iter()
        .find(|body| {
            let function = program.module.fn_by_id(body.fn_id);
            let NativeBodyOrigin::Continuation { owner } = body.origin else {
                return false;
            };
            function.name.starts_with("deliver_lanes__")
                && program.module.fn_by_id(owner).name.starts_with("count__")
                && matches!(body.entry_abi, NativeEntryAbi::Continuation { extra_params: 1 })
                && body.param_reprs == [AbiValueRepr::RawInt]
        })
        .expect("the native adapter should expose the same exact delivered integer lane");

    assert!(
        program
            .module
            .fn_by_id(adapter.fn_id)
            .blocks
            .iter()
            .any(|block| matches!(block.terminator, IrTerm::TailCall { .. })),
        "the adapter should tail-deliver the reconstructed value to the original resume entry",
    );
}

#[test]
fn compiler2_native_program_calls_published_callable_values_through_runtime_identity() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("enum_take_reducer_published_value.fz".to_string()),
        text: "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n".to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "Enum.take should settle before inspecting reducer callable calls",
    );

    let program = native.last(root_id).program;
    let reducer_calls = program
        .module
        .fns
        .iter()
        .filter(|function| function.name.starts_with("reduce_while_cont__clause_"))
        .flat_map(|function| function.blocks.iter())
        .filter(|block| matches!(&block.terminator, IrTerm::CallClosure { .. }))
        .count();

    assert!(
        reducer_calls > 0,
        "a generic reducer call must stay a first-class closure call dispatching through the published callable value",
    );
}

/// fz-bdk: a runtime fault must never report success. `handle(pick(5))` is
/// well-typed as written -- which atom arrives depends on execution -- so the
/// uncovered `:third` witness can only be caught by the runtime trap. Interp
/// already surfaces that trap as a loud `Err`; the JIT driver used to run the
/// scheduler until idle and return `Ok(())` unconditionally, discarding the
/// fault (real side effects up to the trap, then a silent success). The exit
/// kind is a structural fact set only by the fault-halt trap itself -- never
/// inferred from the halted value, which a program may legitimately return.
#[test]
fn compiler2_jit_reports_runtime_dispatch_fault_at_the_exit_boundary() {
    let source = r#"
fn pick(0), do: :first
fn pick(_), do: :third

fn handle(:first), do: 1
fn handle(:second), do: 2

fn main() do
  dbg(1)
  dbg(handle(pick(5)))
  dbg(2)
end
"#;
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("runtime_dispatch_fault.fz".to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let interp_error = compiler
        .run_root_interp(root)
        .expect_err("interp must abort on the uncovered dispatch witness");
    assert!(
        interp_error.contains("function_clause"),
        "interp fault should name function_clause: {interp_error}"
    );
    let jit_error = compiler
        .run_root_jit(root)
        .expect_err("the JIT driver must report the runtime fault, not unify it with normal completion");
    assert!(
        jit_error.contains("function_clause"),
        "JIT fault should name function_clause: {jit_error}"
    );
    assert_eq!(
        dbg.lines(),
        vec!["1".to_string(), "1".to_string()],
        "both paths run real side effects up to the trap and nothing after it",
    );
}

/// fz-9in: a binding can be dead while the call that produces it survives
/// (the `1..5` Range construction allocates, so the call edge is kept even
/// though nothing demands its result). The callee then runs with zero
/// materialized inputs, so every step retained in its body must respect the
/// absence proof: a construction step whose value is proven runtime-absent
/// must lower as `Omitted`, not execute a read of never-bound params. Before
/// the fix this failed on interp ("backend value 0 is unbound") and panicked
/// native lowering's bound-before-use invariant.
#[test]
fn compiler2_unused_construction_call_binding_keeps_the_root_runnable() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/unused_range_binding.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/unused_range_binding.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .expect("the unused range binding must not starve the Range construction body on interp");
    compiler
        .run_root_jit(root)
        .expect("the unused range binding must not starve the Range construction body on JIT");
    assert_eq!(
        dbg.lines(),
        vec!["[1, 2, 3]".to_string(), "[1, 2, 3]".to_string()],
        "Enum.take must be unaffected by the dead sibling binding",
    );
}

/// fz-kdt.111: on the empty-list path `Enum.drop_while/2` never invokes its
/// predicate, so runtime demand marks the closure input `ignore` and transport
/// gives the `Lambda` value no lane at all -- nothing downstream can read it.
/// The construction step for that dead closure must therefore be omitted like
/// any other fresh construction of a proven-absent value: the interp evaluates
/// steps eagerly and used to fault reading the never-bound capture ("backend
/// value 1 is unbound") while native, which materializes absent values lazily,
/// ran the same program correctly -- a three-path-parity break.
#[test]
fn compiler2_dead_closure_capture_does_not_starve_the_empty_list_path() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/dead_closure_capture_empty_list.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/dead_closure_capture_empty_list.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .expect("interp must not evaluate the dead predicate closure's capture read");
    compiler.run_root_jit(root).expect("JIT must run the same fixture");
    let lines = dbg.lines();
    assert_eq!(
        lines,
        vec!["[]".to_string(), "[3]".to_string(), "[]".to_string(), "[3]".to_string()],
        "both paths must drop nothing from the empty list and still run the live predicate",
    );
}

/// A rendered closure reports the arity its source declares, not the size of
/// the environment the compiler happened to give it. Both closures here carry
/// exactly one capture, so a renderer keyed on the environment cannot tell
/// them apart; Elixir's `#Function<.../arity>` reports the parameter count,
/// and so does `#fn<id/arity>` (fz-gk4).
#[test]
fn compiler2_rendered_closure_reports_its_arity_not_its_capture_count() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/closure_render_arity.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/closure_render_arity.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root).expect("interp must run the fixture");
    compiler.run_root_jit(root).expect("JIT must run the fixture");
    let arities = dbg
        .lines()
        .iter()
        .map(|line| {
            line.rsplit_once('/')
                .and_then(|(_, tail)| tail.strip_suffix('>'))
                .unwrap_or_else(|| panic!("rendered closure {line} must end in /<arity>>"))
                .to_string()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        arities,
        vec!["0", "2", "0", "2"],
        "both lanes must render the declared arities (0 and 2), not the capture count (1)",
    );
}

#[test]
fn compiler2_native_program_keeps_published_closure_calls_indirect() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/opaque_fn_each_discarded_return.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/opaque_fn_each_discarded_return.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "closure boundary fixture should settle before inspecting closure call telemetry",
    );

    let program = native.last(root_id).program;
    assert!(
        native_closure_call_count(&program) > 0,
        "fixture should publish an indirect closure call through its callable boundary",
    );
}

#[test]
fn compiler2_enum_take_drop_split_keeps_predicate_calls_exact_through_interp_and_jit() {
    let source = include_str!("../../fixtures2/behavior/enum_take_drop_split.fz");
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/enum_take_drop_split.fz".to_string()),
        text: source.to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(compiler.drive(), "enum take/drop/split should lower natively");

    let predicate_functions = functions
        .all()
        .into_iter()
        .filter(|record| {
            record
                .function_ref
                .name
                .strip_prefix("#lambda:0:")
                .is_some_and(|range| {
                    range.split_once('-').is_some_and(|(start, end)| {
                        start
                            .parse::<usize>()
                            .ok()
                            .zip(end.parse::<usize>().ok())
                            .and_then(|(start, end)| source.get(start..end))
                            .is_some_and(|body| body.contains("x < 4"))
                    })
                })
        })
        .map(|record| record.function_id)
        .collect::<HashSet<_>>();
    assert!(!predicate_functions.is_empty());
    let program = native.last(root_id).program;
    let predicate_targets = program
        .bodies
        .iter()
        .filter_map(|body| match &body.origin {
            NativeBodyOrigin::Executable(key) if predicate_functions.contains(&key.activation.function) => {
                Some(body.fn_id)
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    assert!(
        program
            .module
            .fns
            .iter()
            .flat_map(|function| &function.blocks)
            .any(|block| match &block.terminator {
                IrTerm::Call {
                    callee: crate::fz_ir::DirectCallTarget::Local(target),
                    ..
                }
                | IrTerm::TailCall {
                    callee: crate::fz_ir::DirectCallTarget::Local(target),
                    ..
                } => predicate_targets.contains(target),
                _ => false,
            })
    );

    compiler
        .run_root_interp(root_id)
        .expect("enum take/drop/split should run in the interpreter");
    compiler
        .run_root_jit(root_id)
        .expect("enum take/drop/split should run in the JIT");
    let expected = include_str!("../../fixtures2/behavior/enum_take_drop_split.expected.txt")
        .lines()
        .collect::<Vec<_>>();
    let lines = dbg.lines();
    assert_eq!(&lines[..expected.len()], expected.as_slice());
    assert_eq!(&lines[expected.len()..], expected.as_slice());
}

/// fz-f98.17 — a callee that still carries type variables is NOT-YET-KNOWN, and
/// a closure call must not answer it with the earned `any`.
///
/// `Enum.drop_while/2` reaches `List.reduce_while_cont/3`, whose body calls
/// `reducer.(head, acc)` through a parameter. The reducer slot arrives from the
/// `Enumerable.reduce_while/3` protocol callback, whose spec cannot instantiate
/// it, so the callee type at that call is a bare type variable (or the real
/// closure joined with one). Reading that as a dynamic edge earned `any`, and
/// because the value-type join is cumulative it was never retracted once the
/// slot grounded — leaving the callsite holding a precisely-resolved
/// `CallSiteSummary` and an `any` value type at the same time.
///
/// Two distinct closures were green and three were not, so this drives three.
/// The fz-f98.14.11 artifact guard is the detector: it refuses to materialize a
/// public closure callsite whose settled return disagrees with its semantic
/// result type, so a returning `any` fails the drive here.
#[test]
fn compiler2_variable_callee_is_absence_not_an_earned_any() {
    let _lock = tests_support_lock().lock().unwrap();
    tests_support_dtor_reset();

    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/enum_hof_three_distinct_closures.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/enum_hof_three_distinct_closures.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "one Enum HOF at three distinct closures should lower without earning `any` at its reducer call",
    );

    compiler
        .run_root_interp(root_id)
        .expect("three distinct closures should run in the interpreter");
    let expected = include_str!("../../fixtures2/behavior/enum_hof_three_distinct_closures.expected.txt")
        .lines()
        .collect::<Vec<_>>();
    assert_eq!(dbg.lines(), expected.as_slice());
}

#[test]
fn compiler2_native_program_resource_fixture_shapes_callable_boundaries_explicitly() {
    let _lock = tests_support_lock().lock().unwrap();
    tests_support_dtor_reset();

    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_resource_callable_shape.fz".to_string()),
        text: include_str!("../../fixtures2/00026_make_resource.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "resource fixture should settle through native lowering before JIT consumes it",
    );

    let program = native.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let lambda_id = generated_functions_owned_by(&functions, main_id)
        .into_iter()
        .next()
        .expect("generated dtor lambda")
        .function_id;
    let callable_boundaries = program
        .callable_boundaries
        .iter()
        .filter(|entry| {
            entry
                .members
                .iter()
                .any(|member| member.target.activation.function == lambda_id)
        })
        .map(|entry| {
            (
                entry.captures.len(),
                entry.call_arity,
                entry
                    .members
                    .iter()
                    .filter(|member| member.target.activation.function == lambda_id)
                    .map(|member| {
                        member
                            .target_inputs
                            .iter()
                            .map(|input| input.layout.reprs.to_vec())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        callable_boundaries,
        vec![(0, 1, vec![vec![vec![AbiValueRepr::RawInt]]],)],
        "resource destructor lambdas should publish a wrapper-owned call surface with the member's exact raw payload layout",
    );
    assert_eq!(
        native_executable_body(&program, lambda_id).param_reprs,
        vec![AbiValueRepr::RawInt],
        "resource destructor executable bodies should specialize their native entry lane to the raw payload type",
    );
    let make_resource_id = function_id(&functions, "fz_make_resource", 2);
    let make_resource_body = native_executable_body(&program, make_resource_id);
    assert_eq!(
        make_resource_body.param_reprs,
        vec![AbiValueRepr::RawInt, AbiValueRepr::ValueRef],
        "fz_make_resource/2 must take the payload through the raw integer lane and the destructor closure through the boxed value lane",
    );
    assert!(
        make_resource_body.return_reprs.is_empty(),
        "main discards the resource handle, so fz_make_resource/2's resource return is not transported",
    );

    let native_callable_boundary = program
        .callable_boundaries
        .iter()
        .find(|entry| {
            entry
                .members
                .iter()
                .any(|member| member.target.activation.function == lambda_id)
        })
        .expect("native program should publish the dtor lambda callable boundary");
    let compiled = jit_compile_native_program(&mut compiler, &program);
    // Singletons are keyed by callable-boundary id -- the same key
    // `fz_get_static_closure` looks them up under at runtime.
    let static_target = compiled
        .static_closure_targets()
        .iter()
        .find(|(cl_sid, _, _, _)| *cl_sid == native_callable_boundary.id().as_u32())
        .expect("compiled JIT module should publish one static closure target for the dtor wrapper");
    let body_ptr = compiled
        .fn_ptr(native_callable_boundary.wrapper_fn)
        .expect("compiled JIT module should publish the dtor wrapper body address");
    assert_ne!(
        static_target.2, body_ptr,
        "static closure singletons should point at callable-boundary wrappers, not straight at the lambda body",
    );
}

/// fz-hwn.17 -- an escaping callable grounded by its boundary contract keys its
/// activation at the grounded surface, not its own polymorphic template.
///
/// `make_resource(42, fn (x) -> _resource_test_dtor(x) end)` passes the
/// destructor lambda across the `fz_make_resource(t, (t) -> nil) :: resource(t)
/// when t: integer | cpointer` boundary. The literal `42` pins `t := integer`,
/// so the boundary's settled surface for the lambda is `(integer) -> nil`. The
/// lambda's *own* type stays the polymorphic template `(t) -> nil` -- that is
/// correct, and is left untouched. What must happen is that the escape demand
/// carries the boundary's grounded surface so the lambda's specialized
/// activation is keyed at `[integer]`.
///
/// We observe the cause directly: the lambda's executable body is keyed at the
/// grounded `int` payload type (the same interned `int` that `main` returns),
/// and therefore takes the raw integer lane. A leaked free type variable would
/// key a distinct, un-grounded activation with no raw lane -- it would box to
/// `ValueRef`, which is exactly the regression this pins against.
#[test]
fn escaping_destructor_keys_its_activation_at_the_grounded_boundary_surface() {
    let _lock = tests_support_lock().lock().unwrap();
    tests_support_dtor_reset();

    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_resource_callable_shape.fz".to_string()),
        text: include_str!("../../fixtures2/00026_make_resource.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "resource fixture should settle through native lowering",
    );

    let program = native.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let lambda_id = generated_functions_owned_by(&functions, main_id)
        .into_iter()
        .next()
        .expect("generated dtor lambda")
        .function_id;

    // `main` ends in the literal `0`, so its settled return type is the
    // interned `int`. The escaping destructor's payload must be that same type.
    let int_ty = native_executable_body(&program, main_id).return_ty;
    let lambda_body = native_executable_body(&program, lambda_id);
    let NativeBodyOrigin::Executable(key) = &lambda_body.origin else {
        panic!("the destructor lambda should lower to a top-level executable body");
    };
    assert_eq!(
        key.activation.inputs(compiler.types_for_test()),
        vec![int_ty],
        "the escaping destructor keys its activation at the grounded payload type carried by make_resource's boundary surface, not its own (t) template",
    );
    assert_eq!(
        lambda_body.param_reprs,
        vec![AbiValueRepr::RawInt],
        "the grounded activation takes the raw integer lane; a leaked type variable would have no raw lane and box to ValueRef",
    );
}

/// fz-hwn.19.3 -- a typed-capture closure that the compiler resolves to a known
/// target is dispatched DIRECTLY; it does not publish an opaque first-class
/// callable boundary.
///
/// `add_to(x, y)` returns `fn (z) -> x + y + z`, and `apply1(f, x)` calls `f.(x)`.
/// Because the closure's producer and call site are both visible, transport
/// settles it as a *direct* callable (`direct_callable_count >= 1`,
/// `boundary_publication_count == 0`); `apply1`'s `f.(z)` lowers to a direct
/// call to the lambda body, passing the captured `[x, y]` lanes straight through.
///
/// The previous form of this test asserted the opposite -- that the program
/// publishes a widened `ValueRef` opaque callable boundary -- which is provably
/// wrong for this fixture: compiler2 never makes this closure opaque, so no such
/// boundary exists (verified: `callable_boundaries` is empty). The settled
/// callable-boundary *selection* this red-worklist entry was reaching for is the
/// rematerialization path, now covered by
/// `compiler2_native_callable_materialization_selects_the_callableid_fact_boundary`.
/// fz-hwn.19.5 removed the native-codegen return-shape vocabulary that kept
/// this fixture from reaching JIT execution.
#[test]
fn compiler2_native_codegen_dispatches_typed_capture_closure_directly_without_a_published_boundary() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/closure_typed_captures.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/closure_typed_captures.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "closure_typed_captures should settle through native lowering before JIT consumes it",
    );

    let program = native.last(root_id).program;
    assert!(
        program.callable_boundaries.is_empty(),
        "a typed-capture closure resolved to a known target must dispatch directly, not publish an opaque first-class callable boundary; got {:?}",
        program.callable_boundaries,
    );
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let halt = compiled.run(compiler.telemetry(), program.entry);
    assert_eq!(
        halt, 0,
        "closure_typed_captures should execute through JIT and halt with nil"
    );
}

#[test]
fn compiler2_unchanged_backend_request_emits_no_content_movement() {
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    demand_backend_product(&mut compiler, root_id);
    assert_resolved(compiler.drive(), "initial backend product should settle for quicksort");
    demand_backend_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "rebuilding unchanged backend state should resolve without redefining it",
    );

    let records = backend.records(root_id);
    assert_eq!(
        records.len(),
        1,
        "an unchanged backend request must not emit another changed settlement",
    );
    assert!(
        records[0].changed,
        "a changed backend settlement represents actual state movement",
    );
}

#[test]
fn compiler2_variadic_extern_too_few_args_is_a_lower_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/variadic_open_too_few_compiler2.fz".to_string()),
        text: include_str!("../../fixtures2/00052_variadic_open_too_few.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let outcome = compiler.drive();
    let main_id = function_id(&functions, "main", 0);
    let job = match outcome {
        DriveOutcome::Fatal { job } => job,
        other => panic!("too-few variadic args should fail during lowering: {other:?}"),
    };
    assert_eq!(
        job,
        Job::LowerFunction(main_id),
        "the direct caller should fail while lowering the impossible variadic call",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("variadic arity diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::LOWER_UNSUPPORTED.0,
        "too-few variadic args should surface as an unsupported lowering case",
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("at least 2 arg(s)")
            && metadata_str(&diagnostic, "message").contains("provides 1"),
        "variadic arity diagnostic should explain the fixed prefix the call failed to satisfy",
    );
}

#[test]
fn compiler2_semantic_analysis_derives_reachable_call_edges_and_tuple_return_need() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let callsites = CallsiteCapture::new();
    callsites.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "rooted quicksort should settle the first semantic direct-call island",
    );

    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);
    let callsites = callsites.all();

    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == main_id
                && summary_is_single_callee(&record.summary, SelectedCallee::Function(qsort_id))
        }),
        "semantic analysis should publish the rooted main/0 -> qsort/1 direct edge"
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == qsort_id
                && summary_is_single_callee(&record.summary, SelectedCallee::Function(partition_id))
        }),
        "semantic analysis should publish qsort/1's reachable partition/4 direct edge"
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == qsort_id
                && summary_is_single_callee(&record.summary, SelectedCallee::Function(append_id))
        }),
        "semantic analysis should publish qsort/1's reachable append/2 direct edge"
    );
    assert!(
        callsites
            .iter()
            .all(|record| !summary_has_callee(&record.summary, SelectedCallee::Function(foo_id))),
        "uncalled foo/0 should stay semantically cold"
    );
    assert_eq!(
        capture.find(&["fz", "type_infer"]).len(),
        0,
        "Compiler2 semantic analysis should not invoke the legacy type inference pipeline"
    );
    assert_eq!(
        capture.find(&["fz", "planner"]).len(),
        0,
        "Compiler2 semantic analysis should not invoke the legacy planner pipeline"
    );
}

#[test]
fn compiler2_backend_product_lowers_closed_union_protocol_dispatch_as_call_edge() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &["fz", "diag", "error"]);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let callsites = CallsiteCapture::new();
    callsites.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_protocol_union_dispatch.fz".to_string()),
        text: r#"
defprotocol Sizer do
  fn size(value)
end

defimpl Sizer, for: Range do
  fn size(value), do: 7
end

defimpl Sizer, for: List do
  fn size(value), do: 100
end

fn describe(value), do: Sizer.size(value)

fn main() do
  case [1..3, [1, 2, 3]] do
    [a, b] -> describe(a) + describe(b)
    _ -> 0
  end
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    match compiler.drive() {
        DriveOutcome::Resolved => {}
        DriveOutcome::Fatal { job } => panic!(
            "closed-union protocol receivers should lower as a dispatch call edge instead of dying with a missing direct edge: {job:?}; diag={:?}",
            capture
                .last(&["fz", "diag", "error"])
                .map(|event| metadata_str(&event, "message").to_string())
        ),
        other => panic!(
            "closed-union protocol receivers should lower as a dispatch call edge instead of dying with a missing direct edge: {other:?}"
        ),
    }

    let describe_id = function_id(&functions, "describe", 1);
    let describe_summary = callsites
        .all()
        .into_iter()
        .find(|record| record.key.activation.root == root_id && record.key.activation.function == describe_id)
        .unwrap_or_else(|| panic!("callsite.defined for describe/1"));
    let expected_targets = describe_summary
        .summary
        .targets
        .iter()
        .map(|target| match target.callee {
            SelectedCallee::Function(function) => function,
            SelectedCallee::ProviderBoundary(function) => {
                panic!("expected local protocol target, got provider-boundary function {function:?}")
            }
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        expected_targets.len(),
        2,
        "describe/1 should record one semantic callsite fact with exactly two viable protocol impls",
    );

    let program = backend.last(root_id).program;
    let (_, describe_exec) = backend_executable(&program, describe_id);
    let crate::compiler2::BackendBody::Clauses { entries, .. } = &describe_exec.body else {
        panic!("describe/1 should lower as clauses");
    };
    let (callsite, edge) = entries
        .iter()
        .find_map(|entry| match &entry.tail {
            BackendTail::DirectCall { callsite, target, .. } => Some((*callsite, target)),
            _ => None,
        })
        .unwrap_or_else(|| panic!("backend describe/1 should keep its original direct-call tail"));
    let CallEdge::Dispatch(dispatch) = edge else {
        panic!(
            "closed-union protocol receiver should lower as a dispatch call edge at callsite {}",
            callsite.as_u32(),
        );
    };
    assert_eq!(
        dispatch.plan.input_count, 1,
        "protocol call dispatch should test the receiver input only",
    );
    assert_eq!(
        dispatch.arms.len(),
        2,
        "closed-union protocol dispatch should lower one call edge arm per viable impl",
    );
    let arm_targets = dispatch
        .arms
        .iter()
        .map(|arm| {
            let target = arm
                .callee
                .local()
                .unwrap_or_else(|| panic!("protocol dispatch arms should target local executables"));
            target.activation.function
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        arm_targets, expected_targets,
        "the backend dispatch call-edge arms should target the two settled impl executables from the semantic summary",
    );
}

/// fz-kdt.104: arm order must not be the program's meaning.
///
/// A dispatch arm asks its question through `RuntimeTypePredicate`, which is
/// coarser than the semantic type it is projected from -- `{:cont, pair}` and
/// `{:cont | :halt, pair}` are both just "a 2-tuple". Two arms that project to
/// ONE question are not two alternatives: nothing but their order decides
/// which body runs, and that order is the scheduler's. At FIFO the wide arm of
/// `Enum.take`'s `reduce_while_step` dispatch happens to come first and the
/// narrow one is dead; at LIFO the narrow arm comes first, swallows
/// `{:halt, _}`, and `Enum.take(xs, 3)` returns the whole list.
///
/// `call_destinations` therefore drops an arm whose stand-in the seat would
/// never let it pass -- the SAME callee on a strictly wider observable domain
/// asking a question that admits everything the arm's own admits -- and this
/// gate reads the landed artifact back to prove no two arms asking one
/// question survived. It is red at FIFO on today's tree -- no schedule knob
/// needed.
///
/// The LIFO half is verified by hand, per the fz-kdt.93 precedent: change
/// `Agenda::pop` (src/compiler2/agenda.rs) to `self.queue.pop_back()` and run
/// `fz2 run fixtures2/00183_enum_take_list_range.fz`; its first line must be
/// `[1, 2, 3]`.
///
/// Arms asking one question with no stand-in between them -- neither domain
/// contains the other, or they are different functions -- are a different,
/// wider defect: no arm can supply the others' bodies, so the cure is a
/// runtime predicate that can tell them apart, not a smaller plan
/// (fz-kdt.107). Three predicates cleared the corpus of them, and every
/// fixture each one cleared is listed here.
///
/// fz-kdt.125 supplied the first -- which callable a value is.
/// `closure_identity_tag_split` and `closure_identity_captures` are the two
/// programs that named the defect and are shadow-free by that cure.
///
/// fz-kdt.107 step 3 supplied the second -- what a cons cell's first element
/// is -- and `enum_map_family` is the fixture it clears: its three
/// `[:a | :b]` / `[binary]` / `[int]` arms were one question, they are three
/// now, and its arm-reversal abort dies with them.
///
/// fz-kdt.127 supplied the third -- which CONSTRUCTION a callable value was
/// minted from, function and capture layout together -- and it clears the last
/// five: `00231`, `00277`, `00281`, `opaque_fn_value_join` and
/// `repr_seam_enum_count_after_reduce2` each had one or two groups that were
/// one lambda over two capture types, which is one code pointer only while
/// the axis stops at the function.
///
/// The CALL-EDGE census those three cures emptied is empty still, and every
/// fixture each one cleared is listed below. What fz-kdt.178 added is the rest
/// of the artifact -- an executable's clause dispatch and a construction
/// wrapper's member selection are plans with arms exactly as a callsite is --
/// and the wrapper selections are NOT empty:
/// [`INDISTINGUISHABLE_ARM_POPULATION`] names each site and its group count.
/// Member selection runs the drop now (fz-kdt.179), so any group whose members
/// have a stand-in dissolves; what remains is fz-kdt.107's -- a group with no
/// stand-in, whose members no runtime predicate tells apart -- and the constant
/// is the ratchet fz-kdt.107 shrinks.
#[test]
fn compiler2_dispatch_offers_no_runtime_indistinguishable_arm() {
    let mut measured: BTreeMap<(&str, String), usize> = BTreeMap::new();
    let mut twins = Vec::new();
    for fixture in [
        "fixtures2/00183_enum_take_list_range.fz",
        "fixtures2/00420_enum_take_drop_split.fz",
        "fixtures2/00275_enum_count_member_reduce.fz",
        "fixtures2/behavior/enum_reduce_halt_arm_order.fz",
        "fixtures2/behavior/range_enumerable.fz",
        "fixtures2/behavior/closure_identity_tag_split.fz",
        "fixtures2/behavior/closure_identity_captures.fz",
        "fixtures2/behavior/enum_map_family.fz",
        "fixtures2/00231_joined_fn_refs_enum_reduce.fz",
        "fixtures2/00277_enum_tier0_fixture.fz",
        "fixtures2/00281_opaque_reducer_closure.fz",
        "fixtures2/behavior/opaque_fn_value_join.fz",
        "fixtures2/behavior/repr_seam_enum_count_after_reduce2.fz",
    ] {
        for finding in indistinguishable_dispatch_arms(fixture) {
            let (site, group) = finding
                .split_once(" arm ")
                .expect("a twin names its site then its arms");
            *measured.entry((fixture, site.to_string())).or_default() += 1;
            twins.push(format!("{fixture} {site}: arm {group}"));
        }
    }
    let known = INDISTINGUISHABLE_ARM_POPULATION
        .iter()
        .map(|(fixture, site, groups)| ((*fixture, (*site).to_string()), *groups))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        measured, known,
        "a dispatch must not offer two arms that ask one runtime question, or arm order decides the \
         program's meaning -- and the only groups that may are the ones fz-kdt.107 owns: members no \
         runtime predicate tells apart, on a wrapper selection or a callsite alike: {twins:#?}",
    );
}

/// The plans that still offer two arms one runtime question cannot separate,
/// by site and by how many such groups the site carries.
///
/// Every row is a construction wrapper's member selection, and what remains is
/// fz-kdt.107's alone. Member selection runs through `routable_alternatives`
/// now (fz-kdt.179, `construction_member_selection`), so fz-kdt.118's drop --
/// which dissolves a group whose members have a stand-in -- runs there exactly
/// as it does on a callsite. What a drop cannot reach afterwards is fz-kdt.107's:
/// members no runtime predicate tells apart at all, whose only cure is a sharper
/// test, not a smaller plan.
///
/// A ratchet, per site, so fz-kdt.107 can retire a wrapper at a time. A new
/// row, or a row on a call edge or an entry dispatch, is a new latent
/// miscompile and wants a ticket rather than a re-blessed constant.
///
/// fz-kdt.183 shrank every moving site and retired none: `enum_map_family`
/// 3 -> 1 at fifteen wrappers, `00277` 3 -> 1 at five and 4 -> 1 or 2 at
/// seven. The sites are the same because the wrapper is the same; the GROUPS
/// fall because the members whose arms asked one question were reducer
/// specializations keyed on a blind list element. With the element in the key
/// most of those members are one member, so there is nothing left to be
/// indistinguishable from. fz-kdt.179 then dissolved the last groups a stand-in
/// could reach (three of `00277`'s wrappers went 2 -> 1; they were `w15`, `w18`
/// and `w19` in the PUBLISHED numbering of the tree that was measured in, and
/// 00277 publishes five wrappers at head, so those names point at nothing now
/// -- nor would they point at the same wrappers in a dump, which is
/// fz-kdt.193's), and fz-kdt.199 drove the remainder to ZERO on every fixture
/// the gate reads. The 44 groups this
/// constant held -- 16 on `00277_enum_tier0_fixture`, 12 on
/// `00420_enum_take_drop_split`, 16 on `enum_map_family`, each at group
/// count 1 -- were construction-wrapper member selections whose members no
/// runtime predicate told apart: two members carrying the same joined
/// accumulator type. Keying a returned accumulator position gives each member
/// its own type, so the selections discriminate and the groups dissolve.
///
/// The emptiness is a CURE and not vacuity, and the ratchet is its own proof:
/// this constant is compared against what the walk FINDS, so the green tree at
/// fz-kdt.199's base is the same walk over the same 13 fixtures reading
/// exactly those 44 groups. The walk did not stop looking; the cause stopped
/// existing.
///
/// But zero here is the strongest thing THIS gate can say, and it reads 13
/// named fixtures -- it is not a proof that no such group exists anywhere.
/// fz-kdt.107 is therefore UNMEASURABLE by this instrument rather than
/// retired, and stays open.
const INDISTINGUISHABLE_ARM_POPULATION: &[(&str, &str, usize)] = &[];

/// The question that clears the last of them, in the program that names it.
///
/// `same_lambda_two_capture_types_dynamic` picks its closure with a `case` on
/// a value that came back out of the mailbox, so no key can pin which lambda
/// reaches `P.run/2`: it arrives as the union of a construction over an int
/// and a construction over a float, and only the word the mint stamped can
/// separate them. Until fz-kdt.127 the test that reads that word could name
/// only the FUNCTION, the two arms asked one and the same question, and arm 0
/// took every value.
///
/// The word a value carries is the address of the construction WRAPPER that
/// minted it, and a wrapper is one function at one capture layout. So the two
/// arms ask about the same function and their capture questions are disjoint,
/// which is what this asserts: the pair separates on the callable axis alone,
/// and no value can pass both tests.
///
/// The static twin `same_lambda_two_capture_types` asks nothing at all --
/// `compiler2_a_forwarded_lambdas_capture_layout_is_the_static_key` pins that.
#[test]
fn compiler2_a_forwarded_lambdas_capture_layout_is_the_runtime_question() {
    let fixture = "fixtures2/behavior/same_lambda_two_capture_types_dynamic.fz";
    let (compiler, program) = driven_backend_program(fixture);
    let types = compiler.world().types();
    let mut separated = Vec::new();
    for entry in artifact_plans(compiler.world(), &program) {
        let asked = entry
            .plan
            .matrix
            .arms
            .iter()
            .map(|arm| {
                arm.questions
                    .iter()
                    .filter_map(|question| match &question.predicate.region {
                        Region::Type(ty) => Some(types.runtime_type_predicate(ty)),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for (index, left) in asked.iter().enumerate() {
            for right in asked.iter().skip(index + 1) {
                let ([left], [right]) = (left.as_slice(), right.as_slice()) else {
                    continue;
                };
                if left.callables.targets() != right.callables.targets() || left.callables.targets().values.len() != 1 {
                    continue;
                }
                assert!(
                    !left.overlaps(right),
                    "{fixture} {}: two constructions of one lambda must put \
                     disjoint questions, or a value reaches a body whose capture lane never \
                     named it -- {left} vs {right}",
                    entry.site,
                );
                separated.push(format!("{}: {left} vs {right}", entry.site));
            }
        }
    }
    assert!(
        !separated.is_empty(),
        "{fixture} delivers one lambda at two capture layouts through a value no key can pin, \
         so some dispatch must separate them by construction; none did, which is fz-kdt.127's \
         defect back again",
    );
}

/// The static twin asks NOTHING: the forwarder key carries the capture types,
/// so each callsite has one callee and the program carries no dispatch plan of
/// any kind -- no call edge, no clause dispatch, no wrapper member selection
/// (fz-kdt.127 stage A, widened to the whole artifact by fz-kdt.178).
///
/// `same_lambda_two_capture_types` forwards ONE lambda -- closed over an int at
/// one callsite and over a float at another -- through `P.run/2`. Every call
/// site in `main` knows which closure it passes, so the only thing that ever
/// made this a runtime question was the forwarder erasure dropping the closure
/// literal WHOLE: one `run` body for two callers whose `twice` consumers were
/// never going to be shared. Erasing the BRAND and keeping the capture TYPES
/// gives `run` one body per capture type, each with a single grounded callee,
/// and the runtime test disappears. Static knowledge flows by KEY.
#[test]
fn compiler2_a_forwarded_lambdas_capture_layout_is_the_static_key() {
    let fixture = "fixtures2/behavior/same_lambda_two_capture_types.fz";
    let (compiler, program) = driven_backend_program(fixture);
    let plans = artifact_plans(compiler.world(), &program);
    assert!(
        plans.is_empty(),
        "{fixture} passes a known closure at every call site, so nothing may be left for a \
         runtime test; {} plan(s) still dispatch: {:?}",
        plans.len(),
        plans.iter().map(|plan| plan.site.to_string()).collect::<Vec<_>>(),
    );

    let types = compiler.world().types();
    let mut keys_by_function: BTreeMap<FunctionId, BTreeSet<String>> = BTreeMap::new();
    for executable in program.executables() {
        let activation = &executable.key.activation;
        let Some(first) = activation.inputs(types).first().copied() else {
            continue;
        };
        keys_by_function
            .entry(activation.function)
            .or_default()
            .insert(types.display(&first));
    }
    let forwarders_split_by_capture_type = keys_by_function
        .values()
        .filter(|slots| {
            slots.len() > 1 && slots.iter().all(|slot| slot.contains("closure")) && {
                let ints = slots.iter().filter(|slot| slot.contains("int")).count();
                let floats = slots.iter().filter(|slot| slot.contains("float")).count();
                ints > 0 && floats > 0
            }
        })
        .count();
    assert_eq!(
        forwarders_split_by_capture_type, 4,
        "`P.run/2`, `P.twice/2` and their `Q` mirrors each take the lambda at an int capture \
         and at a float capture, and the key -- not a test -- is what separates them: {keys_by_function:#?}",
    );
}

/// Drives one fixture to its backend product and names every arm pair, at
/// every plan the artifact carries, that asks one and the same runtime
/// question.
fn indistinguishable_dispatch_arms(fixture: &str) -> Vec<String> {
    let (compiler, program) = driven_backend_program(fixture);
    let types = compiler.world().types();
    let mut findings = Vec::new();
    for entry in artifact_plans(compiler.world(), &program) {
        for twin in indistinguishable_arms(entry.plan, types) {
            findings.push(format!("{} {twin}", entry.site));
        }
    }
    findings
}

/// Drives one fixture to its backend product, and hands back the program with
/// the compiler whose world types it.
fn driven_backend_program(fixture: &str) -> (Compiler2<ConfiguredTelemetry>, Rc<BackendProgram>) {
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    backend.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some(fixture.to_string()),
        text: std::fs::read_to_string(fixture).unwrap_or_else(|error| panic!("read {fixture}: {error}")),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);
    assert!(
        matches!(compiler.drive(), DriveOutcome::Resolved),
        "{fixture} should drive to a settled backend product",
    );
    let program = backend.last(root_id).program;
    (compiler, program)
}

/// Where in the artifact a [`PatternDispatchPlan`] sits.
///
/// The artifact carries FIVE, and every one of them decides which body a
/// runtime value reaches, so every one of them is a seat the census owes an
/// answer about. Three of the five have a `PatternDispatchPlan` field of their
/// own -- `DispatchCallEdge`, `ExecutableDispatch`, `BackendConstructionWrapper`
/// -- and two more ride a `BackendTail`: `BackendTail::Dispatch`'s
/// `ControlDispatch` (a body's own `case`) and `BackendTail::Receive`'s
/// `BackendReceive` (a `receive`'s clauses).
///
/// Two of the five seat their bodies in an order the COMPILER chose, and those
/// are the ones a seat rule may move: a call edge's arms and a wrapper's
/// members. The other three seat them in SOURCE order -- a function's clauses,
/// a `case`'s clauses, a `receive`'s clauses -- and there the first matching
/// clause is what the language means, so moving one would change the program.
/// [`PlanSite::is_source_order`] is that split, and it is what the seat gate
/// and the blind-escape census both read.
enum PlanSite {
    /// A dispatching direct call a body tails into, named by its callsite.
    CallEdge { executable: usize, callsite: u32 },
    /// An executable's own clause dispatch: the function's source clauses.
    Entry { executable: usize },
    /// A body's own `case`, named by the control entry that tails into it.
    Case { executable: usize, entry: usize },
    /// A `receive`'s clause dispatch, named by the control entry that tails
    /// into it.
    Receive { executable: usize, entry: usize },
    /// A construction wrapper's member selection, carrying BOTH of the
    /// wrapper's numbers: the `identity` the artifact publishes (which is its
    /// position in `construction_wrappers`, and what the interpreter's own
    /// errors print) and the `canonical` number
    /// [`canon_backend_program`](crate::compiler2::canon::canon_backend_program)
    /// heads its block with. They are different numbers and they agree only by
    /// accident (fz-kdt.193).
    Selection { wrapper: u32, canonical: usize },
}

impl PlanSite {
    /// The class a census counts this plan under.
    fn kind(&self) -> &'static str {
        match self {
            Self::CallEdge { .. } => "call-edge",
            Self::Entry { .. } => "entry",
            Self::Case { .. } => "case",
            Self::Receive { .. } => "receive",
            Self::Selection { .. } => "selection",
        }
    }

    /// Whether the order this site lists its bodies in is the PROGRAMMER's.
    ///
    /// A function's clauses, a `case`'s clauses and a `receive`'s clauses are
    /// all tried first-match in source order, which is what the language
    /// means; a seat rule that reordered one would change the program. A call
    /// edge's arms and a wrapper's members are the compiler's own order, and
    /// those are the two the seat owns.
    fn is_source_order(&self) -> bool {
        matches!(self, Self::Entry { .. } | Self::Case { .. } | Self::Receive { .. })
    }
}

impl std::fmt::Display for PlanSite {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CallEdge { executable, callsite } => write!(f, "callsite {callsite} (executable {executable})"),
            Self::Entry { executable } => write!(f, "entry dispatch of executable {executable}"),
            Self::Case { executable, entry } => write!(f, "case dispatch at entry e{entry} (executable {executable})"),
            Self::Receive { executable, entry } => write!(f, "receive at entry e{entry} (executable {executable})"),
            Self::Selection { wrapper, canonical } => {
                write!(f, "wrapper w{canonical} (published w{wrapper}) selection")
            }
        }
    }
}

/// One plan the artifact carries, with the bodies it can reach in the order
/// the site itself lists them.
struct ArtifactPlan<'a> {
    site: PlanSite,
    plan: &'a PatternDispatchPlan<Ty>,
    /// The body ids this site offers, in the site's own list order: the call
    /// arms for a call edge, the reachable clause ids for an entry, the member
    /// index for a selection (welded to the plan's rows by fz-kdt.108).
    ///
    /// That list order is the order the runtime reaches them in.
    /// `compiler2_dispatch_lists_its_bodies_in_the_graphs_first_match_order`
    /// holds it to the decision graph, which is the only order execution has.
    bodies: Vec<u32>,
}

/// Every [`PatternDispatchPlan`] a backend program carries, whatever kind of
/// site it sits at.
///
/// A plan is a plan: the runtime walks the same decision graph and reaches a
/// body by the same first-match rule whether the site is a callsite's arms, a
/// function's own clauses, a body's `case`, a `receive`'s clauses or a
/// construction wrapper's members. Walking only the call edges (fz-kdt.178)
/// left the other kinds uncensused, and the dynamic tripwire was reading
/// escapes in a wrapper's member selection that no static gate could see.
///
/// EXHAUSTIVE BY MEASUREMENT, not by hope: the five sites are every field of
/// type `PatternDispatchPlan<Ty>` reachable from a `BackendProgram`, and the
/// two that ride a `BackendTail` are matched here by naming every tail variant
/// that carries one, so a sixth would have to be added to
/// `BackendTail`/`BackendProgram` to escape this walk.
fn artifact_plans<'a>(world: &crate::compiler2::World, program: &'a BackendProgram) -> Vec<ArtifactPlan<'a>> {
    // A selection site is labelled with the number the DUMP prints, so a reader
    // following a failure message into `--dump backend=` lands on the wrapper
    // the message meant (fz-kdt.193).
    let canonical = crate::compiler2::canon::canonical_wrapper_numbers(world, program);
    let mut plans = Vec::new();
    for (index, executable) in program.executables().iter().enumerate() {
        if let Some(entry) = &executable.abi.materialized.entry_dispatch {
            plans.push(ArtifactPlan {
                site: PlanSite::Entry { executable: index },
                plan: entry.plan(),
                bodies: entry.clause_ids().to_vec(),
            });
        }
        let BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for (entry_index, entry) in entries.iter().enumerate() {
            match &entry.tail {
                BackendTail::DirectCall {
                    callsite,
                    target: CallEdge::Dispatch(dispatch),
                    ..
                } => plans.push(ArtifactPlan {
                    site: PlanSite::CallEdge {
                        executable: index,
                        callsite: callsite.as_u32(),
                    },
                    plan: &dispatch.plan,
                    bodies: dispatch.arms.iter().map(|arm| arm.body_id).collect(),
                }),
                // `native.rs` and `ir_interp/backend.rs` both reach the arm by
                // `arm_entries[body_id]`, so the arm order IS the body order.
                BackendTail::Dispatch { dispatch, .. } => plans.push(ArtifactPlan {
                    site: PlanSite::Case {
                        executable: index,
                        entry: entry_index,
                    },
                    plan: &dispatch.plan,
                    bodies: (0..dispatch.arm_entries.len() as u32).collect(),
                }),
                // Same weld on the receive side: the matched clause index is
                // the plan's body id, and `clauses` is in source order.
                BackendTail::Receive(receive) => plans.push(ArtifactPlan {
                    site: PlanSite::Receive {
                        executable: index,
                        entry: entry_index,
                    },
                    plan: &receive.dispatch,
                    bodies: (0..receive.clauses.len() as u32).collect(),
                }),
                _ => {}
            }
        }
    }
    for (index, wrapper) in program.construction_wrappers().iter().enumerate() {
        let Some(selection) = &wrapper.selection else {
            continue;
        };
        plans.push(ArtifactPlan {
            site: PlanSite::Selection {
                wrapper: index as u32,
                canonical: canonical[index],
            },
            plan: selection,
            bodies: (0..wrapper.members.len() as u32).collect(),
        });
    }
    plans
}

/// The order a plan's decision graph actually reaches its bodies in: a walk
/// from the root taking the match edge before the miss edge, recording each
/// outcome the first time it is reached.
///
/// This is the only order execution has -- the runtime executes `plan.graph`
/// and never `plan.matrix.arms` -- so whether a site's own list agrees with it
/// is a measurement, which
/// `compiler2_dispatch_lists_its_bodies_in_the_graphs_first_match_order`
/// takes.
fn graph_first_match_bodies(plan: &PatternDispatchPlan<Ty>) -> Vec<u32> {
    use crate::dispatch_matrix::DispatchNode;

    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![plan.graph.root];
    while let Some(node) = stack.pop() {
        match plan.graph.node(node) {
            None | Some(DispatchNode::Fail) => {}
            Some(DispatchNode::Outcome { outcome, .. }) => {
                if let Some(entry) = plan.outcome(*outcome)
                    && seen.insert(entry.body_id)
                {
                    order.push(entry.body_id);
                }
            }
            Some(DispatchNode::Test { on_match, on_miss, .. }) => {
                stack.push(on_miss.target);
                stack.push(on_match.target);
            }
        }
    }
    order
}

/// fz-kdt.178: every census here reads a plan's bodies off the site's own
/// list, and the runtime reaches them by walking the plan's decision graph.
/// Those are two different orders unless they agree, and this is what says
/// they do.
///
/// They agree BY CONSTRUCTION: `compile_dispatch_matrix` compiles the arms
/// first-match in list order and emits one arm per row, so the graph's
/// first-match walk is the list restricted to the bodies the site offers. An
/// entry site offers only its reachable clause ids, which is a restriction of
/// the same order, so the comparand is the graph order filtered to the bodies
/// the site lists.
///
/// A fact by construction holds only while the construction does, which is why
/// it is a gate: if a producer ever emits a graph that reaches its rows out of
/// order, every seat this file reasons about is read off the wrong list, and
/// nothing else here would say so.
#[test]
fn compiler2_dispatch_lists_its_bodies_in_the_graphs_first_match_order() {
    let mut compared = 0;
    let mut disagreements = Vec::new();
    for fixture in ARM_ORDER_CENSUS {
        let (compiler, program) = driven_backend_program(fixture);
        for entry in artifact_plans(compiler.world(), &program) {
            compared += 1;
            let walked = graph_first_match_bodies(entry.plan)
                .into_iter()
                .filter(|body| entry.bodies.contains(body))
                .collect::<Vec<_>>();
            if walked != entry.bodies {
                disagreements.push(format!(
                    "{fixture} {}: the site lists {:?} and the graph reaches {walked:?}",
                    entry.site, entry.bodies,
                ));
            }
        }
    }
    println!("plans whose list order was held to the graph's first-match order: {compared}");
    assert!(
        disagreements.is_empty(),
        "a plan's bodies must be reached in the order its site lists them, or the seat every census in this \
         file reads is not the seat the runtime takes: {disagreements:#?}",
    );
    assert!(
        compared > 0,
        "the agreement gate compared no plan at all, so it cannot have held anything"
    );
}

/// fz-kdt.131: no seat over the corpus lets a value reach a body its surface
/// never named -- at the settled arrival AND under every arm perturbation the
/// stress can name.
///
/// A blind escape is a seat where the arm tested first does not name what the
/// arm tested second holds while some value satisfies both. Both a CALL EDGE
/// and a construction wrapper's MEMBER SELECTION are seated by the same relation
/// now (fz-kdt.179, `routable_alternatives`), so the seating law -- an arm is
/// moved ahead of a sibling only under `Covering`, which admits no blind escape
/// -- is the debug_assert in `specificity_order` that the fixture matrix drives
/// on every debug compile. This gate reads the LANDED artifact back to the same
/// law, and it reads zero: fz-kdt.119 and fz-kdt.107 gave the tuple and list
/// axes the tests that separated the call-edge pairs, fz-kdt.183 keyed the
/// reducer specializations on the element they carry, and fz-kdt.179 put member
/// selection through the drop and the covering seat.
///
/// THREE POPULATIONS, ONE WALK, because a reading only means something once it
/// says which of them it belongs to: the REACHABLE escapes, which are latent
/// miscompiles; the SOURCE-ORDER escapes -- a function's clauses, a `case`'s,
/// a `receive`'s -- whose order is the programmer's; and the plans the walk
/// could not read at all, counted so that class's zero is honest.
///
/// A pair no value can reach is in none of them. [`seating`] answers
/// `Separated` for it, in this reader and in production alike, and the walk
/// never opens it (fz-kdt.186).
///
/// WHY IT IS DRIVEN UNDER ONE SEED (fz-kdt.143, narrowed by fz-kdt.196). A
/// census read at the settled arrival was once blind to a seat only a legal
/// permutation produced, and until fz-kdt.143 the corpus had such seats: an arm
/// the seat would never let past its stand-in was kept anyway, because
/// fz-kdt.118's drop ran only inside one question group and every axis
/// refinement since had split those groups. Under `arms:2` and `arms:3` this
/// census once read 5 where the settled order pinned 3, the two extras being
/// `dispatch_list_head_separates`'s `[int]` arm seated ahead of the arms that
/// stand in for it. Those arms are dropped now.
///
/// SIX SEEDS WERE SIX READINGS OF ONE FACT, and that is a derivation rather
/// than a hope: fz-kdt.194 gave every separated pair a canonical order and
/// pinned the ARTIFACT's arrival-invariance in its own gate, so a census OF
/// THAT ARTIFACT is arrival-invariant too. Measured by instrumenting this walk
/// to count pairs and verdicts at each arrival: **87 pairs -- 36 `Separated`,
/// 51 `Covering`, 0 `Escaping` -- at the settled arrival AND at every one of
/// seeds 1-6, so all seven arrivals together walk exactly 609 = 87 x 7 pairs
/// with the histogram scaling exactly 7x (252 / 357 / 0).** Not one seed read
/// a pair, or a verdict, the settled arrival did not.
///
/// So ONE seed is kept, not none. The loop is still the permutation ratchet --
/// a future arm axis that re-opens breaks the invariance fz-kdt.194 pins and
/// this walk would then read a pair its gate does not -- and `arms:6` is the
/// seed kept because it is the one that once aborted `enum_map_family` and
/// `enum_predicate_search`. Dropping the other five costs no reading. Measured
/// back to back in a debug build: run alone and serially this gate goes from
/// **108.5 s to 34.1 s of CPU** (109.1 s -> 37.2 s wall), and the lib suite,
/// whose critical path it is, from **705.8 s to 620.9 s of CPU** and
/// 157.5 s -> 105.1 s of wall clock. CPU is the figure to compare: this is a
/// shared machine and the suite's wall clock swings with what else is on it.
///
/// INJECTION RECIPE, so this zero is a cure and not a blind spot. In
/// `callsite_dispatch::seats_before`, widen the `covering` closure to
/// `Seating::Covering | Seating::Escaping` and delete `specificity_order`'s two
/// `debug_assert`s (which otherwise catch the injection before an artifact
/// lands). Production then seats blind arms ahead, and this gate FAILS on its
/// `Reachable` assert reporting **25 escapes at the settled arrival** -- and
/// the injected population is arrival-invariant too, reading the same 137 pairs
/// / 36 `Separated` / 76 `Covering` / **25 `Escaping`** at settled and at each
/// of seeds 1-6. The injection is caught by the settled reading alone, which is
/// the same measurement that says the extra seeds bought nothing.
///
/// The census is a RATCHET, not a target: a new entry under ANY setting is a
/// new latent miscompile and wants a ticket, not a re-blessed constant.
#[test]
fn compiler2_dispatch_blind_escape_census_is_the_known_population() {
    let settled = blind_escape_census();
    println!(
        "plans walked: {:?}; plans the census cannot read: {:?}",
        settled.plans, settled.unreadable,
    );
    assert_eq!(
        settled.source_order_plans(),
        SOURCE_ORDER_PLANS_ON_THE_CENSUS,
        "a source-order class that reports no blind escape says nothing unless it also says how many of \
         its plans it could read: {:?}",
        settled.unreadable,
    );
    let reachable = seated_escapes(&settled, EscapeClass::Reachable);
    assert!(
        reachable.is_empty(),
        "the corpus carries no reachable blind escape at the settled arrival: fz-kdt.119 and fz-kdt.107 \
         gave the tuple and list axes the tests that separate the call-edge pairs, fz-kdt.183 keyed the \
         reducer specializations on the list element they carry, and fz-kdt.179 made construction-wrapper \
         member selection run the drop and the covering seat -- so a new entry here is a new latent \
         miscompile and wants a ticket, not a re-blessed constant: {reachable:#?}",
    );
    assert_eq!(
        seated_escapes(&settled, EscapeClass::SourceOrder),
        SOURCE_ORDER_BLIND_ESCAPES,
        "a clause order -- a function's, a `case`'s or a `receive`'s -- is the programmer's, so a blind \
         escape there is a source-level fact with a repr-level cure, and it gets its own population rather \
         than a seat finding",
    );
    // A permuted arrival is one the fixpoint could have delivered, so a blind
    // pair any legal arm order reaches is a pair production could ship. None
    // does: the reachable and source-order populations are empty at the seed as
    // well as at the settled arrival (fz-kdt.143's red-first drive, kept as an
    // emptiness ratchet now that the call-edge and selection populations it once
    // tracked have both retired). ONE seed, not six: see the derivation above.
    for setting in BLIND_ESCAPE_CENSUS_STRESSES {
        let _stress = crate::compiler2::callsite_dispatch::dispatch_stress::DispatchStressed::install(
            crate::compiler2::callsite_dispatch::dispatch_stress::setting(setting),
        );
        let pairs = escaping_pairs(&blind_escape_census());
        assert!(
            pairs.is_empty(),
            "FZ_STRESS_PERMUTE_DISPATCH={setting} reached a blind pair the settled arrival does not, which \
             is an arrival production could deliver: {pairs:#?}",
        );
    }
}

/// The permuted arrivals the blind-escape census is read at, beside the settled
/// one.
///
/// ONE seed, because the census is a reading of an ARTIFACT fz-kdt.194 pins as
/// arrival-invariant, and the measurement in
/// `compiler2_dispatch_blind_escape_census_is_the_known_population`'s doc says
/// so outright: all seven arrivals walked the same 87 pairs with the same 36 /
/// 51 / 0 histogram. `arms:6` is kept rather than none because a re-opened arm
/// axis is exactly what this loop is the ratchet for, and it is that seed
/// rather than another because it is the arrival that once aborted
/// `enum_map_family` and `enum_predicate_search` (see [`ARM_ORDER_STRESSES`]).
const BLIND_ESCAPE_CENSUS_STRESSES: [&str; 1] = ["arms:6"];

/// Which population a blind pair belongs to.
///
/// One reading, two owners, because the cure differs: a seat can move the
/// first, and only a repr or a sharper test can help the second. A pair no
/// value can reach is in neither -- [`seating`] answers `Separated` for it and
/// the walk never opens it (fz-kdt.186).
#[derive(Clone, Copy, PartialEq)]
enum EscapeClass {
    /// A call-edge or wrapper-selection pair some value can satisfy both
    /// halves of, so the seat between them decides which body it reaches.
    Reachable,
    /// A function's own clause dispatch, a body's `case`, or a `receive`:
    /// sites where the order is the programmer's and the cure is never a seat.
    SourceOrder,
}

/// One reading of the census: where it was found, and the two surfaces that
/// meet blind there.
struct BlindEscape {
    class: EscapeClass,
    site: String,
    early: String,
    late: String,
}

/// A census pass: every blind pair the walk found, and what it was able to
/// look at while finding them.
struct BlindEscapeCensus {
    escapes: Vec<BlindEscape>,
    /// How many plans of each site kind the walk saw.
    plans: BTreeMap<&'static str, usize>,
    /// The plans whose surfaces could not be read, by site kind and by the
    /// question variant that stopped the read. fz-kdt.187 reads the readable
    /// ones; a `Guard` genuinely cannot be read at all.
    unreadable: BTreeMap<(&'static str, &'static str), usize>,
}

impl BlindEscapeCensus {
    /// How many plans of one site kind the walk could not read.
    fn unreadable_plans_of(&self, kind: &str) -> usize {
        self.unreadable
            .iter()
            .filter(|((candidate, _), _)| *candidate == kind)
            .map(|(_, count)| *count)
            .sum()
    }

    /// Every SOURCE-ORDER kind the walk saw, with how many plans it saw and
    /// how many of those it could not read -- the comparand
    /// [`SOURCE_ORDER_PLANS_ON_THE_CENSUS`] pins so the class's zero says how
    /// much of itself it speaks for.
    fn source_order_plans(&self) -> Vec<(&'static str, usize, usize)> {
        let mut rows = self
            .plans
            .iter()
            .filter(|(kind, _)| matches!(**kind, "entry" | "case" | "receive"))
            .map(|(kind, plans)| (*kind, *plans, self.unreadable_plans_of(kind)))
            .collect::<Vec<_>>();
        rows.sort();
        rows
    }
}

/// Every seat in the census fixtures where the arm tested first does not name
/// what the arm tested second holds, under whatever arrival this thread's
/// stress setting asks for: where it happens, which population it belongs to,
/// and the two surfaces that meet.
///
/// Every plan the artifact carries is walked -- call edge, entry dispatch and
/// wrapper selection alike -- and the ones the reader cannot read are counted
/// rather than passed over, so an empty class says how much of itself it
/// speaks for.
fn blind_escape_census() -> BlindEscapeCensus {
    let mut census = BlindEscapeCensus {
        escapes: Vec::new(),
        plans: BTreeMap::new(),
        unreadable: BTreeMap::new(),
    };
    for fixture in ARM_ORDER_CENSUS {
        let (compiler, program) = driven_backend_program(fixture);
        let types = compiler.world().types();
        for entry in artifact_plans(compiler.world(), &program) {
            *census.plans.entry(entry.site.kind()).or_default() += 1;
            if let Some(reason) = unreadable_reason(entry.plan, &entry.bodies) {
                *census.unreadable.entry((entry.site.kind(), reason)).or_default() += 1;
                continue;
            }
            let seated = seated_arm_surfaces(entry.plan, &entry.bodies);
            for early in 0..seated.len() {
                for late in early + 1..seated.len() {
                    if seating(types, &seated[early], &seated[late]) == Seating::Separated {
                        continue;
                    }
                    let class = match entry.site.is_source_order() {
                        true => EscapeClass::SourceOrder,
                        false => EscapeClass::Reachable,
                    };
                    for subject in blind_escapes(types, &seated[early], &seated[late]) {
                        census.escapes.push(BlindEscape {
                            class,
                            site: format!("{fixture} {} subject {}", entry.site, subject.0),
                            early: types.display(&seated[early][&subject]),
                            late: types.display(&seated[late][&subject]),
                        });
                    }
                }
            }
        }
    }
    census
}

/// The census as SEATS, one class at a time: which surface the plan tests
/// first.
fn seated_escapes(census: &BlindEscapeCensus, class: EscapeClass) -> Vec<String> {
    let mut seated = census
        .escapes
        .iter()
        .filter(|escape| escape.class == class)
        .map(|escape| format!("{}: {} is seated before {}", escape.site, escape.early, escape.late))
        .collect::<Vec<_>>();
    seated.sort();
    seated
}

/// The census as PAIRS: which two surfaces meet blind, with the seat
/// forgotten, so an arrival that flips an arrival-kept pair reads the same.
/// Both classes are here, and the SITE says which: whether an order is the
/// programmer's is a fact about the site, so no arrival can move a pair
/// between them.
fn escaping_pairs(census: &BlindEscapeCensus) -> Vec<String> {
    let mut pairs = census
        .escapes
        .iter()
        .map(|escape| {
            let (first, second) = match escape.early <= escape.late {
                true => (&escape.early, &escape.late),
                false => (&escape.late, &escape.early),
            };
            format!("{}: {first} with {second}", escape.site)
        })
        .collect::<Vec<_>>();
    pairs.sort();
    pairs
}

/// The blind escapes at the SOURCE-ORDER sites: a function's own clause
/// dispatch, a body's `case`, a `receive`'s clauses.
///
/// Empty, and the emptiness is the finding: the seat gate excludes these three
/// because their order is the programmer's, so this is the only place a blind
/// clause pair would be counted, and there are none.
///
/// [`SOURCE_ORDER_PLANS_ON_THE_CENSUS`] says how much of the class that zero
/// speaks for.
const SOURCE_ORDER_BLIND_ESCAPES: &[&str] = &[];

/// How many plans of each source-order kind the census walks, and how many of
/// them it cannot read: `(kind, plans, unreadable)`.
///
/// A clause dispatch asks whatever the source patterns ask, and
/// [`seated_arm_surfaces`] compares `Region::Type` questions only, so most
/// entry plans and every `case` here are skipped. Pinning the numbers per kind
/// is what stops [`SOURCE_ORDER_BLIND_ESCAPES`] from being an honest-looking
/// zero over a class nobody looked at. The gate prints the variant breakdown
/// beside them, and reading the readable variants is fz-kdt.187's.
///
/// A kind that reads zero plans is ABSENT here rather than zero, because the
/// walk only reports the kinds it saw; a row appearing or leaving is the
/// census fixtures changing shape, which wants looking at either way.
///
/// fz-kdt.183: `entry` 144 -> 153 plans, 137 -> 146 unreadable. Nine more
/// entry plans exist because a demanded list element keys nine more reducer
/// specializations apart, and every one of them asks a `Region::List`
/// question, which this walk does not read -- so the readable denominator is
/// unchanged and the zero above still speaks for exactly what it did.
/// fz-kdt.199: `entry` 153 -> 169 plans, 146 -> 162 unreadable. Sixteen more
/// entry plans exist because a returned accumulator keys its seed apart from
/// its ascent, and every one of them asks a `Region::List` or
/// `Region::TupleArity` question, which this walk does not read -- so the
/// READABLE denominator is 7 either way and the zero above still speaks for
/// exactly what it did.
/// fz-kdt.120: `entry` 169 -> 171 plans, 162 -> 164 unreadable, and both new
/// plans are `Region::TupleArity` (25 -> 27; every other variant is flat). The
/// two are one apiece on `00420_enum_take_drop_split` and
/// `behavior/enum_take_drop_split`: with the fz-f98.16 empty-list veto gone,
/// `List.reduce_while_step/3` keys on the accumulator the fold really carries,
/// `{:cont | :halt, []} | {:cont, [int]}`, where the veto had erased the seed
/// rung and left `{:cont, [int]}` alone -- so each fixture's artifact gains two
/// dispatch plans and its `tuple_arity` questions go 21 -> 28. The READABLE
/// denominator is 7 either way and the zero above still speaks for exactly what
/// it did.
const SOURCE_ORDER_PLANS_ON_THE_CENSUS: &[(&str, usize, usize)] =
    &[("case", 3, 3), ("entry", 171, 164), ("receive", 2, 0)];

/// The subjects at which seating `early` before `late` lets a value reach a
/// body that never named it: the two arms put one and the same question there,
/// so nothing the plan emits separates them, and `late`'s surface holds values
/// `early`'s does not.
fn blind_escapes(types: &Types, early: &BTreeMap<SubjectId, Ty>, late: &BTreeMap<SubjectId, Ty>) -> Vec<SubjectId> {
    if early.len() != late.len() {
        return Vec::new();
    }
    early
        .iter()
        .filter(|(subject, early)| {
            late.get(subject).is_some_and(|late| {
                // Trigger on the relation production's `covers` actually
                // consults -- erasing overlap -- not on predicate EQUALITY.
                // At the fz-kdt.129 baseline both triggers count the same 19
                // escapes (equal predicates overlap on their erasing axes),
                // so this correction is verifiable in place; under a REFINED
                // axis (fz-kdt.119 tuples, fz-kdt.107 step 3 lists) equality
                // under-triggers exactly when the census number becomes the
                // headline (fz-kdt.142).
                types
                    .runtime_type_predicate(early)
                    .overlaps_on_an_erasing_axis(&types.runtime_type_predicate(late))
                    && !types.is_subtype(late, early)
            })
        })
        .map(|(subject, _)| *subject)
        .collect()
}

/// What one seated pair asks of a seat, read back off the LANDED artifact.
///
/// ONE RELATION, TWO READERS: this mirrors `callsite_dispatch::Seating`
/// exactly, and this file is the only place the whole materialization path can
/// be held to it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Seating {
    /// The plan's own tests keep the two arms apart outright: at some subject
    /// their predicates are DISJOINT, so no value satisfies both and no seat
    /// between them routes anything. Not a blind escape, not a seat finding,
    /// and not a population -- there is nothing there (fz-kdt.186).
    Separated,
    /// Some value reaches both, and wherever the tests cannot separate it
    /// `early`'s surface already names everything `late` holds.
    Covering,
    /// Some value reaches both, and at some subject the test is blind while
    /// `late` holds values `early` does not name.
    Escaping,
}

/// How the plan's own tests relate these two arms.
///
/// A row is a CONJUNCTION over its subjects, so the two arms admit a common
/// call only where EVERY subject admits a common value; where one does not,
/// the pair is separated and neither half of the coverage question applies.
///
/// A subject the two arms ask IDENTICALLY separates nothing -- it admits the
/// same set to both, whatever that set is -- and saying so is what keeps an
/// unrealizable projected test from deciding a reading, exactly as production's
/// `callsite_dispatch::seating` does.
fn seating(types: &Types, early: &BTreeMap<SubjectId, Ty>, late: &BTreeMap<SubjectId, Ty>) -> Seating {
    let reaches_both = early.len() == late.len()
        && early.iter().all(|(subject, early)| {
            late.get(subject).is_some_and(|late| {
                let (early, late) = (types.runtime_type_predicate(early), types.runtime_type_predicate(late));
                early == late || early.overlaps(&late)
            })
        });
    if !reaches_both {
        return Seating::Separated;
    }
    match blind_escapes(types, early, late).is_empty() {
        true => Seating::Covering,
        false => Seating::Escaping,
    }
}

/// Why the census cannot read a plan's surfaces, if it cannot: the first
/// question variant that is not a `Region::Type`, or the broken weld that
/// leaves a listed body with no arm to read.
///
/// This is the same condition [`seated_arm_surfaces`] gives up on, named
/// instead of silent, so a class whose census reads zero also says how much of
/// itself it actually looked at. Reading the readable variants -- a
/// `Region::List` is a shape test over the value exactly as a `Region::Type`
/// is -- is fz-kdt.187's.
fn unreadable_reason(plan: &PatternDispatchPlan<Ty>, bodies: &[u32]) -> Option<&'static str> {
    for body_id in bodies {
        let Some(outcome) = plan.outcomes.iter().find(|outcome| outcome.body_id == *body_id) else {
            return Some("a listed body has no outcome");
        };
        let Some(arm) = plan.matrix.arms.iter().find(|arm| arm.outcome == outcome.outcome) else {
            return Some("an outcome has no arm");
        };
        for question in &arm.questions {
            let variant = match &question.predicate.region {
                Region::Type(_) => continue,
                Region::Equal(_) => "Region::Equal",
                Region::TupleArity(_) => "Region::TupleArity",
                Region::List(_) => "Region::List",
                Region::MapKind => "Region::MapKind",
                Region::MapKeyPresent { .. } => "Region::MapKeyPresent",
                Region::Bitstring(_) => "Region::Bitstring",
                Region::Guard(_) => "Region::Guard",
            };
            return Some(variant);
        }
    }
    None
}

/// A plan's bodies in the order its site seats them, each as the observable
/// surface it puts to every subject it asks about.
///
/// The surface, not only the predicate projected from it: the projection is
/// exactly what a seat may not be reasoned from alone, so both halves have to
/// come off the artifact together.
///
/// An arm asking a question the plan does not put through `Region::Type` is not
/// a test this can compare, and the whole plan is skipped rather than guessed
/// at. That skip is silent no longer: [`unreadable_reason`] names it, the
/// census counts it and [`SOURCE_ORDER_PLANS_ON_THE_CENSUS`] pins it, and
/// reading the readable variants is fz-kdt.187's.
fn seated_arm_surfaces(plan: &PatternDispatchPlan<Ty>, bodies: &[u32]) -> Vec<BTreeMap<SubjectId, Ty>> {
    let mut seated = Vec::new();
    for body_id in bodies {
        let Some(outcome) = plan.outcomes.iter().find(|outcome| outcome.body_id == *body_id) else {
            return Vec::new();
        };
        let Some(arm) = plan.matrix.arms.iter().find(|arm| arm.outcome == outcome.outcome) else {
            return Vec::new();
        };
        let mut asked = BTreeMap::new();
        for question in &arm.questions {
            let Region::Type(ty) = &question.predicate.region else {
                return Vec::new();
            };
            asked.insert(question.predicate.subject, *ty);
        }
        seated.push(asked);
    }
    seated
}

/// The arm pairs whose runtime questions are the same question.
///
/// A question the plan does not answer through `RuntimeTypePredicate` (a
/// guard, say) makes the plan unprovable and is skipped rather than guessed
/// at. One arm's questions merely CONTAINING another's is not this relation:
/// nested regions are how dispatch is supposed to work, and either order
/// routes each value to the arm that named it.
fn indistinguishable_arms(plan: &PatternDispatchPlan<Ty>, types: &Types) -> Vec<String> {
    let mut asked = Vec::new();
    for arm in &plan.matrix.arms {
        let mut questions = std::collections::BTreeMap::new();
        for question in &arm.questions {
            let Region::Type(ty) = &question.predicate.region else {
                return Vec::new();
            };
            questions.insert(question.predicate.subject, types.runtime_type_predicate(ty));
        }
        asked.push((arm.id, questions));
    }
    let mut twins = Vec::new();
    for (left, (left_id, left_questions)) in asked.iter().enumerate() {
        for (right_id, right_questions) in asked.iter().skip(left + 1) {
            if left_questions == right_questions {
                twins.push(format!("arm a{} asks arm a{}'s question", left_id.0, right_id.0));
            }
        }
    }
    twins
}

/// The fixtures fz-kdt.107's census found carrying dispatch arms one runtime
/// question cannot separate -- 17 groups across 10 fixtures -- plus the one
/// fz-kdt.118 added for the group it dissolves, the two fz-kdt.125 added for
/// the callable-identity shape, and the one fz-kdt.129 added for the seat a
/// blind list test would otherwise take.
///
/// fz-kdt.107 step 3 adds `dispatch_list_head_separates`. Its
/// `List.reduce_while_cont/3` callsite settles FOUR arms and seats TWO of
/// them: the head question separates the `[:false | :true]` and
/// `[int | :ok | :true]` arms from each other's values only where their heads
/// are disjoint, and the other two, `[int]` and `[int | :ok]`, are dropped
/// because `[int | :ok | :true]` stands in for each and no seat would put
/// either first (fz-kdt.143). The pair that survives is the fz-kdt.131
/// facet-3 reproducer this census is here to hold.
///
/// WHAT IS IN IT (fz-kdt.178): every fixture a corpus walk of all five plan
/// kinds found carrying a blind pair or a pair one question cannot separate.
/// The `case` and `receive` kinds put none of them anywhere: over the 469
/// drivable fixtures the corpus carries 70 `case` plans and 86 `receive`
/// plans, 156 of which read zero blind pairs, because a `case` or a `receive`
/// asks `Region::Equal`, `TupleArity`, `List`, `MapKind`, `Bitstring` or a
/// guard and almost never a bare `Region::Type` -- the same reason the entry
/// class reads what it reads, and the same fz-kdt.187 that would widen it.
/// The seven at the end were outside this census while the walk saw call edges
/// alone -- `mailbox_closure_enum_hofs` was in no census at all, and the other
/// six were in `WRAPPER_MEMBER_CENSUS` only, which measures whether an
/// artifact MOVES under a permuted wrapper order and not what its plans then
/// ask.
///
/// `00420_enum_take_drop_split` and `enum_take_drop_split` are the last two
/// the corpus walk found: each carried four wrapper-selection seat findings on
/// four adjacent wrappers that fz-kdt.179 has since cured -- `w21`-`w24` in the
/// PUBLISHED numbering of the tree they were measured in, which is neither the
/// numbering of this tree nor the one a dump prints (fz-kdt.193) -- and they
/// stay in the census
/// because their wrapper member selections still exercise the weld gate and the
/// blind-escape walk under every seed -- the ratchet that would catch a
/// regression of that cure.
const ARM_ORDER_CENSUS: [&str; 22] = [
    "fixtures2/behavior/dispatch_seat_element_blind.fz",
    "fixtures2/behavior/dispatch_list_head_separates.fz",
    "fixtures2/00231_joined_fn_refs_enum_reduce.fz",
    "fixtures2/00275_enum_count_member_reduce.fz",
    "fixtures2/00277_enum_tier0_fixture.fz",
    "fixtures2/00281_opaque_reducer_closure.fz",
    "fixtures2/behavior/enum_map_family.fz",
    "fixtures2/behavior/enum_predicate_search.fz",
    "fixtures2/behavior/enum_reduce_halt_arm_order.fz",
    "fixtures2/behavior/fz_f98_range_map_converges.fz",
    "fixtures2/behavior/opaque_fn_value_join.fz",
    "fixtures2/behavior/range_enumerable.fz",
    "fixtures2/behavior/repr_seam_enum_count_after_reduce2.fz",
    "fixtures2/behavior/closure_identity_tag_split.fz",
    "fixtures2/behavior/closure_identity_captures.fz",
    "fixtures2/00276_enum_to_list_and_map.fz",
    "fixtures2/behavior/enum_hof_three_distinct_closures.fz",
    "fixtures2/behavior/list_literal_trailing_call.fz",
    "fixtures2/behavior/mailbox_closure_enum_hofs.fz",
    "fixtures2/behavior/map_enumerable.fz",
    "fixtures2/00420_enum_take_drop_split.fz",
    "fixtures2/behavior/enum_take_drop_split.fz",
];

/// The fixtures whose CONSTRUCTION-WRAPPER member order is free: compiling each
/// under a permuted wrapper order moves its `BackendProgram` canon, and
/// compiling it under the settled one does not.
///
/// A callable value's construction wrapper carries one member per surviving
/// first-class surface it can be invoked at, and both the member list and the
/// selection plan are derived from one seated order (`construction_member_selection`
/// returns the surviving member indices and transport walks exactly them,
/// `jobs/transport.rs`). The surfaces arrive as a `BTreeSet` walked in
/// interned-surface order -- the type interner's mint order, which is the
/// agenda's -- so that order is the scheduler's, exactly like a callsite's
/// arrival order, and exactly as free to move.
///
/// This is the census the retired `FZ_STRESS_REVERSE_DISPATCH_ARMS` never
/// touched at all (fz-kdt.136). Measured at this commit by sweeping the corpus
/// under `wrappers:` seeds and diffing the backend dump; eleven of the nineteen
/// are named by [`ARM_ORDER_CENSUS`] too, which walks the same wrappers'
/// selection PLANS rather than whether their artifact moves.
const WRAPPER_MEMBER_CENSUS: [&str; 19] = [
    "fixtures2/00183_enum_take_list_range.fz",
    "fixtures2/00197_poly_capture_ref.fz",
    "fixtures2/00230_enum_take_chained.fz",
    "fixtures2/00276_enum_to_list_and_map.fz",
    "fixtures2/00277_enum_tier0_fixture.fz",
    "fixtures2/00391_poly_capture_ref.fz",
    "fixtures2/00418_enum_count_range.fz",
    "fixtures2/00419_enum_take_mixed.fz",
    "fixtures2/00420_enum_take_drop_split.fz",
    "fixtures2/behavior/dispatch_seat_element_blind.fz",
    "fixtures2/behavior/enum_hof_three_distinct_closures.fz",
    "fixtures2/behavior/enum_map_family.fz",
    "fixtures2/behavior/enum_predicate_search.fz",
    "fixtures2/behavior/enum_take_drop_split.fz",
    "fixtures2/behavior/fz_f98_range_map_converges.fz",
    "fixtures2/behavior/list_literal_trailing_call.fz",
    "fixtures2/behavior/map_enumerable.fz",
    "fixtures2/behavior/opaque_fn_mixed_return.fz",
    "fixtures2/behavior/unused_range_binding.fz",
];

/// The arrival-order settings the in-process gate drives.
///
/// `arms:reverse` is the retired knob's exact permutation, kept because the
/// fixtures and the prose around it were measured under it. The seeds are why
/// this gate has teeth the reversal did not: measured at fz-kdt.141's landing,
/// `arms:reverse` moved 8 fixtures' artifacts and a seed moved 27 (both are 0
/// at `ca23b676f` + fz-kdt.194, which is what
/// `compiler2_a_permuted_arm_order_renders_the_same_artifact` ratchets; this
/// gate holds the ANSWER, which was invariant throughout). The two
/// seeds here are the ones that named the four native aborts fz-kdt.107 step 3
/// then killed -- seed 1 aborted `00277` and `dispatch_seat_element_blind`,
/// seed 6 aborted `enum_map_family` and `enum_predicate_search` -- and they
/// are kept because those are the arrivals that reach the seats, not because
/// anything still aborts under them.
const ARM_ORDER_STRESSES: [&str; 3] = ["arms:reverse", "arms:1", "arms:6"];

/// The construction-member settings the in-process gate drives. Two seeds,
/// because most wrappers carry exactly two members and one seed is one of the
/// two orders they can be in.
const WRAPPER_MEMBER_STRESSES: [&str; 2] = ["wrappers:1", "wrappers:6"];

/// fz-kdt.118 / fz-kdt.107 / fz-kdt.141: the two orders that decide which body
/// a value reaches are the scheduler's, so no answer may depend on either.
///
/// A callsite's ARRIVAL order is the settled targets' order, which is the
/// semantic fixpoint's, which is the agenda's. A callable's CONSTRUCTION-
/// WRAPPER member order is a `BTreeSet<CallableSurface>` walked in interned-id
/// order, which is the type interner's mint order, which is the agenda's again.
/// Any permutation of either is an order the fixpoint could legally have
/// delivered, so an answer that moves under one is an answer a schedule
/// decides. This is the only gate that catches the class: the corpus's own two
/// schedules never disagree about these orders (FIFO and LIFO are stdout-
/// identical on all 584 fixtures), so the miscompiling orders stay legal but
/// unproduced until something perturbs them.
///
/// WHY THIS GATE IS NOT THE REVERSAL GATE IT REPLACES (fz-kdt.141). The
/// retired `FZ_STRESS_REVERSE_DISPATCH_ARMS` mirrored the members of each
/// runtime-indistinguishable GROUP, and nothing else. That reaches one
/// permutation of exactly the pairs the plan cannot separate -- so as
/// fz-kdt.119 taught the predicate to separate more of them the same knob got
/// weaker, and on a callsite whose groups are all singletons it is the
/// IDENTITY -- and at `ca23b676f` + fz-kdt.194 every group on the corpus IS a
/// singleton, so it moves nothing at all. Measured at that head over the
/// 604-fixture corpus: reversal moves 0 fixtures' artifacts and a seeded arm
/// permutation moves 0 as well (22 without fz-kdt.194's canonical order over
/// separated pairs), while a wrapper seed still moves 19. So the arm gates
/// below assert an invariance the perturbation can no longer break by
/// reordering separated arms; what they still reach is a permuted arrival
/// running through the drop and the seat.
///
/// RED AT 788c0c21f on `enum_reduce_halt_arm_order`, which returned
/// `{:done, 3}` for `{:halted, 3}` when the narrow `{:cont, int}` arm was
/// listed first (fz-kdt.118 fixed it).
///
/// This gate drives the INTERPRETER, which is where every fixture's answer is
/// defined and where a mis-seated value survives on its dynamic tag. The
/// native doors agree. Four fixtures USED to abort under a legal arm order --
/// `enum_map_family`, `00277_enum_tier0_fixture`, `dispatch_seat_element_blind`
/// and `enum_predicate_search` -- all in one class: three list arms whose
/// bodies use incompatible element accessors, no one of which covers another,
/// so `fz_list_head_int_ref` read non-int elements as ints. fz-kdt.107 step 3
/// gave the list axis a head question and killed the class; measured on the
/// JIT door at the fz-kdt.143 landing, all 28 combinations of those four
/// fixtures with `arms:reverse` and seeds 1-6 exit 0. Reproduce outside the
/// harness, where an abort could not take the suite down with it:
///
///     FZ_STRESS_PERMUTE_DISPATCH=arms:1 \
///       cargo run --bin fz2 -- run fixtures2/behavior/dispatch_seat_element_blind.fz
///
/// The full recipe -- every fixture, every door, N seeds -- is in
/// `.agent/docs/dispatch-matrix.md`.
#[test]
fn compiler2_dispatch_answers_the_same_under_a_permuted_arm_order() {
    assert_no_answer_moves(&ARM_ORDER_CENSUS, &ARM_ORDER_STRESSES);
}

/// The same law on the other free order: which construction-wrapper member a
/// callable value's invocation reaches is decided by the mint order the members
/// were derived in, and nothing else.
///
/// This half is what fz-kdt.136 found missing. It is green on stdout at this
/// commit, on every door. Until fz-kdt.179 it was green OVER a live hazard: the
/// surface-membership tripwire read 12 escapes on `00277_enum_tier0_fixture` at
/// the SETTLED wrapper order and 0 under `wrappers:1`/`wrappers:6`/
/// `wrappers:reverse`, because the member the mint order put first took values
/// its surface never named and only a permutation happened to put a covering
/// member there instead. Member selection runs the drop and the covering seat
/// now, so the settled order reads 0 as well -- but identical answers still are
/// not the same claim as safe routing, and
/// `compiler2_no_value_reaches_a_construction_member_that_never_named_it` holds
/// the other half;
/// `compiler2_a_permuted_wrapper_order_reseats_the_construction_members` is
/// what proves the perturbation still lands.
#[test]
fn compiler2_dispatch_answers_the_same_under_a_permuted_wrapper_order() {
    assert_no_answer_moves(&WRAPPER_MEMBER_CENSUS, &WRAPPER_MEMBER_STRESSES);
}

/// Each fixture's answer, under the settled order and under every setting.
fn assert_no_answer_moves(fixtures: &[&str], stresses: &[&str]) {
    for fixture in fixtures {
        let settled = settled_arm_order_answer(fixture);
        for stress in stresses {
            let permuted = {
                let _stress = crate::compiler2::callsite_dispatch::dispatch_stress::DispatchStressed::install(
                    crate::compiler2::callsite_dispatch::dispatch_stress::setting(stress),
                );
                interpreted_answer(fixture)
            };
            assert_eq!(
                permuted, settled,
                "{fixture} under FZ_STRESS_PERMUTE_DISPATCH={stress}: permuting an order the \
                 fixpoint chose is a legal arrival, so it must not change a single answer",
            );
        }
    }
}

/// A value never reaches a body whose surface never named it, on any fixture
/// [`SURFACE_MEMBERSHIP_CENSUS`] names, at any arrival it names.
///
/// A dispatch test is a PROJECTION of the surface an arm was compiled for, so
/// passing the test is not the same as belonging to the surface. Where the two
/// part company, a body typed for one domain runs on a value from another. The
/// `FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP` tripwire measures that gap on the
/// production interpreter path by re-asking each admitted value's own test
/// under `PositionScope::Full`; this is the same census the shell recipe in
/// `.agent/docs/dispatch-matrix.md` reads off stderr, driven in process so the
/// population cannot grow unnoticed.
///
/// TWO ASSERTIONS, IN THIS ORDER, because a zero has two ways of being wrong
/// (fz-kdt.187). First: the row OBSERVED something. A fixture whose wrappers
/// have collapsed to single members runs no dispatch, so its escape count is 0
/// no matter what the compiler does, and the row is watching an empty room --
/// that is a stale row, not a green one, and it gets its own finding. Only then:
/// the observations and the escapes are the two numbers
/// [`SURFACE_MEMBERSHIP_CENSUS`] pins.
///
/// A RATCHET, not a blessing: see the table's own doc for what each row holds
/// and what moving one means.
#[test]
fn compiler2_no_value_reaches_a_construction_member_that_never_named_it() {
    let mut blind = Vec::new();
    let mut moved = Vec::new();
    for (fixture, setting, observed, expected) in SURFACE_MEMBERSHIP_CENSUS {
        let _stress = crate::compiler2::callsite_dispatch::dispatch_stress::DispatchStressed::install(
            crate::compiler2::callsite_dispatch::dispatch_stress::setting(setting),
        );
        let census = crate::runtime_type_predicate::surface_membership::SurfaceMembershipCensus::install();
        interpreted_answer(fixture);
        let (observations, escapes) = (census.observations(), census.escapes());
        let arrival = if setting.is_empty() {
            "the settled arrival"
        } else {
            setting
        };
        if observations == 0 {
            blind.push(format!("{fixture} under {arrival}"));
        }
        if (observations, escapes) != (observed, expected) {
            moved.push(format!(
                "{fixture} under {arrival}: {observations} observations / {escapes} escapes, census says \
                 {observed} / {expected}"
            ));
        }
    }
    assert!(
        blind.is_empty(),
        "a row that observes nothing reports no escape for the same reason an empty room is quiet, so its \
         zero says `nothing was looked at` rather than `nothing escaped` -- re-home it onto a fixture and \
         arrival that still reach a dispatch, or delete it and say why: {}",
        blind.join("; "),
    );
    assert!(
        moved.is_empty(),
        "a value that passes an arm's test but lies outside the surface that arm was compiled for is \
         running a body that never named it -- the arm is missing, not the test; and an observation count \
         that moves is the row's denominator changing under it: {}",
        moved.join("; "),
    );
}

/// The measured surface-membership population: fixture, arrival, observations,
/// escapes. `""` is the settled arrival, and every other string is a
/// `FZ_STRESS_PERMUTE_DISPATCH` setting the fixpoint could legally have
/// delivered instead.
///
/// OBSERVATIONS ARE THE DENOMINATOR, and without them a row cannot be read
/// (fz-kdt.187). `observe` fires once per `Region::Type` question a running
/// dispatch plan MATCHES, so a fixture that runs no such question reports no
/// escape for the same reason an empty room is quiet: its 0 says "nothing was
/// looked at", not "nothing escaped". The gate asserts the count is positive
/// before it reads the escapes, and pins it, so a row cannot go blind in
/// silence.
///
/// The list-tail reading (fz-kdt.144) replaced the tuple-era population, which
/// fz-kdt.132 emptied and fz-kdt.138 then made empty by construction. The first
/// seven rows are that tuple-era population, kept at 0 because a table that
/// only lists what escapes cannot say that anything stopped escaping.
///
/// **`00277_enum_tier0_fixture` and `enum_predicate_search` are GONE from this
/// table, and the observation counter is what found them.** Both held
/// fz-kdt.179's and fz-kdt.183's cures; both now observe ZERO at every arrival
/// this table drove them at. Read off `interp --dump backend=`, the cause is
/// the same for both and it is fz-kdt.199: `00277` publishes five construction
/// wrappers and `enum_predicate_search` publishes 32, and EVERY one
/// of them is single-member with no selection plan, so
/// `select_construction_member` takes its `None if members.len() == 1` branch
/// and no dispatch runs. The cures are real and their fixtures no longer build
/// the shape that shows them.
///
/// WHERE THE SEVEN BLIND ROWS WENT. `00277`'s three wrapper orders and its
/// `arms:6` moved to `behavior/enum_take_drop_split`, which still builds what
/// they were written to watch: 23 of its 38 wrappers are multi-member WITH a
/// selection plan, so a permuted wrapper or arm order really does reseat the
/// members a value is routed among, and it observes 375 at each of those four
/// arrivals. `enum_predicate_search`'s `arms:6` moved to `00419_enum_take_mixed`
/// -- fz-kdt.183's cure was about two list arms whose ELEMENTS differ, and that
/// is `enum_take_mixed`'s subject; all four of its wrappers are two-member with
/// a selection plan, and it observes 36 under `arms:6`. The two SETTLED rows
/// were DELETED rather than re-homed, because the settled arrival is already
/// held by the six settled rows above them and a re-homing would have been a
/// duplicate row, not a kept property.
///
/// WHAT THE OLD `00277` ROWS RECORDED, kept here because the table no longer
/// can. Its construction wrapper's member-selection plan for
/// `Enum.reverse(1..7//2, [:tail])`'s reducer used to seat `list(int)` ahead of
/// `list(int | :tail)`, so the accumulator `[1, :tail]` and its growth passed
/// `list(int)`'s head test and ran the body compiled for `[integer]` -- 12
/// escapes at the settled arrival, 12 under `arms:6` and `arms:reverse`, 0
/// under every wrapper order. stdout was right on every door because the
/// accumulator lane is `ValueRef` in both bodies (boxed element access, the
/// fz-kdt.131 correlation nobody proved), so the escape was latent. Member
/// selection now runs through `routable_alternatives` (fz-kdt.179): the
/// covering member stands in for `list(int)`, the drop takes it, and every
/// arrival read 0 -- until fz-kdt.199 left the fixture with nothing to select
/// among at all.
///
/// WHAT THE OLD `enum_predicate_search` ROWS RECORDED. The `arms:6` row was
/// fz-kdt.131's facet-3 pair -- two list arms whose heads overlap and neither
/// of whose surfaces contains the other -- measured on the production path for
/// the first time, and fz-kdt.183 cured it 1 -> 0. The pair existed because one
/// `List.reduce_while_step/3` key stood for two callers whose list elements
/// differ; with the element in the key the two arms are two keys and neither is
/// blind to the other's values. fz-kdt.131 has no reproducer in this tree and
/// must decide one -- the facet-3 shape is still constructible, this fixture
/// just no longer builds it.
///
/// A RATCHET, not a blessing. Every row reads 0 escapes now, each holding a
/// fixture and arrival that once escaped or could regress; a count this table
/// does not carry -- in either direction, and in either column -- is either a
/// new latent miscompile, a cure, or a fixture that stopped exercising the
/// property, and all three want the table edited deliberately rather than a
/// number re-blessed.
///
/// fz-kdt.120: `enum_take_drop_split` reads 375 -> 373 OBSERVATIONS at all six
/// of its arrivals, escapes flat at 0. The denominator moved because the plan
/// shape did. With the fz-f98.16 empty-list veto gone,
/// `List.reduce_while_step/3` keys on the accumulator the fold really carries,
/// `{:cont | :halt, []} | {:cont, [int]}`, where the veto had erased the seed
/// rung; the body's two rungs must then be told apart, so the artifact grows an
/// entry clause dispatch asking `tuple_arity(2)` and `equal(:cont)`/
/// `equal(:halt)`. Measured on the `--dump backend=` canon: +2 dispatch plans,
/// `tuple_arity` questions 21 -> 28, `equal` +2, `Region::Type` questions FLAT
/// at 62, executables flat at 237, and interp and run stdout byte-identical.
/// Two evaluations that used to reach a matched `Region::Type` question are
/// settled by that clause dispatch instead, which is the denominator changing
/// under the row and not the escape count moving. fz-tfn.26 then coalesces
/// fifteen content-caused analyses on this combined stack; eleven of those runs had
/// reached a matched `Region::Type` question, so each affected row's
/// observation denominator falls 373 -> 362 while escapes stay at zero.
const SURFACE_MEMBERSHIP_CENSUS: [(&str, &str, usize, usize); 13] = [
    ("fixtures2/00183_enum_take_list_range.fz", "", 36, 0),
    ("fixtures2/00230_enum_take_chained.fz", "", 36, 0),
    ("fixtures2/00418_enum_count_range.fz", "", 6, 0),
    ("fixtures2/00419_enum_take_mixed.fz", "", 36, 0),
    ("fixtures2/00420_enum_take_drop_split.fz", "", 362, 0),
    ("fixtures2/behavior/enum_take_drop_split.fz", "", 362, 0),
    ("fixtures2/behavior/unused_range_binding.fz", "", 6, 0),
    // fz-kdt.187: the four permuted arrivals `00277_enum_tier0_fixture` used to
    // hold, re-homed onto the fixture that still selects among members.
    ("fixtures2/behavior/enum_take_drop_split.fz", "arms:6", 362, 0),
    ("fixtures2/behavior/enum_take_drop_split.fz", "wrappers:1", 362, 0),
    ("fixtures2/behavior/enum_take_drop_split.fz", "wrappers:6", 362, 0),
    ("fixtures2/behavior/enum_take_drop_split.fz", "wrappers:reverse", 362, 0),
    // fz-kdt.187: `enum_predicate_search`'s `arms:6` row, re-homed onto the
    // fixture whose list arms still differ at the element.
    ("fixtures2/00419_enum_take_mixed.fz", "arms:6", 36, 0),
    // The fixture written for fz-kdt.131's facet-3 pair reads 0: its header
    // says why (the fold hands the TAIL to the recursive dispatch, so the
    // mixed list never reaches the `[:false | :true]` arm), and this row is
    // what holds that sentence to the tree.
    ("fixtures2/behavior/dispatch_list_head_separates.fz", "", 4, 0),
];

/// fz-kdt.141 / fz-kdt.136: the wrapper half of the stress has teeth.
///
/// A gate that asserts invariance is worth exactly what its perturbation
/// reaches, and the instrument this replaces reached the construction wrappers
/// not at all. So assert the perturbation lands: the same fixture, compiled to
/// the same stage, renders a DIFFERENT canonical backend program under a
/// permuted wrapper order -- and an identical one under no setting, which is
/// the inertness claim on the same comparand.
///
/// `enum_take_drop_split` is the subject because its wrappers carry members
/// keyed on accumulator tuples that differ only at a list position -- pairs
/// the tuple test COULD not separate before fz-kdt.138 (whichever the mint
/// order put first took every value) and now separates by shape and head.
/// Which member the mint order lists first is what this perturbation moves.
/// On this fixture that choice is no longer a hazard -- fz-kdt.132 minted the
/// covering rung every one of its members needed, and the tripwire reads 0 here
/// at every setting -- but it is still a choice nothing but the interner makes,
/// which is what this gate holds to one answer. Where a wrapper's members are
/// NOT all covering, the mint order used to decide a routing (00277 read 12
/// surface-membership escapes at the settled order before fz-kdt.179); member
/// selection runs the drop and the covering seat now, so that no longer depends
/// on the interner, and `compiler2_no_value_reaches_a_construction_member_that_never_named_it`
/// holds it at 0 under every setting.
#[test]
fn compiler2_a_permuted_wrapper_order_reseats_the_construction_members() {
    use crate::compiler2::callsite_dispatch::dispatch_stress::{DispatchStressed, setting};

    let fixture = "fixtures2/behavior/enum_take_drop_split.fz";
    let settled = backend_canon(fixture);
    assert_eq!(
        backend_canon(fixture),
        settled,
        "the same fixture compiled twice with no setting must render the same artifact, or this \
         gate's comparand is noise",
    );
    let permuted = {
        let _stress = DispatchStressed::install(setting("wrappers:1"));
        backend_canon(fixture)
    };
    assert_ne!(
        permuted, settled,
        "a permuted wrapper order must reseat the construction members it was built to perturb; \
         a stress that cannot move them proves nothing about the order they arrived in",
    );
}

/// fz-kdt.193: the number a selection site's LABEL prints is the number the
/// dump heads that wrapper's block with.
///
/// A wrapper has two numbers. Its `identity` is its position in
/// `construction_wrappers`, and it is what the interpreter prints when a member
/// selection goes wrong (`select_construction_member`'s three error messages).
/// Its CANONICAL number is where `ProgramCanon::wrapper_order` sorts it, and it
/// is what `--dump backend=` prints. They agree only by accident: on
/// `00419_enum_take_mixed` the map is `0->2, 1->3, 2->0, 3->1` and no wrapper
/// is a fixed point at all, so a label that printed the identity sent a reader
/// following a failure message into the dump to the WRONG BLOCK, every time.
///
/// The cure is one authority, not a second opinion:
/// [`PlanSite::Selection`] carries the number
/// [`canonical_wrapper_numbers`](crate::compiler2::canon::canonical_wrapper_numbers)
/// computes, which is `wrapper_order` read the other way round -- the same
/// order the dump prints in. It prints BOTH numbers, because both have a
/// reader: the canonical one leads to the dump, and the published one is what
/// a runtime error and a debugger show.
///
/// AND THE PERTURBATION LANDS, which is what stops this being a tautology: the
/// last assertion is that no selection site on this fixture has its two numbers
/// agree, so the old label named the wrong block at every one of the four and
/// this gate is exactly as red at base as the defect it holds.
///
/// `enum_map_family` was the ticket's subject and cannot be: fz-kdt.199 left
/// all twelve of its wrappers single-member with no selection plan, so it
/// carries no `PlanSite::Selection` at all now. `00419_enum_take_mixed` does --
/// four wrappers, four two-member selections -- and its map has no fixed point
/// either.
#[test]
fn compiler2_a_selection_sites_label_names_the_wrapper_the_dump_prints() {
    let fixture = "fixtures2/00419_enum_take_mixed.fz";
    let (compiler, program) = driven_backend_program(fixture);
    let world = compiler.world();

    // The reader's destination. Canon prints one block per wrapper, in
    // canonical order, so the Nth block is headed `wrapper wN` -- and that is
    // the only thing a number in a label can mean to whoever follows it here.
    let dump = crate::compiler2::canon::canon_backend_program(world, &program);
    let heads = dump
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("wrapper w"))
        .collect::<Vec<_>>();
    assert_eq!(
        heads,
        (0..program.construction_wrappers().len())
            .map(|canonical| format!("wrapper w{canonical}"))
            .collect::<Vec<_>>(),
        "the dump heads one block per wrapper in canonical order; if it stopped doing that, a label \
         could not name a block at all",
    );

    let canonical_of = crate::compiler2::canon::canonical_wrapper_numbers(world, &program);
    let mut checked = 0;
    let mut both_numbers_differ = 0;
    for entry in artifact_plans(world, &program) {
        let PlanSite::Selection { wrapper, .. } = entry.site else {
            continue;
        };
        let label = entry.site.to_string();
        let canonical = canonical_of[wrapper as usize];
        assert!(
            label.starts_with(&format!("wrapper w{canonical} ")),
            "a selection site's label must LEAD with the number the dump prints, because that is the \
             number a reader carries into `--dump backend=`: {label}",
        );
        assert_eq!(
            heads[canonical],
            format!("wrapper w{canonical}"),
            "the block {label} sends a reader to must be the one the dump heads with that number",
        );
        assert!(
            label.contains(&format!("(published w{wrapper})")),
            "the published identity is what a runtime error and a debugger show, so the label keeps it \
             too rather than trading one wrong number for another: {label}",
        );
        checked += 1;
        both_numbers_differ += usize::from(canonical != wrapper as usize);
    }
    assert_eq!(
        checked, 4,
        "{fixture} is the subject because it still publishes four wrapper member selections; a fixture \
         with none proves nothing here",
    );
    assert_eq!(
        both_numbers_differ, checked,
        "the two numberings must actually disagree on every site, or this gate would pass on a label \
         that printed the published identity and would not be red at the defect it holds",
    );
}

/// fz-kdt.194: on the fixtures below, the ARTIFACT -- and not only the answer
/// -- is the same whichever order the fixpoint delivered a callsite's targets
/// in.
///
/// `compiler2_dispatch_answers_the_same_under_a_permuted_arm_order` holds the
/// BEHAVIOUR invariant, and it was green long before this: the residues arrival
/// order decided were meaning-free or the corpus never reached them. What moved
/// was the ARTIFACT -- arm order, and every plan node and body numbering
/// downstream of it. Measured at fz-kdt.184's landing (`ca23b676f`), sweeping
/// all 604 fixtures through `interp --dump backend=`: the settled canon differs
/// from the `arms:N` canon on the 22 fixtures below, at every one of seeds 1-6
/// and on the identical fixture set at each, and on none of the other 453 that
/// render one.
///
/// Every one of those 22 moved on a SEPARATED pair -- two arms no value can
/// reach both of, whose order therefore said nothing.
/// `specificity_order`'s canonical repair settles them from any arrival, and
/// the population reads 0 at every seed.
///
/// WHAT THIS DOES NOT CLAIM. The arm axis is not closed in general. The repair
/// settles a run only where the run is pairwise separated end to end, and a
/// `Covering` or `Escaping` pair anywhere in it stops there
/// (`a_covering_pair_blocks_the_repair_and_leaves_the_arrival_showing` and
/// `a_separated_run_a_meaning_bearing_pair_blocks_is_not_sorted_through` are
/// the two shapes). What is measured is this corpus at this head: the
/// population that moved is 0, and this gate is the ratchet on it.
///
/// A RATCHET ON THE WHOLE MEASURED POPULATION, not a sample: a fixture that
/// starts moving again is an ordering axis that has re-opened, and it must be
/// diagnosed rather than removed from this list.
///
/// WHAT IT COSTS, AND WHAT THAT BOUGHT. 22 fixtures x 3 compiles -- one
/// settled and one per seed -- is the whole of the gate, and compiling
/// fixtures is the most expensive thing this suite does. Measured back to back
/// in a debug build on one machine: **36.9 s** at the two seeds it drives,
/// against **61.6 s** at the four settings the prototype swept
/// (`arms:reverse` plus seeds 1, 3 and 6). At four it joined
/// `compiler2_dispatch_answers_the_same_under_a_permuted_arm_order`,
/// `..._wrapper_order` and
/// `compiler2_dispatch_blind_escape_census_is_the_known_population` above the
/// harness's 60-second banner; at two it runs below them.
///
/// The 25 s came off readings measured to carry no signal, and measured BY
/// INJECTION rather than argued: with the repair call deleted, this gate
/// reports **66** findings under the prototype's four settings and every one
/// of them is a seed -- `arms:reverse` contributes ZERO (a group mirror is the
/// identity on singleton groups, and every group on this corpus is one), and
/// seeds 1, 3 and 6 each name the SAME 22 fixtures. So the reversal bought 22
/// compiles of nothing and the third seed bought a duplicate. Under the two
/// seeds kept, the same injection reports **44**, so the gate is still exactly
/// as red at base as the population it ratchets.
///
/// The SECOND seed is kept for the reason `WRAPPER_MEMBER_STRESSES` keeps its
/// second: a seeded permutation of a two-element arrival is the identity for
/// half the seeds, so one seed can be blind on a callsite this corpus does not
/// have yet. `arms:reverse` is still exercised by `ARM_ORDER_STRESSES`, which
/// drives the cheap in-process ANSWER gates, and
/// `.agent/docs/dispatch-matrix.md` carries the recipe for the full six-seed
/// corpus sweep, which is where a wider question gets asked.
#[test]
fn compiler2_a_permuted_arm_order_renders_the_same_artifact() {
    let mut moved = Vec::new();
    for fixture in ARM_ORDER_ARTIFACT_CENSUS {
        let settled = backend_canon(fixture);
        for stress in ARM_ORDER_ARTIFACT_STRESSES {
            let permuted = {
                let _stress = crate::compiler2::callsite_dispatch::dispatch_stress::DispatchStressed::install(
                    crate::compiler2::callsite_dispatch::dispatch_stress::setting(stress),
                );
                backend_canon(fixture)
            };
            if permuted != settled {
                moved.push(format!("{fixture} under {stress}"));
            }
        }
    }
    assert!(
        moved.is_empty(),
        "a permuted arrival is an order the fixpoint could legally have delivered, so an artifact \
         that differs under one is an artifact the schedule wrote: {}",
        moved.join("; "),
    );
}

/// The fixtures whose backend canon moved under a seeded arm permutation at
/// `ca23b676f`, measured over the whole corpus. Each one carried at least one
/// separated pair the seat left in arrival order.
const ARM_ORDER_ARTIFACT_CENSUS: [&str; 22] = [
    "fixtures2/00231_joined_fn_refs_enum_reduce.fz",
    "fixtures2/00274_closed_union_protocol.fz",
    "fixtures2/00281_opaque_reducer_closure.fz",
    "fixtures2/00384_closure_predicate_wrapper.fz",
    "fixtures2/00420_enum_take_drop_split.fz",
    "fixtures2/00426_closed_union_protocol_dispatch.fz",
    "fixtures2/00428_open_union_protocol.fz",
    "fixtures2/behavior/brand_refines_its_inner.fz",
    "fixtures2/behavior/bsx_guard_eq.fz",
    "fixtures2/behavior/bsx_nested_match.fz",
    "fixtures2/behavior/closure_identity_captures.fz",
    "fixtures2/behavior/closure_identity_tag_split.fz",
    "fixtures2/behavior/enum_map_family.fz",
    "fixtures2/behavior/enum_reduce_halt_arm_order.fz",
    "fixtures2/behavior/enum_take_drop_split.fz",
    "fixtures2/behavior/enumerable_protocol_dispatch.fz",
    "fixtures2/behavior/opaque_fn_mixed_return.fz",
    "fixtures2/behavior/opaque_fn_value_join.fz",
    "fixtures2/behavior/pipe_headless_case.fz",
    "fixtures2/behavior/range_enumerable.fz",
    "fixtures2/behavior/repr_seam_closure_predicate.fz",
    "fixtures2/behavior/same_lambda_two_capture_types_dynamic.fz",
];

/// The arrival settings the artifact ratchet drives: the two SEEDS
/// [`ARM_ORDER_STRESSES`] names, and not its `arms:reverse`. All six seeds
/// moved the identical 22 fixtures at base and the reversal moved none, so a
/// third seed is a duplicate reading and the reversal is an empty one -- the
/// gate's doc has the injection numbers that say so. The corpus recipe in
/// `.agent/docs/dispatch-matrix.md` drives all six seeds and the reversal.
const ARM_ORDER_ARTIFACT_STRESSES: [&str; 2] = ["arms:1", "arms:6"];

/// One fixture's canonical `BackendProgram` -- the comparand the `--dump
/// backend` path renders.
fn backend_canon(fixture: &str) -> String {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some(fixture.to_string()),
        text: std::fs::read_to_string(fixture).unwrap_or_else(|error| panic!("read {fixture}: {error}")),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, crate::compiler2::dump::DumpStage::Backend)
        .unwrap_or_else(|error| panic!("{fixture} should reach a backend program: {error}"));
    let world = compiler.world();
    crate::compiler2::canon::canon_backend_program(world, &compiler.retained_backend_program(root))
}

#[test]
fn runtime_demand_facts_converge_across_independent_self_and_mutual_schedule_orders() {
    const FUNCTIONS: [(&str, &str); 5] = [
        ("left.fz", "fn left(x), do: fn(y) -> x + y end\n"),
        ("right.fz", "fn right(x), do: fn(y) -> x * y end\n"),
        (
            "count.fz",
            "fn count(0), do: fn(x) -> x end\nfn count(n), do: count(n - 1)\n",
        ),
        (
            "even.fz",
            "fn even(0), do: fn(x) -> x end\nfn even(n), do: odd(n - 1)\n",
        ),
        (
            "odd.fz",
            "fn odd(0), do: fn(x) -> x + 1 end\nfn odd(n), do: even(n - 1)\n",
        ),
    ];
    fn settle(order: usize) -> (String, Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
        let tel = ConfiguredTelemetry::new();
        let runs = Rc::new(RefCell::new(Vec::<(ExecutableKey, String)>::new()));
        let run_sink = Rc::clone(&runs);
        tel.attach_raw_event2::<World, super::JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, world, completion| {
                if let Job::DeriveRuntimeDemand(executable) = &completion.job {
                    let name = world.function_ref(executable.activation.function).name.clone();
                    if ["left", "right", "count", "even", "odd", "main"].contains(&name.as_str()) {
                        run_sink.borrow_mut().push((executable.clone(), name));
                    }
                }
            },
        );
        let mut compiler = Compiler2::new(tel);
        let dbg = DbgCapture::new();
        compiler.set_output(dbg.sink());
        let mut source = String::new();
        for (_, text) in &FUNCTIONS {
            source.push_str(text);
        }
        source.push_str("fn main(), do: dbg({left(1).(3), right(2).(4), count(3).(1), even(4).(1)})\n");
        compiler.submit_code(CodeSubmission {
            name: Some("runtime_demand_order.fz".to_string()),
            text: source,
        });
        let root_specs = [("left", 1), ("right", 1), ("count", 1), ("even", 1), ("main", 0)];
        let swapped_root_specs = [("right", 1), ("left", 1), ("count", 1), ("even", 1), ("main", 0)];
        let rotated_root_specs = [("count", 1), ("even", 1), ("right", 1), ("left", 1), ("main", 0)];
        let ordered_roots = match order {
            0 => &root_specs,
            1 => &swapped_root_specs,
            2 => &rotated_root_specs,
            _ => panic!("unknown root order"),
        };
        let mut main_root = None;
        for (name, arity) in ordered_roots {
            let root = compiler.submit_root(RootSubmission {
                module_name: None,
                name: (*name).to_string(),
                arity: *arity,
                need: ExecutableNeed::Value,
            });
            if *name == "main" {
                main_root = Some(root);
            }
        }
        let root = main_root.expect("main root");
        compiler
            .run_root_interp(root)
            .expect("the reactive demand graph should settle and run");
        let world = compiler.world();
        let runs = runs.borrow();
        let mut construction_owners = HashSet::new();
        for (executable, _) in runs.iter() {
            assert!(
                world.fact_is_settled(&FactKey::RuntimeDemand(executable.clone())),
                "every observed RuntimeDemand formula must finish settled",
            );
            let job = Job::DeriveRuntimeDemand(executable.clone());
            let reads = world.job_reads(&job);
            assert!(
                reads.contains(&FactUse::current(FactKey::RuntimeDemandInput(executable.clone()))),
                "each formula must read only its exact caller contribution cell",
            );
            let facts = world
                .executable_facts(executable)
                .expect("an observed RuntimeDemand formula must retain its executable facts");
            let mut expected_peers = HashSet::new();
            for (callsite, summary) in facts.callsites() {
                let need = facts
                    .callsite_needs()
                    .get(callsite)
                    .copied()
                    .unwrap_or(ExecutableNeed::Value);
                expected_peers.extend(
                    summary
                        .targets
                        .iter()
                        .filter_map(|target| target.runtime_executable(need)),
                );
            }
            expected_peers.extend(
                world
                    .runtime_demand(executable)
                    .expect("an observed RuntimeDemand formula must retain its answer")
                    .callable_flows
                    .values()
                    .flat_map(|flow| flow.resolutions.iter().cloned()),
            );
            let actual_peers = reads
                .iter()
                .filter_map(|read| match read {
                    FactUse::Current(FactKey::RuntimeDemandInputs(peer)) => Some(peer.clone()),
                    _ => None,
                })
                .collect::<HashSet<_>>();
            if reads.iter().any(|read| {
                matches!(
                    read,
                    FactUse::Current(FactKey::CallableConstructionTarget(key)) if key.owner == *executable
                )
            }) {
                construction_owners.insert(world.function_ref(executable.activation.function).name.clone());
            }
            assert_eq!(
                actual_peers, expected_peers,
                "each formula must subscribe to exactly its direct and callable-flow targets",
            );
        }
        assert!(
            ["even", "odd"].iter().all(|name| construction_owners.contains(*name)),
            "the mutually recursive closure producers must bootstrap through exact construction targets: {construction_owners:?}",
        );
        let order = runs.iter().map(|(_, name)| name.clone()).collect();
        let mut work = runs
            .iter()
            .map(|(executable, _)| crate::compiler2::canon::canon_executable_key(world, executable))
            .collect::<Vec<_>>();
        work.sort();
        let mut facts = world
            .runtime_demand_facts()
            .map(|(executable, demand)| crate::compiler2::canon::canon_runtime_demand_fact(world, executable, demand))
            .collect::<Vec<_>>();
        facts.sort();
        (
            crate::compiler2::canon::canon_backend_program(world, &compiler.retained_backend_program(root)),
            dbg.lines(),
            order,
            work,
            facts,
        )
    }

    let baseline = settle(0);
    let alternatives = [settle(1), settle(2)];
    assert_eq!(
        baseline.1,
        vec!["{4, 8, 1, 1}"],
        "the settled artifact must execute correctly"
    );
    for alternative in alternatives {
        assert_ne!(
            baseline.2, alternative.2,
            "each registration order must perturb reactive arrival"
        );
        assert_eq!(
            baseline.0, alternative.0,
            "arrival order must not move the canonical backend"
        );
        assert_eq!(baseline.1, alternative.1, "arrival order must not move runtime output");
        assert_eq!(
            baseline.3, alternative.3,
            "arrival order must not move the exact executable RuntimeDemand work multiset",
        );
        assert_eq!(
            baseline.4, alternative.4,
            "arrival order must not move any settled RuntimeDemand semantic fact",
        );
    }
}

#[test]
fn runtime_demand_discovers_nested_local_callable_dependencies_to_closure() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("nested_runtime_demand_dependencies.fz".to_string()),
        text: "fn main() do\n  inner = fn (x) -> x + 1 end\n  outer = fn (x) -> inner.(x) end\n  outer.(1)\nend\n"
            .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(2));

    let main = compiler
        .retained_backend_program(root)
        .executables()
        .iter()
        .find(|executable| compiler.world().function_ref(executable.key.activation.function).name == "main")
        .expect("the main executable should reach the backend")
        .key
        .clone();
    let callable_dependencies = compiler
        .world()
        .job_reads(&Job::DeriveRuntimeDemand(main))
        .into_iter()
        .filter_map(|read| match read {
            FactUse::Current(FactKey::RuntimeDemandInputs(key)) => Some(key.activation.function),
            _ => None,
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_dependencies.len(),
        2,
        "loading the outer lambda row must reveal and subscribe to its captured inner lambda",
    );
    assert!(
        callable_dependencies
            .iter()
            .all(|function| { compiler.world().function_ref(*function).name.starts_with("#lambda:") })
    );
}

#[test]
fn boxed_callable_members_contribute_their_exact_return_contract() {
    use crate::compiler2::RuntimeDemand;
    use crate::compiler2::jobs::runtime_demand::RuntimeDemandFormulaCapture;

    let capture = RuntimeDemandFormulaCapture::install();
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    backend.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("boxed_partial_return_contribution.fz".to_string()),
        text: r#"
fn make_pair(), do: fn (x) -> {:unused, x} end
fn observe(pair, x) do
  wrapped = {:wrapped, pair.(x)}
  {_, {_, value}} = wrapped
  {pair, value}
end
fn main() do
  pair = make_pair()
  observe(pair, 1)
end
"#
        .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, crate::compiler2::dump::DumpStage::Backend)
        .expect("the boxed structured-return fixture should reach a backend program");

    let program = backend.last(root).program;
    let evaluations = capture.evaluations();
    let partial = RuntimeDemand::tuple_fields(vec![RuntimeDemand::ignore(), RuntimeDemand::whole()]);
    let retained = RuntimeDemand::whole();
    let mut candidates = Vec::new();
    for owner in &evaluations {
        for target in owner
            .demand
            .callable_flows
            .values()
            .flat_map(|flow| &flow.first_class_edges)
            .map(|edge| &edge.resolution)
        {
            if target.need != ExecutableNeed::Value
                || owner
                    .contributions
                    .get(target)
                    .and_then(|contribution| contribution.return_demand.as_ref())
                    != Some(&retained)
            {
                continue;
            }
            for observer in &evaluations {
                if observer.member == owner.member {
                    continue;
                }
                let observations = observer
                    .observed_return_contributions
                    .iter()
                    .filter(|(observed_target, demand)| observed_target == target && demand == &partial)
                    .count();
                if observations == 1
                    && observer
                        .contributions
                        .get(target)
                        .and_then(|contribution| contribution.return_demand.as_ref())
                        == Some(&partial)
                {
                    candidates.push((owner, target, observer));
                }
            }
        }
    }
    assert_eq!(
        candidates.len(),
        1,
        "the fixture should have one typed target with distinct retained and partial publishers",
    );
    let (owner, target, observer) = candidates.pop().unwrap();
    assert_ne!(
        owner.member, observer.member,
        "the retained contract and partial observation need distinct owners"
    );
    assert_eq!(
        owner
            .contributions
            .get(target)
            .and_then(|contribution| contribution.return_demand.as_ref()),
        Some(&retained),
        "the construction owner must publish the target's exact Value contract",
    );
    assert_eq!(
        observer
            .observed_return_contributions
            .iter()
            .filter(|(observed_target, demand)| observed_target == target && demand == &partial)
            .count(),
        1,
        "the distinct observer must map its exact partial return demand to the same target key",
    );
    assert_eq!(
        observer
            .contributions
            .get(target)
            .and_then(|contribution| contribution.return_demand.as_ref()),
        Some(&partial),
        "the observer must publish only its own partial evidence",
    );
    let target_publishers = evaluations
        .iter()
        .filter(|evaluation| {
            evaluation
                .contributions
                .get(target)
                .and_then(|contribution| contribution.return_demand.as_ref())
                .is_some()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        target_publishers.len(),
        2,
        "only the construction owner and exact observer may publish the selected target",
    );
    assert!(
        target_publishers
            .iter()
            .all(|publisher| publisher.member == owner.member || publisher.member == observer.member),
        "an anchor or unrelated owner must not satisfy the selected target's joined demand",
    );

    let mut joined = partial;
    joined.join_assign(&retained);
    let target_index = program
        .executables()
        .iter()
        .position(|executable| &executable.key == target)
        .expect("the shared target should reach the backend program");
    let wrapper = program
        .construction_wrappers()
        .iter()
        .find(|wrapper| wrapper.members.iter().any(|member| &member.target == target))
        .expect("the shared target should remain behind its construction wrapper");
    let member = wrapper
        .members
        .iter()
        .find(|member| &member.target == target)
        .expect("the selected wrapper should contain the shared target");
    let executable = &program.executables()[target_index];
    assert_eq!(executable.abi.materialized.runtime_demand.return_demand, joined);
    assert_eq!(member.target_return, executable.abi.return_layout);
    assert_eq!(
        wrapper.return_form,
        BackendCallableReturn::ValueRef,
        "the joined structured return must materialize through the wrapper's public value carrier",
    );
}

#[test]
fn direct_only_callable_flow_does_not_contribute_a_retained_return_contract() {
    use crate::compiler2::RuntimeDemand;
    use crate::compiler2::jobs::runtime_demand::RuntimeDemandFormulaCapture;

    let capture = RuntimeDemandFormulaCapture::install();
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("direct_only_partial_return.fz".to_string()),
        text: r#"
fn pair(x), do: {:unused, x}
fn main() do
  wrapped = {:wrapped, pair(1)}
  {_, {_, value}} = wrapped
  value
end
"#
        .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, crate::compiler2::dump::DumpStage::Backend)
        .expect("the direct-only structured-return fixture should reach a backend program");

    let partial = RuntimeDemand::tuple_fields(vec![RuntimeDemand::ignore(), RuntimeDemand::whole()]);
    let evaluations = capture.evaluations();
    let mut candidates = evaluations
        .iter()
        .flat_map(|evaluation| {
            evaluation
                .observed_return_contributions
                .iter()
                .filter(|(_, demand)| demand == &partial)
                .map(move |(target, _)| (evaluation, target))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        candidates.len(),
        1,
        "the fixture should derive one exact direct-only partial-return target",
    );
    let (observer, target) = candidates.pop().unwrap();
    assert_eq!(
        observer
            .contributions
            .get(target)
            .and_then(|contribution| contribution.return_demand.as_ref()),
        Some(&partial),
        "without a first-class construction, the exact production contribution must remain partial",
    );
    assert!(
        evaluations.iter().all(|evaluation| {
            evaluation
                .demand
                .callable_flows
                .values()
                .flat_map(|flow| &flow.first_class_edges)
                .all(|edge| &edge.resolution != target)
        }),
        "the direct-only target must be absent from every first-class resolution",
    );
}

/// fz-kdt.47 / fz-kdt.179: callable construction has distinct authorities for
/// exact target production and semantic selection; RuntimeDemand never mutates
/// the interner.
/// `plan_callable_flows` orders first-class surfaces with the typed activation
/// relation and resolves each edge directly from the callable-flow plan.
/// `finish_callable_flows` exposes the finished edges at the wrapper stress
/// point. Finally `construction_member_selection` is the sole semantic member
/// authority: it drops and seats the finished edges, and transport builds both
/// the member list and selection rows from that one result.
///
/// `enum_take_drop_split` is the subject. `enum_map_family` was, and it stopped
/// carrying a multi-surface member list at all under fz-kdt.199: its wrapper's
/// members were one element family crossed with the empty and the grown
/// accumulator, and keying the returned accumulator gives each cross its own
/// activation, so every wrapper there is now single-member. The gate is aimed
/// at a fixture that still exercises the order rather than re-blessed to
/// nothing. The end-to-end formula-order and wrapper-stress gates prove the
/// dynamic result; this source assertion prevents the deleted mutating builder
/// from returning as a second construction path.
#[test]
fn compiler2_construction_target_precedes_seated_wrapper_selection() {
    let runtime_demand = include_str!("jobs/runtime_demand.rs");
    assert!(
        !runtime_demand.contains(concat!("callable_flow_resolution_edges_", "product")),
        "the deleted mutating edge builder must not return"
    );
    for authority in [
        "fn plan_callable_flows(",
        "ordered.sort_by(|a, b| types.cmp_activation_tys(&a.inputs, &b.inputs))",
        "let key = CallableConstructionTargetKey {",
        "construction_flow_edge(world, input, &key, producer, surface)",
        "fn finish_callable_flows(",
        "dispatch_stress::perturbed_construction_edges(plan.first_class_edges)",
    ] {
        assert!(
            runtime_demand.contains(authority),
            "runtime demand must retain the read-only callable-resolution step {authority}"
        );
    }
    let transport = include_str!("jobs/transport.rs");
    assert!(
        transport.contains("construction_member_selection(world.types_mut(), &flow.first_class_edges)"),
        "transport must derive the member list and selection plan from the seated edges"
    );

    let fixture = "fixtures2/behavior/enum_take_drop_split.fz";
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some(fixture.to_string()),
        text: std::fs::read_to_string(fixture).unwrap_or_else(|error| panic!("read {fixture}: {error}")),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, crate::compiler2::dump::DumpStage::Backend)
        .unwrap_or_else(|error| panic!("{fixture} should reach a backend program: {error}"));
    let program = compiler.retained_backend_program(root);

    let multi_member_wrappers = program
        .construction_wrappers()
        .iter()
        .filter(|wrapper| wrapper.members.len() > 1)
        .count();
    assert!(
        multi_member_wrappers > 0,
        "{fixture} must exercise at least one multi-surface construction wrapper for this gate to \
         mean anything",
    );
}

/// The answer to hold a permuted order to: the blessed golden where the
/// fixture matrix owns one, and otherwise this tree's own settled-order run.
fn settled_arm_order_answer(fixture: &str) -> Vec<String> {
    let golden = fixture.strip_suffix(".fz").map(|stem| format!("{stem}.expected.txt"));
    match golden.and_then(|path| std::fs::read_to_string(path).ok()) {
        Some(text) => text.lines().map(str::to_string).collect(),
        None => interpreted_answer(fixture),
    }
}

/// One fixture's `dbg` output, through the backend interpreter.
fn interpreted_answer(fixture: &str) -> Vec<String> {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some(fixture.to_string()),
        text: std::fs::read_to_string(fixture).unwrap_or_else(|error| panic!("read {fixture}: {error}")),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        panic!(
            "{fixture} should run on the backend interpreter: {error}; dbg={}",
            dbg.lines().join("\n")
        )
    });
    dbg.lines()
}

/// fz-kdt.125: a closure that reaches its invoker through one generalized hop
/// still runs, and it is the one the caller handed over.
///
/// `run/2` only FORWARDS its callable, so its arrow position generalizes and
/// one shared body serves both lambdas. `apply_twice/2` INVOKES it, so it
/// specializes on the closure literal -- two bodies, each direct-calling its
/// own lambda. `run/2`'s one callsite names both.
///
/// The two observable surfaces used to be identical, because
/// `runtime_type_test_envelope` erased both literals to `fun_top`:
/// `discriminating_inputs` found nothing to test, the plan compiled to an
/// unconditional outcome, arm 1 was emitted unreachable, and `n * 3` never ran
/// (12/12 for 12/90, on all three paths). The erasure was the defect. A closure
/// value's heap word names the code it was minted from, so the envelope keeps
/// literal fn ids and the plan asks which lambda arrived.
#[test]
fn compiler2_forwarded_closures_are_not_replaced_by_their_sibling() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/forwarded_closure_siblings.fz".to_string()),
        text: r#"
defmodule Pipeline do
  fn apply_twice(f, x), do: f.(f.(x))
  fn run(f, x), do: apply_twice(f, x)
end

fn main() do
  dbg(Pipeline.run(fn (n) -> n + 1 end, 10))
  dbg(Pipeline.run(fn (n) -> n * 3 end, 10))
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler
        .run_root_interp(root_id)
        .unwrap_or_else(|error| panic!("forwarded closures should run: {error}"));

    assert_eq!(
        dbg.lines().as_slice(),
        ["12", "90"],
        "each call must invoke the lambda it was handed, not the one the surviving specialization was keyed on",
    );
}

/// fz-kdt.118 / fz-kdt.141, the three-path half: `:halt` halts on the native
/// path too, under every legal order of this callsite's arms.
///
/// The interpreter carries a dynamic tag on every value, so it can survive
/// routing a value into a body that was not specialized for it. Native code
/// cannot, and this fixture's answer is a plan-level fact -- it must read the
/// same whichever way the arms arrived.
///
/// The corpus gates above drive the interpreter, because a mis-seated list
/// element aborts the process natively and an abort takes the whole suite with
/// it. This fixture is the one that can be held to the native door in process:
/// its arms differ by a closure literal the callable axis separates exactly, so
/// no order of them can route a value into a body that never named it -- and
/// the settings below are the ones the corpus sweep measured as leaving it
/// alone on every door.
#[test]
fn compiler2_jit_halts_a_reduce_under_every_arm_order() {
    for stress in ["", "arms:reverse", "arms:1", "arms:6"] {
        let tel = ConfiguredTelemetry::new();
        let dbg = DbgCapture::new();
        let mut compiler = Compiler2::new(tel);
        compiler.set_output(dbg.sink());
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures2/behavior/enum_reduce_halt_arm_order.fz".to_string()),
            text: include_str!("../../fixtures2/behavior/enum_reduce_halt_arm_order.fz").to_string(),
        });
        let root_id = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        let _stress = crate::compiler2::callsite_dispatch::dispatch_stress::DispatchStressed::install(
            crate::compiler2::callsite_dispatch::dispatch_stress::setting(stress),
        );
        compiler
            .run_root_jit(root_id)
            .unwrap_or_else(|error| panic!("the halt fixture should run on the JIT ({stress:?}): {error}"));
        assert_eq!(
            dbg.lines().as_slice(),
            ["{:halted, 3}", "{:done, 1500}"],
            "{stress:?}: `:halt` must halt whichever arm the plan lists first, \
             and the reducer the value carried is the one that must run",
        );
    }
}

#[test]
fn compiler2_membership_operator_protocol_receivers_settle_to_direct_impls() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &["fz", "diag", "error"]);
    let callsites = CallsiteCapture::new();
    callsites.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/membership_operator_compiler2.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/membership_operator.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);

    match compiler.drive() {
        DriveOutcome::Resolved => {}
        DriveOutcome::Fatal { job } => panic!(
            "membership operator protocol calls should resolve without backend-product failures: {job:?}; diag={:?}",
            capture
                .last(&["fz", "diag", "error"])
                .map(|event| metadata_str(&event, "message").to_string())
        ),
        other => panic!("membership operator protocol calls should resolve through backend lowering, got {other:?}"),
    }

    let program = backend.last(root_id).program;
    let summaries = callsites.all();
    let mut found = false;
    for executable in program.executables() {
        let crate::compiler2::BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries {
            let BackendTail::DirectCall { callsite, target, .. } = &entry.tail else {
                continue;
            };
            let CallEdge::Dispatch(dispatch) = target else {
                continue;
            };
            let Some(summary) = summaries
                .iter()
                .rev()
                .find(|record| record.key.activation == executable.key.activation && record.key.callsite == *callsite)
            else {
                continue;
            };
            assert!(
                dispatch.arms.len() > 1,
                "multi-target summary should lower as a multi-arm dispatch edge: {:?}",
                summary.summary,
            );
            found = true;
        }
    }
    assert!(
        !found,
        "membership_operator should now settle each protocol receiver to a direct impl instead of lowering a spurious dispatch edge",
    );
}

#[test]
fn compiler2_quicksort_root_closes_with_a_finite_recursive_frontier() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut world = crate::compiler2::World::new();
    let mut sessions = super::pull::ProductSessions::default();
    world.submit_code(
        Some("quicksort_plus_foo.fz".to_string()),
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_world_backend_product(&mut world, &tel, &mut sessions, root_id);
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "quicksort root should settle to a finite semantic frontier",
    );

    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);

    // The rooted, reachability-pruned activation frontier is derived by walking
    // the settled call graph from the entry (see
    // `rooted_reachable_frontier`). Reachability over the unique least fixpoint
    // is schedule-free, and each callsite resolves to its settled callee, so the
    // mid-convergence intermediates that a raw `activation_analysis` snapshot
    // would leak (e.g. an `append([], [a1_e])` key seeded before `qsort`'s
    // return widened) are never reached and never counted.
    let activations = rooted_reachable_frontier(&mut world, root_id, main_id);

    let entry_activation = ActivationKey::from_inputs(root_id, main_id, &[], world.types_mut());
    let types = world.types();
    assert!(
        activations.contains(&entry_activation),
        "root closure should keep the entry activation in the settled frontier"
    );
    let qsort_activations = activations
        .iter()
        .filter(|activation| activation.function == qsort_id)
        .collect::<Vec<_>>();
    assert_eq!(
        qsort_activations.len(),
        1,
        "root closure should collapse qsort/1 recursive list-family inputs to one activation key"
    );
    let mut partition_activations = activations
        .iter()
        .filter(|activation| activation.function == partition_id)
        .cloned()
        .collect::<Vec<_>>();
    partition_activations.sort_by_key(|activation| activation.inputs(types));
    // Both qsort activations call partition with the same canonical
    // (pivot, rest) — hd/tl of a non-empty and a general list coincide — so
    // ONE partition activation is the tight answer. The historical second
    // key was mid-oscillation garbage (absent evidence read as the empty
    // type) that lingered as dead demand; honest paths self-collect it.
    assert_eq!(
        partition_activations.len(),
        1,
        "root closure should settle on the single live partition/4 activation"
    );
    assert!(
        partition_activations
            .iter()
            .all(|activation| activation.input_len(types) == 4),
        "partition/4 should stay keyed on its four inputs"
    );
    let partition_inputs = partition_activations[0].inputs(types);
    // fz-f98.14.10.2: the two recursive accumulator slots collapse to their
    // ADDRESSED convergence class — `[a2_e]` and `[a3_e]` — list-family slots
    // whose element is a resolvable structural-address var, not the path-blind
    // `list(any)`. They are distinct BY ADDRESS (param 2 vs param 3), which is
    // correct: distinct parameter positions must not conflate. The win is that
    // each slot folds to ONE key (no `[int] | []` over-spec survives).
    assert_eq!(types.display(&partition_inputs[2]), "[a2_e]");
    assert_eq!(types.display(&partition_inputs[3]), "[a3_e]");
    let append_activations = activations
        .iter()
        .filter(|activation| activation.function == append_id)
        .collect::<Vec<_>>();
    assert_eq!(
        append_activations.len(),
        1,
        "root closure should collapse append/2 recursive list-family inputs to one activation key"
    );
    assert!(
        append_activations
            .iter()
            .all(|activation| activation.input_len(types) == 2),
        "append/2 should stay keyed on its two inputs"
    );
    assert!(
        activations.len() <= 17,
        "quicksort should settle within its bounded rooted activation frontier (main + the collapsed \
         qsort/partition/append keys + reached runtime helpers): {activations:?}"
    );
    assert!(
        !activations.iter().any(|activation| activation.function == foo_id),
        "quicksort root should not activate the uncalled foo/0"
    );
}

/// Derives the rooted, reachability-pruned activation frontier by starting at
/// the root's entry activation and following the settled call graph. Each activation's
/// `callsites`, resolved through `callsite_targets`, name the callee activations
/// it actually reaches. Callers: the redefinition tests below, plus the
/// single-drive frontier test and the every-schedule convergence test.
///
/// A raw `activation_analysis.defined` snapshot is NOT enough on its own here:
/// that store is a monotone GLOBAL cache that never retracts an activation once
/// analyzed, so a root that STOPS reaching a function keeps its stale facts
/// there (and the backend product is not rebuilt on redefinition either). Walking
/// the entry's live call graph prunes back to the currently reachable set across
/// redefinitions.
fn rooted_reachable_frontier(
    world: &mut crate::compiler2::World,
    root: crate::compiler2::RootId,
    entry_function: FunctionId,
) -> HashSet<ActivationKey> {
    let entry = ActivationKey::from_inputs(root, entry_function, &[], world.types_mut());
    let mut seen = HashSet::new();
    let mut stack = vec![entry];
    while let Some(key) = stack.pop() {
        if !seen.insert(key.clone()) {
            continue;
        }
        let Some(analysis) = world.activation_analysis(&key) else {
            continue;
        };
        let callsites = analysis.callsites.clone();
        for callsite in callsites {
            let callsite_key = CallSiteKey {
                activation: key.clone(),
                callsite,
            };
            if let Some(targets) = world.callsite_targets(&callsite_key) {
                for callee in targets.targets.iter().filter_map(|edge| edge.activation.clone()) {
                    stack.push(callee);
                }
            }
        }
    }
    seen
}

#[test]
fn compiler2_redefining_uncalled_foo_does_not_reopen_quicksort_root() {
    // After a quicksort root settles, redefining the UNCALLED `foo/0` must not
    // perturb the rooted settled activation frontier: `foo` is never reached, so
    // swapping its body has no bearing on which activations the root closes over.
    // The rooted reachable frontier directly proves incremental stability under
    // an irrelevant redefinition.
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut world = crate::compiler2::World::new();
    let mut sessions = super::pull::ProductSessions::default();
    world.submit_code(
        Some("quicksort_plus_foo_v1.fz".to_string()),
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_world_backend_product(&mut world, &tel, &mut sessions, root_id);
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "initial quicksort root should settle",
    );

    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let foo_id = function_id(&functions, "foo", 0);
    let frontier_before = rooted_reachable_frontier(&mut world, root_id, main_id);
    let functions_before = frontier_before
        .iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    assert!(
        functions_before.contains(&qsort_id) && !functions_before.contains(&foo_id),
        "the initial quicksort frontier should reach qsort and never the uncalled foo/0"
    );
    let executable_facts_before = frontier_before
        .iter()
        .cloned()
        .map(|activation| ExecutableKey {
            activation,
            need: ExecutableNeed::Value,
        })
        .collect::<Vec<_>>();
    let mut demanded_missing_fact = false;
    for executable in &executable_facts_before {
        let fact = FactKey::ExecutableFacts(executable.clone());
        if world.fact_revision(&fact).is_none() {
            demanded_missing_fact |= world.demand(Job::DeriveExecutableFacts(executable.clone()));
        }
    }
    if demanded_missing_fact {
        assert_resolved(
            super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
            "the rooted executable-fact frontier should settle before the unrelated edit",
        );
    }
    let executable_fact_revisions = executable_facts_before
        .iter()
        .map(|executable| {
            (
                executable.clone(),
                world
                    .fact_revision(&FactKey::ExecutableFacts(executable.clone()))
                    .expect("the demanded rooted executable fact should be present"),
            )
        })
        .collect::<HashMap<_, _>>();

    world.submit_code(
        Some("quicksort_plus_foo_v2.fz".to_string()),
        include_str!("../../fixtures2/00027_foo_99.fz").to_string(),
    );
    drive_world_backend_product(&mut world, &tel, &mut sessions, root_id);
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "redefining uncalled foo/0 should not reopen the quicksort root",
    );

    let frontier_after = rooted_reachable_frontier(&mut world, root_id, main_id);
    assert_eq!(
        frontier_after, frontier_before,
        "uncalled foo/0 redefinition should leave the rooted reachable activation frontier unchanged"
    );
    for (executable, revision) in executable_fact_revisions {
        assert_eq!(
            world.fact_revision(&FactKey::ExecutableFacts(executable)),
            Some(revision),
            "an uncalled function redefinition must not move any demanded executable fact in the selected root",
        );
    }
}

#[test]
fn compiler2_redefining_main_retracts_the_old_root_frontier_and_activates_foo() {
    // Redefining `main/0` so it drops qsort and instead calls foo/0 must RETRACT
    // the old recursive frontier: the rooted reachable frontier must become
    // exactly {main, foo} and no longer reach qsort/partition/append.
    //
    // Observe the root's reached activation frontier after replacing main's
    // body, independently of retained definitions for the former callees.
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut world = crate::compiler2::World::new();
    let mut sessions = super::pull::ProductSessions::default();
    world.submit_code(
        Some("quicksort_plus_foo_v1.fz".to_string()),
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_world_backend_product(&mut world, &tel, &mut sessions, root_id);
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "initial quicksort root should settle",
    );

    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);

    // Before: the entry reaches the full recursive quicksort frontier.
    let functions_before = rooted_reachable_frontier(&mut world, root_id, main_id)
        .iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    assert!(
        functions_before.contains(&qsort_id)
            && functions_before.contains(&partition_id)
            && functions_before.contains(&append_id),
        "the initial quicksort frontier should reach the recursive qsort/partition/append closure"
    );

    world.submit_code(
        Some("quicksort_plus_foo_v2.fz".to_string()),
        include_str!("../../fixtures2/00008_callsite_fact_surface.fz").to_string(),
    );
    drive_world_backend_product(&mut world, &tel, &mut sessions, root_id);
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "redefining main/0 should retract the old quicksort root frontier",
    );

    let functions_after = rooted_reachable_frontier(&mut world, root_id, main_id)
        .iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        functions_after,
        HashSet::from([main_id, foo_id]),
        "redefining main/0 should leave only main/0 and foo/0 in the rooted reachable frontier"
    );
    assert!(
        !functions_after.contains(&qsort_id)
            && !functions_after.contains(&partition_id)
            && !functions_after.contains(&append_id),
        "redefining main/0 should retract the old quicksort recursive frontier"
    );
}

#[test]
fn compiler2_submit_root_before_code_reports_unresolved_until_entry_is_defined() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let work_graph = WorkGraphCapture::new();
    work_graph.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let function_id = compiler.root_function(root_id);

    let outcome = compiler.drive();
    match outcome {
        DriveOutcome::Unresolved { waits } => {
            assert!(
                waits.iter().any(|wait| {
                    wait.fact == super::drive::fact_dependency(settled_fact(FactKey::FunctionDefined(function_id)))
                        && wait.jobs.contains(&Job::SeedRoot(root_id))
                }),
                "unresolved drive should report SeedRoot waiting on the entry definition"
            );
            assert!(
                work_graph
                    .all()
                    .into_iter()
                    .any(
                        |step| step.blocked.contains(&super::drive::fact_dependency(settled_fact(
                            FactKey::FunctionDefined(function_id)
                        )))
                    ),
                "work-graph telemetry should carry the exact fact that blocked the seed job"
            );
        }
        other => panic!("root-before-code should finish unresolved: {other:?}"),
    }
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("missing global entry diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::RESOLVE_UNKNOWN_FUNCTION.0,
        "missing top-level roots should report an unknown-function diagnostic"
    );
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "function `main/0` is not defined",
        "missing top-level roots should name the unresolved function"
    );

    match compiler.drive() {
        DriveOutcome::Unresolved { .. } => {}
        other => panic!("re-driving an unchanged missing root should stay unresolved: {other:?}"),
    }
    assert_eq!(
        capture.count(&["fz", "diag", "error"]),
        1,
        "the same unresolved root should not re-emit duplicate diagnostics"
    );

    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/late_main.fz".to_string()),
        text: include_str!("../../fixtures2/00009_no_runtime.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "adding the entry definition should resolve the waiting root",
    );
}

#[test]
fn compiler2_submit_module_root_without_code_reports_one_unknown_module_diag() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    match compiler.drive() {
        DriveOutcome::Unresolved { .. } => {}
        other => panic!("missing module root should finish unresolved: {other:?}"),
    }
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("missing module diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::RESOLVE_UNKNOWN_MODULE.0,
        "missing named roots should report the missing module, not an internal wait fact"
    );
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `User` is not defined",
        "missing named roots should name the unresolved module"
    );
    assert_eq!(
        capture.count(&["fz", "diag", "error"]),
        1,
        "one missing module should emit one diagnostic even when multiple waits depend on it"
    );

    match compiler.drive() {
        DriveOutcome::Unresolved { .. } => {}
        other => panic!("re-driving an unchanged missing module should stay unresolved: {other:?}"),
    }
    assert_eq!(
        capture.count(&["fz", "diag", "error"]),
        1,
        "the same unresolved module should not re-emit duplicate diagnostics"
    );
}

#[test]
fn compiler2_submit_code_after_root_auto_scopes_new_definitions_without_reseeding_semantics() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_only.fz".to_string()),
        text: include_str!("../../fixtures2/00009_no_runtime.fz").to_string(),
    });
    let _root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "first drive should seed the initial root");
    let lowered_before = outputs.stops_matching(|job| matches!(job, Job::LowerFunction(_))).len();
    let seed_stops_before = outputs.stops_matching(|job| matches!(job, Job::SeedRoot(_))).len();
    assert!(
        seed_stops_before >= 2,
        "entry seeding should settle before later code arrives"
    );

    let late_code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/late_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00030_foo_42.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "second drive should scope late code automatically while a root is active",
    );

    let scope_outputs = outputs
        .take(Job::ScopeCode(late_code_id))
        .expect("late code ScopeCode job effects");
    // Scope publication is demand-addressed (fz-f98.14.5): the late ScopeCode
    // publishes CodeScoped and eagerly stashes foo/0's source, but does NOT
    // output FunctionSource for the uncalled foo. The auto-scope is proven by the
    // CodeScoped output plus foo/0's eager `stashed` capture.
    assert!(
        scope_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::CodeScoped(late_code_id)),
        "late code should auto-scope without an explicit ScopeCode demand"
    );
    let foo_id = function_id(&functions, "foo", 0);
    assert!(
        !scope_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::FunctionSource(foo_id)),
        "an uncalled late foo/0 should be stashed, not body-published, by auto-scope"
    );
    assert_eq!(
        outputs.stops_matching(|job| matches!(job, Job::SeedRoot(_))).len(),
        seed_stops_before,
        "late unrelated code should not reseed the existing root"
    );
    assert_eq!(
        outputs.stops_matching(|job| matches!(job, Job::LowerFunction(_))).len(),
        lowered_before,
        "late unrelated code should not lower foo/0 just because a root already exists"
    );
}

#[test]
fn compiler2_lower_function_mints_lambda_defs_without_eagerly_lowering_them() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/local_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00031_local_lambda.fz").to_string(),
    });
    let _root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "rooting a local lambda should lower only the reachable owner and generated lambda bodies",
    );

    let main_id = function_id(&functions, "main", 0);
    let lower_outputs = outputs
        .take(Job::LowerFunction(main_id))
        .expect("LowerFunction job effects for local-lambda main/0");
    let generated = lower_outputs
        .iter()
        .filter_map(|(fact, _)| match fact {
            FactKey::FunctionDefined(function) if *function != main_id => Some(*function),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        lower_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::LoweredBody(main_id)),
        "lowering local-lambda main/0 should publish the lowered body fact"
    );
    assert_eq!(
        generated.len(),
        1,
        "lowering local-lambda main/0 should mint one generated lambda definition"
    );
    assert!(
        !lower_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::LoweredBody(generated[0])),
        "lowering main/0 should not eagerly lower the generated reducer lambda"
    );
    let generated_outputs = outputs
        .take(Job::LowerFunction(generated[0]))
        .expect("LowerFunction job effects for the reached local lambda");
    assert!(
        generated_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::LoweredBody(generated[0])),
        "reaching the local lambda through the rooted call should lower its body in its own job",
    );
    let lowered_functions = outputs
        .stops_matching(|job| matches!(job, Job::LowerFunction(_)))
        .into_iter()
        .filter_map(|stop| match stop.job {
            Job::LowerFunction(function) => Some(function),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let lowered_debug = lowered_functions
        .iter()
        .map(|function_id| {
            let record = functions
                .all()
                .into_iter()
                .find(|record| record.function_id == *function_id)
                .unwrap_or_else(|| panic!("function.defined for lowered function {function_id:?}"));
            format!(
                "{}::{}/{}",
                modules
                    .try_qualified_name(record.module_id)
                    .unwrap_or_else(|| format!("<unnamed:{}>", record.module_id.as_u32())),
                record.function_ref.name,
                record.arity,
            )
        })
        .collect::<HashSet<_>>();
    assert!(
        lowered_functions.contains(&main_id) && lowered_functions.contains(&generated[0]),
        "rooting a local lambda should lower main/0 and later lower the reached generated lambda in its own job; actual={lowered_debug:?}",
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "Compiler2 lowering should not invoke the old frontend lowerer"
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "Compiler2 lowering should stay above the old planner"
    );
}

/// fz-kdt.56's acceptance shape: a call chain three deep plus one mutually
/// recursive pair, so the same program carries a plain reachability answer
/// (nothing on the chain reaches itself) and a cyclic one.
const STATIC_CALL_GRAPH_SOURCE: &str = r#"
fn c(x), do: x + 1
fn b(x), do: c(x) + 1
fn a(x), do: b(x) + 1
fn pong(n), do: ping(n - 1)
fn ping(n) do
  if n <= 0 do
    0
  else
    pong(n)
  end
end
fn main(), do: dbg(a(1) + ping(3))
"#;

/// fz-kdt.56: the static call graph is a per-function FACT, extracted from one
/// body once, and recursion is answered by walking those edges.
///
/// Before this ticket `DeriveRecursive` owned the whole traversal: every
/// evaluation re-extracted the callees of every body it could reach, so
/// discovering one more layer of the graph cost a full re-scan of the layers
/// already known (165 evaluations over 100 functions on
/// `enum_take_drop_split`, 65 of them concluding nothing). Three things have to
/// hold together for the edge fact to be the honest replacement:
///
/// (a) the edges are the body's real callees -- `main` reaches `a` and `ping`,
///     the chain steps `a -> b -> c` one hop at a time, `c` is a leaf, and the
///     mutual pair points at each other;
/// (b) the answer the walking job publishes off those edges is unchanged --
///     `recursive` is true for exactly the cycle, false for the chain and for
///     `main`, which calls into the cycle without being in it;
/// (c) one body, one extraction: each function's `StaticCallees` fact is
///     published by exactly one evaluation of its own job. A function whose
///     edges are read by five different callers still pays for one scan.
#[test]
fn compiler2_static_callee_facts_are_extracted_once_per_body_and_answer_recursion() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_static_call_graph.fz".to_string()),
        text: STATIC_CALL_GRAPH_SOURCE.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "the static call graph fixture should settle");

    let id = |name: &str, arity: u64| function_id(&functions, name, arity);
    let (main, a, b, c, ping, pong) = (
        id("main", 0),
        id("a", 1),
        id("b", 1),
        id("c", 1),
        id("ping", 1),
        id("pong", 1),
    );

    // (a) the edges themselves. Named rather than id-compared, because the
    // graph is the WHOLE static graph: an operator call is a call, so `+` and
    // `<=` are edges into the runtime module exactly like `a` and `ping` are
    // edges into this source.
    let callees = |function: FunctionId| compiler.world().static_callees(function).to_vec();
    let edge_names = |function: FunctionId| {
        callees(function)
            .into_iter()
            .map(|callee| compiler.world().function_ref(callee).name.clone())
            .collect::<BTreeSet<_>>()
    };
    let names = |names: [&str; 2]| names.map(str::to_string).into_iter().collect::<BTreeSet<_>>();
    assert_eq!(
        edge_names(main),
        ["+", "dbg", "a", "ping"].map(str::to_string).into_iter().collect(),
        "main's edges are every function its body calls, operators included",
    );
    assert_eq!(edge_names(a), names(["+", "b"]), "the chain steps one hop at a time");
    assert_eq!(edge_names(b), names(["+", "c"]), "the chain steps one hop at a time");
    assert_eq!(
        edge_names(c),
        ["+"].map(str::to_string).into_iter().collect(),
        "c is a leaf of this source: its only edge is the operator",
    );
    assert_eq!(
        edge_names(ping),
        names(["<=", "pong"]),
        "the mutual pair points at pong"
    );
    assert_eq!(edge_names(pong), names(["-", "ping"]), "the mutual pair points back");

    // The published `Vec` is deterministic by construction: `static_edges`
    // yields a body's edges in ascending function id, and the callee list keeps
    // that order instead of re-sorting a set at publication time.
    for function in [main, a, b, c, ping, pong] {
        let edges = callees(function);
        assert!(
            edges.windows(2).all(|pair| pair[0].as_u32() < pair[1].as_u32()),
            "{function:?} published its callees out of extraction order: {edges:?}",
        );
    }

    // (b) the conclusion drawn from those edges is the same answer the old
    // whole-graph re-walk produced.
    let recursive = |function: FunctionId| {
        compiler
            .world()
            .body_keying(function)
            .unwrap_or_else(|| panic!("body keying for {function:?}"))
            .recursive
    };
    assert!(recursive(ping) && recursive(pong), "the mutual pair is recursive");
    for function in [main, a, b, c] {
        assert!(
            !recursive(function),
            "{function:?} reaches the cycle but never itself, so it is not recursive",
        );
    }

    // (c) one body, one extraction. `DeriveStaticCallees` may block while it
    // waits for the body -- that is demand, not work -- but exactly one of its
    // evaluations may conclude and publish the edges.
    for function in [main, a, b, c, ping, pong] {
        let publications = outputs
            .stops_matching(|job| *job == Job::DeriveStaticCallees(function))
            .into_iter()
            .filter(|stop| {
                stop.effects
                    .as_ref()
                    .is_some_and(|effects| effects.outputs.contains(&FactKey::StaticCallees(function)))
            })
            .count();
        assert_eq!(
            publications, 1,
            "{function:?} should have its body scanned for edges exactly once, not once per reader",
        );
    }
}

/// fz-kdt.61: the call graph's strong components are a per-function FACT, and
/// recursion is a projection of it.
///
/// `CallGraphComponent(f)` stores the SMALLEST `FunctionId` mutually reachable
/// with `f`. A strong component is a set and its minimum is a function of that
/// set alone, so two functions are mutually reachable exactly when their
/// stored ids are EQUAL -- membership becomes a comparison of two fact reads
/// instead of a traversal at every asking site.
///
/// Three things hold together on the same chain-plus-cycle fixture the edge
/// facts use:
///
/// (a) the cycle shares one canonical id and the chain does not, and the id is
///     genuinely the smallest member rather than whichever node was walked
///     first;
/// (b) recursion agrees with component membership everywhere -- `recursive` is
///     true for exactly the functions whose component has more than one member
///     or whose own edge set names them. This is the same answer the deleted
///     `reaches_self` walk produced, now read off the component;
/// (c) both facts come from ONE evaluation. The walk is not paid for twice:
///     the evaluation that publishes `CallGraphComponent(f)` is the same one
///     that publishes `Recursive(f)`.
#[test]
fn compiler2_call_graph_components_are_canonical_and_answer_recursion() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_call_graph_components.fz".to_string()),
        text: STATIC_CALL_GRAPH_SOURCE.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "the call graph fixture should settle");

    let id = |name: &str, arity: u64| function_id(&functions, name, arity);
    let (main, a, b, c, ping, pong) = (
        id("main", 0),
        id("a", 1),
        id("b", 1),
        id("c", 1),
        id("ping", 1),
        id("pong", 1),
    );
    let component = |function: FunctionId| {
        compiler
            .world()
            .call_graph_component(function)
            .unwrap_or_else(|| panic!("call graph component for {function:?}"))
    };

    // (a) the mutual pair is one component; the chain is four separate ones.
    assert_eq!(
        component(ping),
        component(pong),
        "ping and pong reach each other, so they share one component",
    );
    assert_eq!(
        component(ping),
        ping.min(pong),
        "the canonical member is the SMALLEST id in the component, not whichever \
         node the walk happened to start from",
    );
    for function in [main, a, b, c] {
        assert_eq!(
            component(function),
            function,
            "{function:?} reaches nothing that reaches it back, so it is its own component",
        );
    }
    let chain = [main, a, b, c, ping];
    for (index, left) in chain.iter().enumerate() {
        for right in &chain[index + 1..] {
            assert_ne!(
                component(*left),
                component(*right),
                "{left:?} and {right:?} are not mutually reachable and must not share an id",
            );
        }
    }

    // (b) recursion is that same answer, read off the component.
    let recursive = |function: FunctionId| {
        compiler
            .world()
            .body_keying(function)
            .unwrap_or_else(|| panic!("body keying for {function:?}"))
            .recursive
    };
    for function in [main, a, b, c, ping, pong] {
        let members = [main, a, b, c, ping, pong]
            .into_iter()
            .filter(|other| component(*other) == component(function))
            .count();
        let self_edge = compiler.world().static_callees(function).contains(&function);
        assert_eq!(
            recursive(function),
            members > 1 || self_edge,
            "{function:?}: recursion must agree with its component membership",
        );
    }
    assert!(recursive(ping) && recursive(pong), "the mutual pair is recursive");
    for function in [main, a, b, c] {
        assert!(
            !recursive(function),
            "{function:?} reaches the cycle but never itself, so it is not recursive",
        );
    }

    // (c) one walk, two facts. A split job would pay for the traversal twice.
    for function in [main, a, b, c, ping, pong] {
        let publications = outputs
            .stops_matching(|job| *job == Job::DeriveCallGraphComponent(function))
            .into_iter()
            .filter(|stop| {
                stop.effects.as_ref().is_some_and(|effects| {
                    effects.outputs.contains(&FactKey::CallGraphComponent(function))
                        && effects.outputs.contains(&FactKey::Recursive(function))
                })
            })
            .count();
        assert_eq!(
            publications, 1,
            "{function:?}: the component and the keying it decides must publish from exactly \
             one evaluation of one walk",
        );
    }
}

#[test]
fn compiler2_recursive_keying_sees_recursion_through_generated_lambdas() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let analyzed = ActivationAnalysisCapture::new();
    analyzed.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_lambda_recursion_keying.fz".to_string()),
        text: include_str!("../../fixtures2/00032_lambda_recursion.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "lambda-mediated recursion should settle through recursive activation key facts",
    );

    let build_id = function_id(&functions, "build", 2);
    let generated = generated_functions_owned_by(&functions, build_id);
    assert_eq!(
        generated.len(),
        1,
        "lowering build/2 should mint the generated recursive step lambda",
    );
    assert!(
        outputs
            .take(Job::DeriveCallGraphComponent(build_id))
            .expect("DeriveCallGraphComponent job effects for build/2")
            .contains(&presence(FactKey::Recursive(build_id), true)),
        "the recursive fact should be published for closure-mediated recursion",
    );
    assert!(
        !outputs
            .stops_matching(|job| *job == Job::LowerFunction(generated[0].function_id))
            .is_empty(),
        "deriving recursion should inspect the generated lambda body instead of peeking only at build/2",
    );

    // `build/2` RETURNS its accumulator (the `n == 0` branch is `acc`), and the
    // recursion that rebuilds it runs inside a generated lambda rather than in
    // `build/2`'s own entries -- which fz-kdt.199's self-call exclusion cannot
    // see. So the accumulator is keyed and its seed `[]` stands apart from the
    // ascended `list(int)`: TWO keys, one ascent rung, both bodies identical.
    // That is a cost this ticket does not buy anything with (the seed
    // activation is shared by every caller either way), and closing it needs
    // the strong component rather than one body. It is the same class as the
    // 91 corpus executables the returned axis adds that gain no distinct
    // published return (against 36 that do), dominated by `List.reduce_*`
    // minting fz-kdt.182 `empty_list()`/`list(tau)` rungs across the
    // cont<->step cycle: fz-kdt.213 owns removing it, so the 2 below is a
    // RECORD of a known-unbought split and not a law. What the test is FOR is
    // unchanged: recursion is seen through the generated lambda at all. Read
    // off the settled per-activation `activation_analysis.defined` frontier,
    // keeping only keys that earned a converged return (dropping
    // mid-convergence intermediates).
    let settled_returns = returns.settled_activations(root_id);
    let build_activations = analyzed
        .keys_for_root(root_id)
        .into_iter()
        .filter(|activation| activation.function == build_id && settled_returns.contains(activation))
        .collect::<HashSet<_>>();
    assert_eq!(
        build_activations.len(),
        2,
        "a returned accumulator whose rebuild hides inside a generated lambda keys its seed apart \
         from its ascent -- a known-unbought split fz-kdt.213 owns, pinned so it cannot grow",
    );
    assert!(
        build_activations
            .iter()
            .all(|activation| activation.input_len(compiler.types_for_test()) != 0),
        "the collapsed build/2 activation should still carry the recursive accumulator slot",
    );
}

#[test]
fn compiler2_lowered_body_keeps_clause_projections_separate_from_entry_matching() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/lowered_clause_projections.fz".to_string()),
        text: include_str!("../../fixtures2/00033_clause_projections.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index the clause fixture");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "lowering still needs defined functions",
    );
    assert_resolved(compiler.drive(), "second drive should define the clause fixture");

    let wanted_id = function_id(&functions, "wanted", 1);
    assert!(
        compiler.demand(Job::LowerFunction(wanted_id)),
        "wanted/1 should be demandable for lowering",
    );
    assert_resolved(
        compiler.drive(),
        "lowering should publish a body without re-embedding entry dispatch",
    );

    let lowered_outputs = outputs
        .take(Job::LowerFunction(wanted_id))
        .expect("LowerFunction job effects for wanted/1");
    assert!(
        lowered_outputs.contains(&presence(FactKey::LoweredBody(wanted_id), true)),
        "lowering wanted/1 should publish its lowered body fact",
    );

    let body = lowered_body(&bodies, wanted_id);
    let LoweredBody::Clauses { clauses, .. } = body else {
        panic!("wanted/1 should lower as clauses");
    };
    assert_eq!(clauses.len(), 2, "wanted/1 should preserve both source clauses");
    assert!(
        !clauses[0].projections.is_empty(),
        "destructuring heads should retain projection steps after dispatch picks the clause",
    );
    assert!(
        clauses[0].projections.iter().all(|step| {
            matches!(
                step,
                LoweredStep::TupleField { .. } | LoweredStep::FieldAccess { .. } | LoweredStep::SplitList { .. }
            )
        }),
        "entry-clause lowering should keep only projection steps and not repeat matcher asserts",
    );
}

#[test]
fn compiler2_generated_lambda_body_binds_captures_as_leading_inputs() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/lambda_capture_inputs.fz".to_string()),
        text: include_str!("../../fixtures2/00034_lambda_capture.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index the capture fixture");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "lowering still needs a defined owner function"
    );
    assert_resolved(compiler.drive(), "second drive should define the capture fixture");

    let main_id = function_id(&functions, "main", 1);
    assert!(
        compiler.demand(Job::LowerFunction(main_id)),
        "main/1 should be demandable for lowering"
    );
    assert_resolved(
        compiler.drive(),
        "lowering main/1 should mint the generated lambda definition",
    );

    let generated = generated_functions_owned_by(&functions, main_id);
    assert_eq!(generated.len(), 1, "lowering main/1 should mint one generated lambda");
    let lambda_id = generated[0].function_id;

    assert!(
        compiler.demand(Job::LowerFunction(lambda_id)),
        "generated lambda should lower on demand"
    );
    assert_resolved(
        compiler.drive(),
        "lowering the generated lambda should bind captures as real inputs",
    );

    let lowered_outputs = outputs
        .take(Job::LowerFunction(lambda_id))
        .expect("LowerFunction job effects for generated lambda");
    assert!(
        lowered_outputs.contains(&presence(FactKey::LoweredBody(lambda_id), true)),
        "lowering the generated lambda should publish its lowered body fact",
    );

    let body = lowered_body(&bodies, lambda_id);
    let LoweredBody::Clauses { clauses, .. } = body else {
        panic!("generated lambda should lower as clauses");
    };
    assert_eq!(
        clauses.len(),
        1,
        "the generated lambda should preserve its single source clause"
    );
    assert_eq!(
        clauses[0].params.len(),
        2,
        "generated lambda entry params should be [captured values..., explicit args...]",
    );
}

#[test]
fn compiler2_lowered_body_keeps_local_match_asserts_inside_the_body() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/lowered_local_match.fz".to_string()),
        text: include_str!("../../fixtures2/00035_local_match.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index the local match fixture");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "lowering still needs a defined function",
    );
    assert_resolved(compiler.drive(), "second drive should define the local match fixture");

    let main_id = function_id(&functions, "main", 0);
    assert!(
        compiler.demand(Job::LowerFunction(main_id)),
        "main/0 should be demandable for lowering",
    );
    assert_resolved(compiler.drive(), "lowering should publish the local match body");

    let lowered_outputs = outputs
        .take(Job::LowerFunction(main_id))
        .expect("LowerFunction job effects for main/0");
    assert!(
        lowered_outputs.contains(&presence(FactKey::LoweredBody(main_id), true)),
        "lowering main/0 should publish its lowered body fact",
    );

    let body = lowered_body(&bodies, main_id);
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        panic!("main/0 should lower as clauses");
    };
    assert_eq!(
        clauses[0].projections.len(),
        0,
        "main/0 has no head params to project after entry dispatch",
    );
    assert!(
        entries[clauses[0].entry.as_u32() as usize].steps.iter().any(|step| {
            matches!(
                step,
                LoweredStep::AssertTuple { .. } | LoweredStep::AssertLiteral { .. } | LoweredStep::AssertSame { .. }
            )
        }),
        "local match expressions should still lower their own assert steps inside the body",
    );
}

#[test]
fn compiler2_lowering_routes_nontail_if_join_flow_through_delivered_resume() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00466_nontail_if_join_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00466_nontail_if_join_flow.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(compiler.drive(), "first drive should index the non-tail join fixture");

    let map_every_list_id = function_id(&functions, "map_every_list", 4);
    assert!(
        compiler.demand(Job::LowerFunction(map_every_list_id)),
        "map_every_list/4 should be demandable for lowering",
    );
    assert_resolved(
        compiler.drive(),
        "lowering map_every_list/4 should publish the non-tail branch join shape",
    );

    let lowered_outputs = outputs
        .take(Job::LowerFunction(map_every_list_id))
        .expect("LowerFunction job effects for map_every_list/4");
    assert!(
        lowered_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::LoweredBody(map_every_list_id)),
        "lowering map_every_list/4 should surface its lowered body fact",
    );

    let body = lowered_body(&bodies, map_every_list_id);
    let LoweredBody::Clauses { entries, .. } = body else {
        panic!("map_every_list/4 should lower as clauses");
    };

    let closure_join = entries.iter().find_map(|entry| match &entry.tail {
        LoweredTail::ClosureCall {
            dest: crate::compiler2::ControlDestination::Deliver(entry_id),
            ..
        } => Some(*entry_id),
        _ => None,
    });
    let value_join = entries.iter().find_map(|entry| match &entry.tail {
        LoweredTail::Value {
            dest: crate::compiler2::ControlDestination::Deliver(entry_id),
            ..
        } => Some(*entry_id),
        _ => None,
    });

    let join_id = closure_join.expect("non-tail join fixture should deliver a closure-call result to a join");
    assert_eq!(
        Some(join_id),
        value_join,
        "the closure-call and passthrough value branches should reconverge at the same join entry",
    );
    assert!(
        matches!(
            entries[join_id.as_u32() as usize].origin,
            ControlEntryOrigin::DeliveredResume { .. }
        ),
        "a join reached by a closure-call result should publish itself as a delivered resume, not a local helper",
    );
}

#[test]
fn compiler2_native_program_routes_nontail_if_join_flow_through_continuation_entries() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00466_nontail_if_join_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00466_nontail_if_join_flow.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "non-tail join fixture should settle before native continuation inspection",
    );

    let program = native.last(root_id).program;
    let join_continuations = program
        .module
        .fns
        .iter()
        .filter(|function| function.name.contains("map_every_list"))
        .flat_map(|function| function.blocks.iter())
        .filter_map(|block| match &block.terminator {
            IrTerm::Call { continuation, .. } | IrTerm::CallClosure { continuation, .. } => Some(continuation.fn_id),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(
        !join_continuations.is_empty(),
        "the non-tail join fixture should contain at least one delivered continuation in native IR",
    );

    for continuation_fn in join_continuations {
        let body = program
            .bodies
            .iter()
            .find(|body| body.fn_id == continuation_fn)
            .unwrap_or_else(|| panic!("native body for continuation {:?} missing", continuation_fn));
        assert!(
            matches!(body.entry_abi, NativeEntryAbi::Continuation { .. }),
            "delivered continuation {:?} should publish a continuation entry ABI, got {:?}",
            continuation_fn,
            body.entry_abi,
        );
    }
}

#[test]
// Triaged 2026-08-24: this is NOT awaiting triage, it asserts a contract
// fz-f98.14.11 deliberately superseded. Its param-shape half pins the OLD rule
// that a discarded call result still occupies a delivered return lane
// (`extra_params: 1`); the rule is now that a discarded result carries no demand
// and publishes no lanes, so lowering yields `extra_params: 0`. Its real
// subject -- the reusable-cons capability surviving a delivered continuation --
// is unaffected and still worth pinning. Re-enabling means rewriting the lane
// assertions to the new contract, deriving the expected shape from the rule
// rather than from whatever lowering currently emits. See fz-f98.22.
#[ignore = "asserts the pre-fz-f98.14.11 discarded-result lane contract; see fz-f98.22"]
fn compiler2_native_program_transports_reusable_cons_caps_through_delivered_continuations() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("reusable_cons_continuation.fz".to_string()),
        text: r#"
fn ping(x), do: x

fn rebuild(xs) do
  [h | t] = xs
  ping(0)
  [h | t]
end

fn main(), do: rebuild([1, 2])
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "reusable-cons continuation fixture should settle before native lowering inspection",
    );

    let program = native.last(root_id).program;
    let continuation = program
        .bodies
        .iter()
        .find(|body| matches!(body.origin, NativeBodyOrigin::Continuation { .. }))
        .expect("the non-tail call should lower through a continuation helper");
    let function = program.module.fn_by_id(continuation.fn_id);

    assert!(
        matches!(continuation.entry_abi, NativeEntryAbi::Continuation { extra_params: 1 }),
        "the ignored ping/1 result should still occupy the callee's delivered return lane, got {:?}",
        continuation.entry_abi,
    );
    assert_eq!(
        function.block(function.entry).params,
        vec![
            crate::fz_ir::Var(0),
            crate::fz_ir::Var(1),
            crate::fz_ir::Var(2),
            crate::fz_ir::Var(3),
        ],
        "the continuation should accept the delivered result, its two semantic captures, and one hidden physical source param",
    );
    assert_eq!(
        function.ignored_entry_params,
        vec![true, false, false, false],
        "the delivered ping/1 result is a boundary lane, but it must not become a semantic specialization input",
    );
    assert_eq!(
        function.physical_entry_params,
        vec![crate::fz_ir::Var(3)],
        "the hidden source-cons param should be marked physical on the entry",
    );
    assert_eq!(
        function.physical_capabilities,
        vec![crate::fz_ir::PhysicalCapabilityFact {
            source: crate::fz_ir::Var(3),
            capability: PhysicalCapability::ReusableConsCell {
                rebuilt_head: crate::fz_ir::Var(1),
            },
        }],
        "the continuation should restore the reusable-cons fact for its captured head",
    );
    assert_eq!(
        function.semantic_entry_params(),
        vec![crate::fz_ir::Var(1), crate::fz_ir::Var(2)],
        "semantic entry params must ignore both the unused delivered result and the hidden physical capture",
    );
}

#[test]
fn compiler2_lowered_body_records_reusable_cons_capture_requirements_on_delivered_entries() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("reusable_cons_continuation.fz".to_string()),
        text: r#"
fn ping(x), do: x

fn rebuild(xs) do
  [h | t] = xs
  ping(0)
  [h | t]
end
"#
        .to_string(),
    });

    assert_resolved(compiler.drive(), "reusable-cons fixture should index cleanly");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "reusable-cons fixture still needs function definition before lowered-body inspection",
    );
    assert_resolved(
        compiler.drive(),
        "reusable-cons fixture should define its functions cleanly",
    );

    let rebuild_id = function_id(&functions, "rebuild", 1);
    assert!(
        compiler.demand(Job::LowerFunction(rebuild_id)),
        "rebuild/1 should be demandable for lowered-body inspection",
    );
    assert_resolved(
        compiler.drive(),
        "lowering rebuild/1 should publish reusable-cons capture metadata on its entries",
    );

    let body = lowered_body(&bodies, rebuild_id);
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        panic!("rebuild/1 should lower as clauses");
    };
    let continuation = entries
        .iter()
        .find(|entry| matches!(entry.origin, ControlEntryOrigin::DeliveredResume { .. }))
        .expect("the non-tail call should lower through a delivered-resume entry");
    assert_eq!(
        continuation.reusable_cons_captures.len(),
        1,
        "the delivered entry should declare exactly the one reusable list cell it must receive",
    );

    let capture = continuation.reusable_cons_captures[0];
    assert!(
        continuation.captures.contains(&capture.head),
        "the hidden physical capture should be paired with a semantic capture for the rebuilt head",
    );

    let source = clauses
        .iter()
        .flat_map(|clause| clause.projections.iter())
        .chain(entries.iter().flat_map(|entry| entry.steps.iter()))
        .find_map(|step| match step {
            LoweredStep::SplitList { source, head, .. } if *head == capture.head => Some(*source),
            _ => None,
        });
    assert_eq!(
        source,
        Some(capture.source),
        "the delivered entry should capture the exact source cons paired with its rebuilt head",
    );
}

#[test]
fn compiler2_reusable_cons_telemetry_reports_birth_transport_and_consumption() {
    let tel = ConfiguredTelemetry::new();
    let exits = ProcessExitCapture::new();
    exits.install(&tel);
    let reusable_cons = ReusableConsCapture::new();
    reusable_cons.install(&tel);
    let mut compiler = Compiler2::new(tel);
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some("reusable_cons_continuation.fz".to_string()),
        text: r#"
fn ping(x), do: x

fn rebuild(xs) do
  [h | t] = xs
  ping(0)
  [h | t]
end

fn main(), do: rebuild([1, 2])
"#
        .to_string(),
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("reusable-cons telemetry fixture should run end-to-end: {error}");
    });

    assert_eq!(reusable_cons.last(), Some((root_id, 1, 1)));

    let exit = exits.last().expect("runtime process exit telemetry");
    assert_eq!(exit.reusable_cons_attempts, 1);
    assert_eq!(
        exit.reusable_cons_reused, 1,
        "the transported cell stays unique across the stack-resident continuation, so the \
         rebuilt `[h | t]` reuses it in place instead of allocating a fresh cons",
    );
}

#[test]
fn compiler2_reusable_cons_telemetry_reports_born_but_not_transported() {
    let tel = ConfiguredTelemetry::new();
    let reusable_cons = ReusableConsCapture::new();
    reusable_cons.install(&tel);
    let mut compiler = Compiler2::new(tel);
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some("reusable_cons_no_transport.fz".to_string()),
        text: r#"
fn ping(x), do: x

fn ignore(xs) do
  [h | t] = xs
  ping(0)
  {h, t}
end

fn main(), do: ignore([1, 2])
"#
        .to_string(),
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("born-without-transport fixture should run end-to-end: {error}");
    });

    assert_eq!(reusable_cons.last(), Some((root_id, 1, 0)));
}

#[test]
fn compiler2_reusable_cons_runtime_telemetry_reports_in_place_reuse() {
    let tel = ConfiguredTelemetry::new();
    let exits = ProcessExitCapture::new();
    exits.install(&tel);
    let reusable_cons = ReusableConsCapture::new();
    reusable_cons.install(&tel);
    let mut compiler = Compiler2::new(tel);
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some("reusable_cons_runtime_reuse.fz".to_string()),
        text: r#"
fn rebuild(xs) do
  [h | t] = xs
  [h | t]
end

fn main(), do: rebuild([1, 2])
"#
        .to_string(),
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("direct reusable-cons fixture should run end-to-end: {error}");
    });

    assert_eq!(reusable_cons.last(), Some((root_id, 1, 0)));

    let exit = exits.last().expect("runtime process exit telemetry");
    assert_eq!(exit.reusable_cons_attempts, 1);
    assert_eq!(exit.reusable_cons_reused, 1);
}

#[test]
fn compiler2_reusable_cons_statically_skips_a_returned_source_alias() {
    let run = reusable_cons_run(
        "reusable_cons_returned_source_alias.fz",
        r#"
fn rebuild(xs) do
  [h | t] = xs
  holder = {xs}
  {holder, [h | t]}
end

fn main() do
  dbg(rebuild([1, 2]))
  0
end
"#,
    );

    assert_eq!((run.births, run.transported), (1, 0));
    assert_eq!((run.attempts, run.reused), (0, 0));
    assert!(run.source_and_rebuild_share_return);
    assert_eq!(run.output, ["{{[1, 2]}, [1, 2]}"]);
}

#[test]
fn compiler2_reusable_cons_erases_unused_call_argument_before_reuse() {
    let run = reusable_cons_run(
        "reusable_cons_erased_unused_argument.fz",
        r#"
fn ping(x), do: x

fn rebuild(xs) do
  [h | t] = xs
  ping(xs)
  {xs, [h | t]}
end

fn main(), do: rebuild([1, 2])
"#,
    );

    assert_eq!((run.attempts, run.reused), (1, 1));
}

struct ReusableConsRun {
    births: u64,
    transported: u64,
    attempts: u64,
    reused: u64,
    source_and_rebuild_share_return: bool,
    output: Vec<String>,
}

fn reusable_cons_run(name: &str, source: &str) -> ReusableConsRun {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let exits = ProcessExitCapture::new();
    exits.install(&tel);
    let reusable_cons = ReusableConsCapture::new();
    reusable_cons.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        let diagnostic = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string());
        panic!("alias-fallback reusable-cons fixture should run end-to-end: {error}; {diagnostic:?}");
    });

    let exit = exits.last().expect("runtime process exit telemetry");
    let (_, births, transported) = reusable_cons.last().expect("reusable-cons compilation telemetry");
    let source_and_rebuild_share_return = reusable_cons_source_and_rebuild_share_return(&native.last(root_id).program);
    ReusableConsRun {
        births,
        transported,
        attempts: exit.reusable_cons_attempts,
        reused: exit.reusable_cons_reused,
        source_and_rebuild_share_return,
        output: dbg.lines(),
    }
}

fn reusable_cons_source_and_rebuild_share_return(program: &NativeProgram) -> bool {
    program.module.fns.iter().any(|function| {
        function.physical_capabilities.iter().any(|fact| {
            let PhysicalCapability::ReusableConsCell { rebuilt_head } = fact.capability;
            let rebuilt = function
                .blocks
                .iter()
                .flat_map(|block| block.stmts.iter())
                .find_map(|stmt| match stmt {
                    IrStmt::Let(value, IrPrim::MakeList(items, Some(_))) if items.as_slice() == [rebuilt_head] => {
                        Some(*value)
                    }
                    _ => None,
                });
            rebuilt.is_some_and(|rebuilt| {
                function.blocks.iter().any(|block| {
                    matches!(
                        &block.terminator,
                        IrTerm::ReturnLanes(lanes)
                            if lanes.contains(&fact.source) && lanes.contains(&rebuilt)
                    )
                })
            })
        })
    })
}

/// fz-km1 — `Enumerable.slice/1` returns a slicer that ignores its parameter and
/// answers from its capture, the shape `map.fz`'s `fn (_map) -> to_list(map) end`
/// has. Such a callable has two semantic inputs but publishes a layout for only
/// one: an input the target never reads carries no runtime demand. A member's
/// `target_inputs` is therefore sparse, keyed by `semantic_index` — which is why
/// every entry carries one — and a consumer must look inputs up by that key
/// rather than assume one entry per semantic input.
#[test]
fn compiler2_jit_and_backend_interp_agree_on_a_callable_that_ignores_its_argument() {
    let source = r#"
fn slice(xs) do
  {:ok, 3, (fn (_arg) -> xs end)}
end

fn main() do
  {:ok, n, slicer} = slice([1, 2, 3])
  dbg(n)
  dbg(slicer.([9, 9]))
end
"#;

    let run_lane = |jit: bool| {
        let tel = ConfiguredTelemetry::new();
        let dbg = DbgCapture::new();
        let mut compiler = Compiler2::new(tel);
        compiler.set_output(dbg.sink());
        compiler.submit_code(CodeSubmission {
            name: Some("callable_ignoring_its_argument.fz".to_string()),
            text: source.to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        if jit {
            compiler
                .run_root_jit(root)
                .expect("compiler2 jit should run a callable that ignores its argument");
        } else {
            compiler
                .run_root_interp(root)
                .expect("compiler2 backend interpreter should run a callable that ignores its argument");
        }
        dbg.lines()
    };

    let jit = run_lane(true);
    assert_eq!(jit, vec!["3", "[1, 2, 3]"], "the slicer answers from its capture");
    assert_eq!(
        run_lane(false),
        jit,
        "jit and backend interpreter should agree on a callable whose argument carries no runtime demand",
    );
}

/// fz-f98.14.11, re-aimed by fz-kdt.155 — the two halves of one indirect
/// calling convention are compiled against ONE contract. `Enum.each`'s step
/// discards the mapper's result:
///
/// ```fz
/// fnp each_step(entry, acc, fun) do
///   fun.(entry)
///   acc
/// end
/// ```
///
/// and the question is which lane count both halves settle on. Deriving the
/// payload from the CALLER's own return was the original break (`each_step`
/// returns a demanded `acc`, so a discarded result claimed a lane the boundary
/// never delivered). Deriving it from the callsite's own appetite -- zero
/// lanes for a discarded result -- only moved the disagreement: a callsite
/// reaching a FIRST-CLASS callee owns none of the members behind the wrapper,
/// so its "ignore" never reaches them and the wrapper hands a value back
/// anyway (`mailbox_closure_each`).
///
/// So the claim is not about any one lane count. It is that the two halves
/// AGREE: every boxed closure callsite delivers exactly what the wrappers it
/// can reach publish. `a_mixed` is the program that made the difference
/// visible -- one lambda reached both grounded and boxed, and wrappers of two
/// different arities in one program, so the honest comparison is per wrapper
/// and not a single set over the whole program.
#[test]
fn compiler2_discarded_indirect_call_result_matches_its_boundary_return() {
    fn assert_seam_halves_agree(name: &str, text: &str) {
        let tel = ConfiguredTelemetry::new();
        let backend = BackendProgramCapture::new();
        backend.install(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some(name.to_string()),
            text: text.to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        demand_backend_product(&mut compiler, root);
        assert_resolved(compiler.drive(), "the seam-agreement root should settle");
        let program = backend.last(root).program;

        let mut checked = 0;
        for executable in program.executables() {
            let crate::compiler2::BackendBody::Clauses { entries, .. } = &executable.body else {
                continue;
            };
            for entry in entries {
                let crate::compiler2::BackendTail::ClosureCall {
                    callee,
                    args,
                    return_flow,
                    ..
                } = &entry.tail
                else {
                    continue;
                };
                // A grounded callee is lowered as a direct edge and aliases its
                // target's own return fact; only a boxed one reaches a wrapper.
                if !executable.abi.value_layouts.get(callee).is_some_and(|layout| {
                    matches!(layout.carrier, crate::compiler2::pull::TransportCarrier::ValueRef(_))
                }) {
                    continue;
                }
                let Some(crate::compiler2::artifact::BackendReturnFlow::Deliver { source, .. }) = return_flow else {
                    continue;
                };
                let delivered = source.layout.reprs.len();
                for wrapper in program
                    .construction_wrappers()
                    .iter()
                    .filter(|wrapper| wrapper.call_arity == args.len())
                    .filter(|wrapper| {
                        !matches!(
                            wrapper.return_form,
                            crate::compiler2::artifact::BackendCallableReturn::Diverges
                        )
                    })
                {
                    let published = match wrapper.return_form {
                        crate::compiler2::artifact::BackendCallableReturn::ValueRef => 1,
                        crate::compiler2::artifact::BackendCallableReturn::Absent
                        | crate::compiler2::artifact::BackendCallableReturn::Diverges => 0,
                    };
                    assert_eq!(
                        published,
                        delivered,
                        "{name}: a boxed closure call taking {} argument(s) delivers {delivered} lane(s) while \
                         wrapper {:?} it can reach publishes {published} ({:?})",
                        args.len(),
                        wrapper.identity,
                        wrapper.return_form,
                    );
                    checked += 1;
                }
            }
        }
        assert!(
            checked > 0,
            "{name} should contain at least one boxed closure callsite reaching a wrapper",
        );
    }

    assert_seam_halves_agree(
        "fixtures2/behavior/opaque_fn_each_discarded_return.fz",
        include_str!("../../fixtures2/behavior/opaque_fn_each_discarded_return.fz"),
    );
    assert_seam_halves_agree(
        "fixtures2/behavior/a_mixed.fz",
        include_str!("../../fixtures2/behavior/a_mixed.fz"),
    );
}

/// fz-kdt.155 — the other side of the same axis, at the lane level: a callable
/// NO boxed seam reaches builds no construction wrapper, so nothing outranks
/// its callsites and a discarded closure call really does compile to zero
/// delivered lanes on both halves. `static_closure_each` is
/// `mailbox_closure_each` with the mailbox removed, and this is the pin that
/// says removing the mailbox is what changes the answer -- without it, the
/// seam rule could quietly widen every closure call in the language and every
/// behavioural fixture would still pass, one boxed allocation per call poorer.
#[test]
fn compiler2_never_boxed_discarded_closure_call_delivers_no_lanes() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let backend = BackendProgramCapture::new();
    backend.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/static_closure_each.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/static_closure_each.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root);
    assert_resolved(compiler.drive(), "the static closure each root should settle");
    let program = backend.last(root).program;

    assert!(
        program.construction_wrappers().is_empty(),
        "a lambda named where it is used never crosses the boxed seam, so the program builds no \
         construction wrapper at all: {:?}",
        program
            .construction_wrappers()
            .iter()
            .map(|wrapper| (&wrapper.identity, wrapper.return_form))
            .collect::<Vec<_>>(),
    );

    // `each_step` is the one call in the program that throws its callee's
    // result away; the reducer calls around it legitimately use theirs.
    let each_step_id = function_id(&functions, "each_step", 3);
    let mut checked = 0;
    for executable in program.executables() {
        if executable.key.activation.function != each_step_id {
            continue;
        }
        let crate::compiler2::BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries {
            let crate::compiler2::BackendTail::ClosureCall { return_flow, .. } = &entry.tail else {
                continue;
            };
            let Some(crate::compiler2::artifact::BackendReturnFlow::Deliver { source, .. }) = return_flow else {
                continue;
            };
            checked += 1;
            assert!(
                source.layout.reprs.is_empty(),
                "no seam boxes this callable, so a discarded closure call publishes no return lanes; \
                 it claimed {:?}",
                source.layout.reprs,
            );
        }
    }
    assert!(
        checked > 0,
        "static_closure_each should contain the each-step closure callsite",
    );
}

/// fz-6gb — a lambda literal's *identity* must not fan functions that merely
/// TRANSPORT it out into per-call-site copies. Elixir compiles one body for
/// `Enum.find/2` no matter how many `fn` literals a program writes; in fz,
/// a function that neither calls through a callable nor captures one into a
/// lambda it constructs treats closure brands as freight, and every
/// same-surface brand shares its activation. Identity-CONSUMING functions
/// deliberately retain separate semantic activations: `find/3` captures the
/// predicate into its wrapper lambda, and the wrapper calls it, so both remain
/// keyed per brand. Native lowering may map equivalent boxed-call activations
/// to one physical CPS graph; grounded direct targets remain distinct, as
/// `compiler2_native_program_keeps_direct_callable_specializations_inequivalent`
/// pins. The semantic marginal cost of a call site is therefore three
/// executables (its lambda, the constructor's split, the wrapper's split), not
/// the seven it was when the pure transporters `find/2` and three
/// `reduce_while/3`s respecialized too. This pins the
/// correlation-preserving regime below `ACTIVATION_INPUT_ROW_BUDGET`; past
/// the budget the evidence rows collapse to their join and the
/// identity-consuming splits merge too (a 32-site program settles 45
/// executables -- 13 shared plus one per lambda -- where it compiled 233
/// before).
#[test]
fn compiler2_same_shape_lambda_literals_share_the_library_chain() {
    let source_for = |sites: usize| {
        let mut source = String::from("fn main() do\n  xs = [1, 2, 3, 4]\n");
        for bound in 0..sites {
            source.push_str(&format!("  dbg(Enum.find(xs, fn (x) -> x > {bound} end))\n"));
        }
        source.push_str("end\n");
        source
    };

    let run_lane = |sites: usize, jit: bool| {
        let tel = ConfiguredTelemetry::new();
        let backend = BackendProgramCapture::new();
        backend.install(&tel);
        let dbg = DbgCapture::new();
        let mut compiler = Compiler2::new(tel);
        compiler.set_output(dbg.sink());
        compiler.submit_code(CodeSubmission {
            name: Some(format!("lambda_literals_{sites}.fz")),
            text: source_for(sites),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        if jit {
            compiler
                .run_root_jit(root)
                .expect("compiler2 jit should run same-shape lambda literals");
        } else {
            compiler
                .run_root_interp(root)
                .expect("compiler2 backend interpreter should run same-shape lambda literals");
        }
        (dbg.lines(), backend.last(root).program.executables().len())
    };

    let (one_site_out, one_site_executables) = run_lane(1, true);
    assert_eq!(
        one_site_out,
        vec!["1"],
        "Enum.find([1,2,3,4], &(&1 > 0)) is 1, as in Elixir"
    );

    let (two_site_out, two_site_executables) = run_lane(2, true);
    assert_eq!(
        two_site_out,
        vec!["1", "2"],
        "each site finds its own first match, as in Elixir"
    );
    assert_eq!(
        run_lane(2, false).0,
        two_site_out,
        "jit and backend interpreter should agree when two lambda brands share the library chain"
    );

    // The second call site's marginal cost is its own lambda plus the two
    // identity-consuming specializations (`find/3` captures the predicate
    // into its wrapper; the wrapper calls it) -- never a private copy of the
    // transport-only chain (`find/2`, the `reduce_while/3`s).
    assert_eq!(
        two_site_executables,
        one_site_executables + 3,
        "a second same-shape lambda literal should add its own executable and the \
         two identity-consuming splits, not respecialize the transport chain \
         ({one_site_executables} -> {two_site_executables})"
    );
}

/// fz-66j — `Enumerable.reduce/3` hands back a `{:cont, acc}` envelope for
/// every element, exactly as Elixir's protocol does. The envelope is consumed
/// lane-wise the instant it arrives: nothing ever asks for it as a heap object.
/// Whether a tuple becomes a heap object is a representation question the value
/// layout's carrier already answers, so both backends must answer it the same
/// way -- otherwise the count grows with the input on one path and not the
/// other, and `Process.heap_alloc_stats` means something different per backend.
#[test]
fn compiler2_jit_and_backend_interp_agree_on_reduce_envelope_materialization() {
    let source = r#"
fn main() do
  xs = [1, 2, 3, 4, 5]
  dbg(Enum.reduce(xs, 0, fn (x, acc) -> acc + x end))
  stats = Process.heap_alloc_stats()
  dbg(stats[:struct_allocs])
end
"#;

    let run_lane = |jit: bool| {
        let tel = ConfiguredTelemetry::new();
        let dbg = DbgCapture::new();
        let mut compiler = Compiler2::new(tel);
        compiler.set_output(dbg.sink());
        compiler.submit_code(CodeSubmission {
            name: Some("reduce_envelope_materialization.fz".to_string()),
            text: source.to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        if jit {
            compiler
                .run_root_jit(root)
                .expect("compiler2 jit should run the reduce-envelope fixture");
        } else {
            compiler
                .run_root_interp(root)
                .expect("compiler2 backend interpreter should run the reduce-envelope fixture");
        }
        dbg.lines()
    };

    let jit = run_lane(true);
    let interp = run_lane(false);

    assert_eq!(
        jit.first(),
        interp.first(),
        "both backends should reduce to the same sum"
    );
    assert_eq!(
        jit.get(1),
        interp.get(1),
        "jit and backend interpreter should agree on how many reduce envelopes become heap objects",
    );
}

#[test]
// Triaged 2026-08-24: blocked on fz-k22, not awaiting triage. It fails with
// that ticket's exact signature -- "backend value ValueId(0) ... must be bound
// before runtime use" (native.rs's unbound-value invariant) -- so this test is
// one of fz-k22's detectors and re-enables with it.
#[ignore = "blocked on fz-k22: generic Enum HOF leaves a backend value unbound"]
fn compiler2_jit_and_backend_interp_agree_on_reusable_cons_exit_counters() {
    let source = r#"
fn ping(x), do: x

fn rebuild(xs) do
  [h | t] = xs
  [h | t]
end

fn rebuild_after_publish(xs) do
  [h | t] = xs
  ping(xs)
  {xs, [h | t]}
end

fn main() do
  rebuild([1, 2])
  rebuild_after_publish([3, 4])
  0
end
"#;

    let jit_tel = ConfiguredTelemetry::new();
    let jit_exits = ProcessExitCapture::new();
    jit_exits.install(&jit_tel);
    let mut jit_compiler = Compiler2::new(jit_tel);
    let jit_root = jit_compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    jit_compiler.submit_code(CodeSubmission {
        name: Some("reusable_cons_mixed_exit_counters.fz".to_string()),
        text: source.to_string(),
    });
    jit_compiler.run_root_jit(jit_root).unwrap_or_else(|error| {
        panic!("compiler2 jit should run the mixed reusable-cons fixture: {error}");
    });
    let jit_exit = jit_exits.last().expect("jit runtime process exit telemetry");

    let interp_tel = ConfiguredTelemetry::new();
    let interp_exits = ProcessExitCapture::new();
    interp_exits.install(&interp_tel);
    let mut interp_compiler = Compiler2::new(interp_tel);
    let interp_root = interp_compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    interp_compiler.submit_code(CodeSubmission {
        name: Some("reusable_cons_mixed_exit_counters.fz".to_string()),
        text: source.to_string(),
    });
    let interp_halt = interp_compiler
        .run_root_interp(interp_root)
        .expect("compiler2 backend interpreter should run the mixed reusable-cons fixture");
    assert_eq!(interp_halt, 0);
    let interp_exit = interp_exits.last().expect("interp runtime process exit telemetry");

    assert_eq!(jit_exit.halt_value, 0);
    assert_eq!(jit_exit.halt_value, interp_exit.halt_value);
    assert_eq!(jit_exit.reusable_cons_attempts, 2);
    assert_eq!(jit_exit.reusable_cons_reused, 1);
    assert_eq!(
        jit_exit.reusable_cons_attempts, interp_exit.reusable_cons_attempts,
        "jit and backend interpreter should agree on reusable-cons attempts",
    );
    assert_eq!(
        jit_exit.reusable_cons_reused, interp_exit.reusable_cons_reused,
        "jit and backend interpreter should agree on in-place reusable-cons reuse",
    );
}

#[test]
fn compiler2_native_program_jit_runs_nontail_if_join_flow_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00466_nontail_if_join_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00466_nontail_if_join_flow.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_jit(root_id).unwrap_or_else(|error| {
        panic!("compiler2 native codegen should run the non-tail join fixture end-to-end: {error}");
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["[100, 2, 300, 4]"],
        "a branch that joins a closure-call result with a passthrough value should still rebuild the list correctly",
    );
}

#[test]
fn compiler2_operator_expressions_lower_to_kernel_wrapper_calls() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let callsites = CallsiteCapture::new();
    callsites.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/operator_wrapper_calls.fz".to_string()),
        text: "defmodule Main do\n  fn main(x), do: {x + 1, x == 1, x < 2}\nend\n".to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: Some("Main".to_string()),
        name: "main".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "operator expressions should lower through wrapper calls",
    );

    let main_id = compiler.root_function(root_id);
    let add_id = function_id_in_module(&functions, &modules, "Kernel", "+", 2);
    let eq_id = function_id_in_module(&functions, &modules, "Kernel", "==", 2);
    let lt_id = function_id_in_module(&functions, &modules, "Kernel", "<", 2);
    let reached = callsites
        .all()
        .into_iter()
        .filter(|record| record.key.activation.root == root_id && record.key.activation.function == main_id)
        .filter_map(|record| record.summary.single_target().map(|target| target.callee.clone()))
        .collect::<Vec<_>>();
    assert!(
        reached.contains(&SelectedCallee::Function(add_id))
            && reached.contains(&SelectedCallee::Function(eq_id))
            && reached.contains(&SelectedCallee::Function(lt_id)),
        "main/1 should resolve operator syntax through Kernel wrapper functions, got {reached:?}",
    );
}

#[test]
fn compiler2_kernel_operator_wrappers_lower_to_intrinsic_extern_calls() {
    let tel = ConfiguredTelemetry::new();
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/operator_intrinsic_lanes.fz".to_string()),
        text: "defmodule Main do\n  fn main(), do: {1 + 2, 1 + 2.0, 2.0 + 1, 2.0 + 3.0}\nend\n".to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Main".to_string()),
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "Kernel operator wrapper should lower through typed intrinsic lanes",
    );

    let add_id = function_id_in_module(&functions, &modules, "Kernel", "+", 2);
    let extern_ii = function_id_in_module(&functions, &modules, "Kernel", "fz_op_add_ii", 2);
    let extern_if = function_id_in_module(&functions, &modules, "Kernel", "fz_op_add_if", 2);
    let extern_ff = function_id_in_module(&functions, &modules, "Kernel", "fz_op_add_ff", 2);
    let body = lowered_body(&bodies, add_id);
    direct_call_in_body(body.clone(), extern_ii);
    direct_call_in_body(body.clone(), extern_if);
    direct_call_in_body(body, extern_ff);
}

#[test]
fn compiler2_guard_dispatch_reifies_single_clause_and_transitive_helpers() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let guard_defs = GuardDispatchCapture::new();
    guard_defs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_helpers.fz".to_string()),
        text: include_str!("../../fixtures2/00036_guard_helpers.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index helper functions");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope helper definitions"
    );
    assert_resolved(compiler.drive(), "second drive should define helper functions");

    let positive_id = function_id(&functions, "positive", 1);
    let wanted_id = function_id(&functions, "wanted", 1);

    assert!(
        compiler.demand(Job::ReifyGuardDispatch(positive_id)),
        "dispatch-pure positive/1 should be demandable"
    );
    assert_resolved(compiler.drive(), "positive/1 should reify into a guard dispatch");
    let positive_outputs = outputs
        .take(Job::ReifyGuardDispatch(positive_id))
        .expect("ReifyGuardDispatch job effects for positive/1");
    assert!(
        positive_outputs.contains(&presence(FactKey::GuardDispatch(positive_id), true)),
        "positive/1 should publish its guard dispatch fact"
    );
    let positive_dispatch = guard_dispatch(&guard_defs, positive_id);
    assert!(
        !guard_dispatch_has_nested_dispatch(&positive_dispatch),
        "single-clause positive/1 should reify directly without nested helper dispatch"
    );

    assert!(
        compiler.demand(Job::ReifyGuardDispatch(wanted_id)),
        "dispatch-pure wanted/1 should be demandable"
    );
    assert_resolved(
        compiler.drive(),
        "wanted/1 should reify through its transitive helper call",
    );
    let wanted_outputs = outputs
        .take(Job::ReifyGuardDispatch(wanted_id))
        .expect("ReifyGuardDispatch job effects for wanted/1");
    assert!(
        wanted_outputs.contains(&presence(FactKey::GuardDispatch(wanted_id), true)),
        "wanted/1 should publish its guard dispatch fact"
    );
    let wanted_dispatch = guard_dispatch(&guard_defs, wanted_id);
    assert!(
        guard_dispatch_has_nested_dispatch(&wanted_dispatch),
        "transitive helper calls should reify as nested guard dispatch"
    );
}

#[test]
fn compiler2_guard_dispatch_threads_call_arguments_and_destructuring() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let guard_defs = GuardDispatchCapture::new();
    guard_defs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_destructure.fz".to_string()),
        text: include_str!("../../fixtures2/00037_guard_destructure.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index destructuring helpers");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope destructuring helpers"
    );
    assert_resolved(compiler.drive(), "second drive should define destructuring helpers");

    let wanted_id = function_id(&functions, "wanted", 1);
    assert!(
        compiler.demand(Job::ReifyGuardDispatch(wanted_id)),
        "multi-clause wanted/1 should be demandable"
    );
    assert_resolved(
        compiler.drive(),
        "wanted/1 should reify destructuring heads and threaded helper args",
    );

    let wanted_outputs = outputs
        .take(Job::ReifyGuardDispatch(wanted_id))
        .expect("ReifyGuardDispatch job effects for destructuring wanted/1");
    assert!(
        wanted_outputs.contains(&presence(FactKey::GuardDispatch(wanted_id), true)),
        "multi-clause wanted/1 should publish its guard dispatch fact"
    );
    let wanted_dispatch = guard_dispatch(&guard_defs, wanted_id);
    assert_eq!(
        wanted_dispatch.bodies.len(),
        2,
        "multi-clause helper reification should preserve one body per clause"
    );
    assert!(
        wanted_dispatch
            .plan
            .outcomes
            .iter()
            .flat_map(|outcome| outcome.bindings.iter())
            .any(|binding| binding.name == "n"),
        "destructuring helper reification should preserve inner bound names"
    );
    assert!(
        guard_dispatch_has_binary_nested_input(&wanted_dispatch),
        "nested helper calls should thread computed call arguments into the nested dispatch"
    );
}

#[test]
fn compiler2_guard_dispatch_rejects_cycles() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_cycle.fz".to_string()),
        text: include_str!("../../fixtures2/00038_guard_cycle.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index cyclic helpers");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope cyclic helpers"
    );
    assert_resolved(compiler.drive(), "second drive should define cyclic helpers");

    let a_id = function_id(&functions, "a", 1);
    assert!(
        compiler.demand(Job::ReifyGuardDispatch(a_id)),
        "cyclic helper should still be demandable"
    );
    let outcome = compiler.drive();
    let job = match outcome {
        DriveOutcome::Fatal { job } => job,
        other => panic!("cyclic helper reification should fail fatally: {other:?}"),
    };
    assert_eq!(
        job,
        Job::ReifyGuardDispatch(a_id),
        "fatal job should be the demanded helper reification"
    );

    let diagnostic = capture.last(&["fz", "diag", "error"]).expect("cycle diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::LOWER_UNSUPPORTED.0,
        "helper cycles should surface as unsupported guard reification"
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("cycle detected"),
        "cycle diagnostic should say why helper reification failed"
    );
}

#[test]
fn compiler2_guard_dispatch_rejects_impure_helpers() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_impure.fz".to_string()),
        text: include_str!("../../fixtures2/00039_guard_impure.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index impure helpers");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope impure helpers"
    );
    assert_resolved(compiler.drive(), "second drive should define impure helpers");

    let bad_id = function_id(&functions, "bad", 1);
    assert!(
        compiler.demand(Job::ReifyGuardDispatch(bad_id)),
        "impure helper should still be demandable"
    );
    let outcome = compiler.drive();
    let job = match outcome {
        DriveOutcome::Fatal { job } => job,
        other => panic!("impure helper reification should fail fatally: {other:?}"),
    };
    assert_eq!(
        job,
        Job::ReifyGuardDispatch(bad_id),
        "fatal job should be the demanded impure helper reification"
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("impure helper diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::LOWER_UNSUPPORTED.0,
        "impure helpers should surface as unsupported guard reification"
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("not dispatch-pure"),
        "impure helper diagnostic should explain the rejected property"
    );
}

#[test]
fn compiler2_entry_dispatch_plans_clause_heads_with_preconditions_and_helper_guards() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let entry_defs = EntryDispatchCapture::new();
    entry_defs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_aliases.fz".to_string()),
        text: include_str!("../../fixtures2/00040_entry_dispatch_aliases.fz").to_string(),
    });

    assert_resolved(
        compiler.drive(),
        "first drive should index module and helper definitions",
    );
    let module_ids = module_indexed_ids(
        &outputs
            .take(Job::IndexCode(code_id))
            .expect("IndexCode job effects for module-scoped entry dispatch"),
    );
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope module contents before planning entry dispatch",
    );
    assert_resolved(compiler.drive(), "second drive should scope the root namespace");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "nested module entry dispatch needs the module surface defined first",
    );
    assert_resolved(compiler.drive(), "third drive should define module-scoped functions");

    let wanted_id = function_id(&functions, "wanted", 1);
    let positive_id = function_id(&functions, "positive", 1);
    assert!(
        compiler.demand(Job::PlanEntryDispatch(wanted_id)),
        "multi-clause wanted/1 should be demandable as entry dispatch",
    );
    assert_resolved(
        compiler.drive(),
        "entry-dispatch planning should reify helper guards and publish one shared plan",
    );

    let helper_outputs = outputs
        .take(Job::ReifyGuardDispatch(positive_id))
        .expect("ReifyGuardDispatch job effects for positive/1");
    assert!(
        helper_outputs.contains(&presence(FactKey::GuardDispatch(positive_id), true)),
        "helper planning should automatically publish the nested guard-dispatch fact",
    );
    let wanted_outputs = outputs
        .take(Job::PlanEntryDispatch(wanted_id))
        .expect("PlanEntryDispatch job effects for wanted/1");
    assert!(
        wanted_outputs.contains(&presence(FactKey::EntryDispatch(wanted_id), true)),
        "wanted/1 should publish its entry-dispatch fact",
    );

    let plan = entry_dispatch(&entry_defs, wanted_id);
    assert_eq!(
        plan.outcomes.iter().map(|outcome| outcome.body_id).collect::<Vec<_>>(),
        vec![0, 1, 2],
        "entry dispatch should preserve clause outcomes in source order",
    );
    assert!(
        plan_has_nested_guard_dispatch(&plan),
        "entry guards that call helpers should inline the helper dispatch artifact",
    );
    assert!(
        plan_body_has_type_question(&plan, 0),
        "parameter annotations should surface as type questions on the planned entry arm",
    );
}

#[test]
fn compiler2_entry_dispatch_plans_trivial_single_clause_functions() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let entry_defs = EntryDispatchCapture::new();
    entry_defs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_single_clause.fz".to_string()),
        text: include_str!("../../fixtures2/00041_entry_dispatch_single.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index the single-clause function");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "single-clause entry dispatch still needs a defined function surface",
    );
    assert_resolved(
        compiler.drive(),
        "second drive should define the single-clause function",
    );

    let wanted_id = function_id(&functions, "wanted", 1);
    assert!(
        compiler.demand(Job::PlanEntryDispatch(wanted_id)),
        "single-clause functions should still publish entry dispatch",
    );
    assert_resolved(compiler.drive(), "single-clause entry dispatch should plan trivially");

    let wanted_outputs = outputs
        .take(Job::PlanEntryDispatch(wanted_id))
        .expect("PlanEntryDispatch job effects for single-clause wanted/1");
    assert!(
        wanted_outputs.contains(&presence(FactKey::EntryDispatch(wanted_id), true)),
        "single-clause wanted/1 should publish its entry-dispatch fact",
    );

    let plan = entry_dispatch(&entry_defs, wanted_id);
    assert_eq!(plan.outcomes.len(), 1, "trivial entry dispatch should have one outcome");
    assert_eq!(plan.guards.len(), 0, "trivial entry dispatch should not invent guards");
    assert_eq!(
        plan.pinned.len(),
        0,
        "trivial entry dispatch should not invent pinned inputs"
    );
}

#[test]
fn compiler2_entry_dispatch_recomputes_only_the_dependent_helper_blast_radius() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let guard_defs = GuardDispatchCapture::new();
    guard_defs.install(&tel);
    let entry_defs = EntryDispatchCapture::new();
    entry_defs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_blast_radius_v1.fz".to_string()),
        text: include_str!("../../fixtures2/00042_blast_radius_v1.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index helper users");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "scope_code should define helper users"
    );
    assert_resolved(compiler.drive(), "second drive should define helper users");

    let positive_id = function_id(&functions, "positive", 1);
    let wanted_id = function_id(&functions, "wanted", 1);
    let other_id = function_id(&functions, "other", 1);

    assert!(
        compiler.demand(Job::PlanEntryDispatch(wanted_id)),
        "wanted/1 should be demandable"
    );
    assert!(
        compiler.demand(Job::PlanEntryDispatch(other_id)),
        "other/1 should be demandable"
    );
    assert_resolved(compiler.drive(), "initial entry dispatch planning should resolve");

    let _ = outputs
        .take(Job::ReifyGuardDispatch(positive_id))
        .expect("initial helper reification should run");
    let _ = outputs
        .take(Job::PlanEntryDispatch(wanted_id))
        .expect("initial wanted/1 entry dispatch should run");
    let _ = outputs
        .take(Job::PlanEntryDispatch(other_id))
        .expect("initial other/1 entry dispatch should run");
    let other_plan_stops_before = outputs
        .stops_matching(|job| matches!(job, Job::PlanEntryDispatch(id) if *id == other_id))
        .len();
    let helper_stops_before = outputs
        .stops_matching(|job| matches!(job, Job::ReifyGuardDispatch(id) if *id == positive_id))
        .len();
    let wanted_plan_stops_before = outputs
        .stops_matching(|job| matches!(job, Job::PlanEntryDispatch(id) if *id == wanted_id))
        .len();
    let positive_dispatch_before = latest_guard_dispatch(&guard_defs, positive_id);
    let wanted_plan_before = latest_entry_dispatch(&entry_defs, wanted_id);
    let other_plan_before = latest_entry_dispatch(&entry_defs, other_id);

    let _code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_blast_radius_v2.fz".to_string()),
        text: include_str!("../../fixtures2/00029_positive_gte.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "late helper redefinition should auto-scope and rerun only the helper and dependent entry-dispatch plan",
    );

    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::ReifyGuardDispatch(id) if *id == positive_id))
            .len()
            > helper_stops_before,
        "helper reification should rerun after helper redefinition",
    );
    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::PlanEntryDispatch(id) if *id == wanted_id))
            .len()
            > wanted_plan_stops_before,
        "dependent wanted/1 entry dispatch should rerun after helper redefinition",
    );
    assert_ne!(
        latest_guard_dispatch(&guard_defs, positive_id),
        positive_dispatch_before,
        "helper redefinition should change the reified helper dispatch artifact itself",
    );
    assert_ne!(
        latest_entry_dispatch(&entry_defs, wanted_id),
        wanted_plan_before,
        "helper redefinition should change only the dependent entry-dispatch plan",
    );
    assert_eq!(
        latest_entry_dispatch(&entry_defs, other_id),
        other_plan_before,
        "independent other/1 entry dispatch should remain byte-for-byte unchanged",
    );
    assert_eq!(
        outputs
            .stops_matching(|job| matches!(job, Job::PlanEntryDispatch(id) if *id == other_id))
            .len(),
        other_plan_stops_before,
        "independent other/1 entry dispatch should stay cold across helper redefinition",
    );
}

#[test]
fn compiler2_scope_code_discovers_nested_modules_through_definition_macros() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/nested_modules.fz".to_string()),
        text: include_str!("../../fixtures2/00044_nested_modules.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should only index the raw source");
    let indexed_outputs = outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects");
    assert_eq!(
        indexed_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleIndexed(_)))
            .count(),
        3,
        "raw source indexing should discover each nested scope-shaping module definition once",
    );

    let indexed_stop = outputs.stop(Job::IndexCode(code_id));
    assert!(indexed_stop.effects_present, "indexing job should finish with effects");

    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for nested modules"
    );
    assert_resolved(
        compiler.drive(),
        "second drive should expand root definition macros and discover nested modules from compiler fragments",
    );

    let scoped_outputs = outputs.take(Job::ScopeCode(code_id)).expect("ScopeCode job effects");
    assert_eq!(
        module_indexed_ids(&scoped_outputs).len(),
        3,
        "root scope should revisit each nested module fragment after definition-macro expansion",
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "module", "defined"]),
        0,
        "root definition should not eagerly define nested modules"
    );
    assert!(
        functions
            .all()
            .into_iter()
            .filter(|record| record.function_ref.name != "__info__")
            .all(|record| record.function_ref.name != "func"),
        "root definition should not eagerly define the nested user function",
    );

    compiler.submit_root(RootSubmission {
        module_name: Some("X.Y.Z".to_string()),
        name: "func".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "demanding a nested runtime entry should walk the parent chain and index nested modules from compiler-defined fragments",
    );

    let mut defined_modules = modules.defined_names();
    defined_modules.sort();
    assert_eq!(
        defined_modules,
        vec!["X", "X.Y", "X.Y.Z"],
        "module.defined should emit one event per nested module"
    );

    let function_defined = functions
        .all()
        .into_iter()
        .find(|record| record.function_ref.name == "func")
        .expect("nested function.defined event");
    assert_eq!(
        function_module_name(&function_defined, &modules),
        "X.Y.Z",
        "nested function should be attributed to its fully-qualified module"
    );
    assert_eq!(
        function_fq_name(&function_defined, &modules),
        "X.Y.Z.func",
        "nested function should publish its fully-qualified function name"
    );
    assert_eq!(function_defined.arity, 0, "nested function arity should be preserved");
    assert!(
        capture
            .find(&["fz", "compiler2", "module", "defined"])
            .into_iter()
            .all(|event| event.metadata.len() == 0),
        "generic capture should not durable-copy synthesized module definition metadata"
    );

    assert_eq!(
        scoped_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleIndexed(_)))
            .count(),
        3,
        "scope-time discovery should surface one module-indexed fact per nested compiler-defined fragment"
    );
    assert_eq!(
        scoped_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::FunctionDefined(_)))
            .count(),
        0,
        "scope-time discovery should not define functions directly"
    );
    assert_eq!(
        scoped_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleDefined(_)))
            .count(),
        0,
        "scope-time discovery should not define modules directly"
    );
}

#[test]
fn compiler2_import_only_keeps_provider_lazy_until_a_body_needs_it() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only.fz".to_string()),
        text: include_str!("../../fixtures2/00045_import_only.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-only scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
    let user_module = named_module_id(compiler.world(), &module_ids, "User");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-only scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-only modules");
    assert_eq!(
        functions
            .all()
            .into_iter()
            .filter(|record| module_ids.contains(&record.module_id))
            .count(),
        0,
        "root definition should not eagerly define project modules before their bodies are demanded"
    );
    assert!(
        compiler.demand(Job::DefineModule(user_module)),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should define the consumer module without forcing the provider interface",
    );
    let mut names = functions
        .all()
        .into_iter()
        .filter(|record| module_ids.contains(&record.module_id))
        .filter(|record| record.function_ref.name != "__info__")
        .map(|record| (function_fq_name(&record, &modules), record.arity))
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        vec![("User.run".to_string(), 0)],
        "exact import-only publication should keep the provider lazy until a caller actually needs it: {names:?}"
    );

    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "rooting User.run should pull Math once the imported callable is actually needed",
    );
    let mut names = functions
        .all()
        .into_iter()
        .filter(|record| module_ids.contains(&record.module_id))
        .filter(|record| record.function_ref.name != "__info__")
        .map(|record| (function_fq_name(&record, &modules), record.arity))
        .collect::<Vec<_>>();
    names.sort();
    assert!(
        names.contains(&("Math.add".to_string(), 1))
            && names.contains(&("Math.add".to_string(), 2))
            && names.contains(&("User.run".to_string(), 0)),
        "root demand should keep the exact imported callable lazy until use, then resolve it without guessing: {names:?}"
    );
}

#[test]
fn compiler2_imported_macro_expands_in_provider_definition_namespace() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/cross_module_macro.fz".to_string()),
        text: r#"
defmodule Helpers do
  fn double(x), do: x * 2

  defmacro twice(x) do
    quote do: double(unquote(x))
  end
end

defmodule App do
  import Helpers, only: [twice: 1]

  fn run(), do: twice(21)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("App".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "imported macro expansion should settle through provider surface and executable facts",
    );

    let records = functions.all();
    let run = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "App.run")
        .expect("App.run/0 should be defined")
        .function_id;
    let double = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "Helpers.double")
        .expect("Helpers.double/1 should be defined")
        .function_id;
    direct_call_in_body(lowered_body(&bodies, run), double);
}

#[test]
fn compiler2_require_except_selects_remote_macro_set() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/require_except_remote_macro.fz".to_string()),
        text: r#"
defmodule Helpers do
  fn double(x), do: x * 2
  fn triple(x), do: x * 3

  defmacro twice(x) do
    quote do: double(unquote(x))
  end

  defmacro thrice(x) do
    quote do: triple(unquote(x))
  end
end

defmodule App do
  require Helpers, except: [twice: 1]

  fn run(), do: Helpers.thrice(14)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("App".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "require except should make only the remaining remote macros available",
    );

    let records = functions.all();
    let run = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "App.run")
        .expect("App.run/0 should be defined")
        .function_id;
    let triple = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "Helpers.triple")
        .expect("Helpers.triple/1 should be defined")
        .function_id;
    direct_call_in_body(lowered_body(&bodies, run), triple);
}

#[test]
fn compiler2_cross_file_bare_require_permits_qualified_macro_call() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/cross_file_macro_provider.fz".to_string()),
        text: r#"
defmodule M do
  fn tag(x), do: {:tagged, x}

  defmacro tagged(x) do
    quote do: tag(unquote(x))
  end
end
"#
        .to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/cross_file_macro_user.fz".to_string()),
        text: r#"
defmodule User do
  require M

  fn run(), do: M.tagged(7)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "bare require should bind module visibility for a qualified macro call across files",
    );

    let records = functions.all();
    let run = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "User.run")
        .expect("User.run/0 should be defined")
        .function_id;
    let tag = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "M.tag")
        .expect("M.tag/1 should be defined")
        .function_id;
    direct_call_in_body(lowered_body(&bodies, run), tag);
}

#[test]
fn compiler2_visible_alias_does_not_permit_remote_macro_without_require() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/aliased_macro_provider.fz".to_string()),
        text: r#"
defmodule Helpers do
  fn double(x), do: x * 2

  defmacro twice(x) do
    quote do: double(unquote(x))
  end
end
"#
        .to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/aliased_macro_user_without_require.fz".to_string()),
        text: r#"
defmodule App do
  alias Helpers, as: H

  fn run(), do: H.twice(21)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("App".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Fatal { .. }),
        "a visible module alias should not bypass the remote macro require guard: {outcome:?}",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("unrequired aliased remote macro diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::MACRO_NOT_REQUIRED.0,
        "aliased remote macros should still require an explicit require",
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("require H"),
        "diagnostic should name the visible qualifier that needs require; got: {}",
        metadata_str(&diagnostic, "message"),
    );
}

#[test]
fn compiler2_dotted_require_permits_full_path_macro_call() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/dotted_macro_provider.fz".to_string()),
        text: r#"
defmodule Foo.Bar do
  fn tag(x), do: {:tagged, x}

  defmacro tagged(x) do
    quote do: tag(unquote(x))
  end
end
"#
        .to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/dotted_macro_user.fz".to_string()),
        text: r#"
defmodule User do
  require Foo.Bar

  fn run(), do: Foo.Bar.tagged(7)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "dotted require should make the full required module path visible to qualified macro expansion",
    );

    let records = functions.all();
    let run = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "User.run")
        .expect("User.run/0 should be defined")
        .function_id;
    let tag = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "Foo.Bar.tag")
        .expect("Foo.Bar.tag/1 should be defined")
        .function_id;
    direct_call_in_body(lowered_body(&bodies, run), tag);
}

#[test]
fn compiler2_dotted_require_does_not_bind_short_alias() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/dotted_macro_provider.fz".to_string()),
        text: r#"
defmodule Foo.Bar do
  fn tag(x), do: {:tagged, x}

  defmacro tagged(x) do
    quote do: tag(unquote(x))
  end
end
"#
        .to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/dotted_macro_user_without_alias.fz".to_string()),
        text: r#"
defmodule User do
  require Foo.Bar

  fn run(), do: Bar.tagged(7)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Fatal { .. }),
        "dotted require should not create the short Bar alias: {outcome:?}",
    );
    assert!(
        capture
            .find(&["fz", "compiler2", "macro", "expanded"])
            .into_iter()
            .all(|event| {
                event
                    .metadata
                    .get("function_ref")
                    .and_then(|value| value.downcast_ref::<FunctionRef>())
                    .is_none_or(|function_ref| function_ref.name != "tagged")
            }),
        "the short alias form should not expand the remote macro",
    );
}

#[test]
fn compiler2_remote_macro_requires_explicit_require() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/remote_macro_without_require.fz".to_string()),
        text: r#"
defmodule Helpers do
  fn double(x), do: x * 2

  defmacro twice(x) do
    quote do: double(unquote(x))
  end
end

defmodule App do
  fn run(), do: Helpers.twice(21)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("App".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Fatal { .. }),
        "unrequired remote macro call should fail during source production: {outcome:?}",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("unrequired remote macro diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::MACRO_NOT_REQUIRED.0,
        "unrequired remote macros should be rejected at source expansion",
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("require Helpers"),
        "diagnostic should explain the missing require; got: {}",
        metadata_str(&diagnostic, "message"),
    );
    assert!(
        capture
            .find(&["fz", "compiler2", "macro", "expanded"])
            .into_iter()
            .all(|event| {
                event
                    .metadata
                    .get("function_ref")
                    .and_then(|value| value.downcast_ref::<FunctionRef>())
                    .is_none_or(|function_ref| function_ref.name != "twice")
            }),
        "remote macros must not expand unless the current source scope required them",
    );
}

#[test]
fn compiler2_require_remote_macro_waits_executable_and_expands() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);
    let bodies = LoweredBodyCapture::new();
    bodies.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/require_remote_macro.fz".to_string()),
        text: r#"
defmodule Helpers do
  fn double(x), do: x * 2

  defmacro twice(x) do
    quote do: double(unquote(x))
  end
end

defmodule App do
  require Helpers, only: [twice: 1]

  fn run(), do: Helpers.twice(21)
end
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("App".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "required remote macro expansion should settle through provider surface and executable facts",
    );

    let records = functions.all();
    let run = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "App.run")
        .expect("App.run/0 should be defined")
        .function_id;
    let double = records
        .iter()
        .find(|record| function_fq_name(record, &modules) == "Helpers.double")
        .expect("Helpers.double/1 should be defined")
        .function_id;
    direct_call_in_body(lowered_body(&bodies, run), double);
}

#[test]
fn compiler2_import_only_missing_target_stays_lazy_until_interface_settlement() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only_unknown.fz".to_string()),
        text: include_str!("../../fixtures2/00046_import_only_unknown.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-only unknown scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
    let user_module = named_module_id(compiler.world(), &module_ids, "User");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-only unknown scope"
    );
    assert_resolved(
        compiler.drive(),
        "second drive should scope import-only unknown modules",
    );
    assert!(
        compiler.demand(Job::DefineModule(user_module)),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(
        compiler.drive(),
        "missing exact import should stay latent until some later job actually settles the provider interface",
    );
    assert!(
        !capture.contains(&["fz", "diag", "error"]),
        "exact import expectations should defer missing-export diagnostics until interface settlement",
    );
}

#[test]
fn compiler2_import_all_waits_for_module_interface() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_all.fz".to_string()),
        text: include_str!("../../fixtures2/00047_import_all.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-all scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
    let user_module = named_module_id(compiler.world(), &module_ids, "User");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-all scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-all modules");
    assert!(
        compiler.demand(Job::DefineModule(user_module)),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should publish the provider interface before retrying User",
    );
    assert!(
        outputs
            .stops_matching(|job| *job == Job::DefineModule(user_module))
            .into_iter()
            .any(|stop| {
                stop.effects.as_ref().is_some_and(|effects| {
                    effects
                        .waits
                        .iter()
                        .any(|fact| matches!(fact, FactUse::Current(FactKey::ModuleInterface(_))))
                })
            }),
        "import-all should wait on provider interface visibility, not provider definition",
    );
    let mut names = functions
        .all()
        .into_iter()
        .filter(|record| module_ids.contains(&record.module_id))
        .filter(|record| record.function_ref.name != "__info__")
        .map(|record| (function_fq_name(&record, &modules), record.arity))
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        vec![
            ("Math.add".to_string(), 1),
            ("Math.add".to_string(), 2),
            ("User.run".to_string(), 0),
        ],
        "import-all indexing should keep the imported module surface and the consumer function intact"
    );
}

#[test]
fn compiler2_import_except_waits_for_module_interface() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let outputs = OutputCapture::new();
    outputs.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let modules = ModuleCapture::new();
    modules.install(&tel);

    let mut compiler = Compiler2::new(tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_except.fz".to_string()),
        text: include_str!("../../fixtures2/00048_import_except.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-except scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
    let user_module = named_module_id(compiler.world(), &module_ids, "User");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-except scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-except modules");
    assert!(
        compiler.demand(Job::DefineModule(user_module)),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should publish the provider interface before retrying User",
    );
    assert!(
        outputs
            .stops_matching(|job| *job == Job::DefineModule(user_module))
            .into_iter()
            .any(|stop| {
                stop.effects.as_ref().is_some_and(|effects| {
                    effects
                        .waits
                        .iter()
                        .any(|fact| matches!(fact, FactUse::Current(FactKey::ModuleInterface(_))))
                })
            }),
        "import-except should wait on provider interface visibility, not provider definition",
    );
    let mut names = functions
        .all()
        .into_iter()
        .filter(|record| module_ids.contains(&record.module_id))
        .filter(|record| record.function_ref.name != "__info__")
        .map(|record| (function_fq_name(&record, &modules), record.arity))
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        vec![
            ("Math.add".to_string(), 1),
            ("Math.add".to_string(), 2),
            ("Math.sub".to_string(), 2),
            ("User.run".to_string(), 0),
        ],
        "import-except indexing should still define the provider surface and the consumer"
    );
}

struct OutputCapture {
    outputs: JobOutputMap,
    stops: Rc<RefCell<Vec<JobSpanStop>>>,
}

struct WorkGraphCapture {
    steps: AppliedSteps,
}

#[derive(Debug, Clone)]
struct JobSpanStop {
    job: Job,
    effects_present: bool,
    effects: Option<JobEffects>,
}

#[derive(Debug, Clone)]
struct FunctionDefinedRecord {
    function_id: FunctionId,
    module_id: ModuleId,
    arity: u64,
    clauses: u64,
    owner_function_id: Option<FunctionId>,
    function_ref: FunctionRef,
}

#[derive(Debug, Clone)]
pub(crate) struct CallsiteDefinedRecord {
    pub(crate) key: CallSiteKey,
    pub(crate) summary: CallSiteSummary,
}

#[derive(Debug, Clone)]
struct BackendProgramRecord {
    root_id: crate::compiler2::RootId,
    changed: bool,
    program: Rc<BackendProgram>,
}

#[derive(Debug, Clone)]
struct NativeProgramRecord {
    root_id: crate::compiler2::RootId,
    program: Rc<NativeProgram>,
}

#[derive(Debug, Clone)]
pub(crate) struct ReturnTypeRecord {
    activation: ActivationKey,
    pub(crate) return_ty: Ty,
}

#[derive(Debug, Clone)]
struct ActivationInputRecord {
    activation: ActivationKey,
    inputs: Vec<Ty>,
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

struct ActivationInputCapture {
    defs: ActivationInputDefs,
}

struct BackendProgramCapture {
    defs: BackendProgramDefs,
}

struct NativeProgramCapture {
    defs: NativeProgramDefs,
}

struct ReusableConsCapture {
    counts: ReusableConsCounts,
}

impl ReusableConsCapture {
    fn new() -> Self {
        Self {
            counts: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let counts = Rc::clone(&self.counts);
        telemetry.attach_raw_event2::<crate::compiler2::RootId, BackendProgram, _>(
            &["fz", "compiler2", "native_program", "reusable_cons"],
            move |_, _, _, root, program| {
                let (birth_count, transport_count) = reusable_cons_counts(program);
                counts.borrow_mut().push((*root, birth_count, transport_count));
            },
        );
    }

    fn last(&self) -> Option<(crate::compiler2::RootId, u64, u64)> {
        self.counts.borrow().last().copied()
    }
}

struct EntryDispatchCapture {
    plans: EntryDispatchMap,
}

struct GuardDispatchCapture {
    dispatches: GuardDispatchMap,
}

struct LoweredBodyCapture {
    bodies: LoweredBodyDefs,
}

impl OutputCapture {
    fn new() -> Self {
        Self {
            outputs: Rc::new(RefCell::new(HashMap::new())),
            stops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
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

    fn take(&self, job: Job) -> Option<OutputFacts> {
        let mut outputs = self.outputs.borrow_mut();
        let matches = outputs.get_mut(&job)?;
        let output = matches.pop();
        if matches.is_empty() {
            outputs.remove(&job);
        }
        output
    }

    fn stop(&self, job: Job) -> JobSpanStop {
        self.stops
            .borrow()
            .iter()
            .rev()
            .find(|stop| stop.job == job)
            .cloned()
            .unwrap_or_else(|| panic!("job stop event for {job:?}"))
    }

    fn effects(&self, job: Job) -> JobEffects {
        self.stop(job.clone())
            .effects
            .unwrap_or_else(|| panic!("job effects for {job:?}"))
    }

    fn stops_matching(&self, mut matches: impl FnMut(&Job) -> bool) -> Vec<JobSpanStop> {
        self.stops
            .borrow()
            .iter()
            .filter(|stop| matches(&stop.job))
            .cloned()
            .collect()
    }
}

impl WorkGraphCapture {
    fn new() -> Self {
        Self {
            steps: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let steps = Rc::clone(&self.steps);
        telemetry.attach_raw_event2::<crate::compiler2::World, crate::compiler2::JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, _, completion| steps.borrow_mut().push(completion.step.clone()),
        );
    }

    fn all(&self) -> Vec<AppliedStep<Job, DependencyKey>> {
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
                    ["fz", "compiler2", "function", "source", "stashed"] => true,
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

    fn all(&self) -> Vec<FunctionDefinedRecord> {
        self.defs.borrow().values().cloned().collect()
    }

    fn id(&self, name: &str, arity: u64) -> FunctionId {
        self.defs
            .borrow()
            .values()
            .find(|record| record.function_ref.name == name && record.arity == arity)
            .map(|record| record.function_id)
            .unwrap_or_else(|| panic!("function fact for {name}/{arity}"))
    }
}

impl SourceNoteCapture {
    fn new() -> Self {
        Self::for_event(&["fz", "compiler2", "function", "source", "noted"])
    }

    fn for_event(event: &'static [&'static str]) -> Self {
        Self {
            notes: Rc::new(RefCell::new(Vec::new())),
            event,
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let event = self.event;
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

    fn count(&self, name: &str, arity: usize) -> usize {
        self.notes
            .borrow()
            .iter()
            .filter(|function_ref| function_ref.name == name && function_ref.arity == arity)
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
                defs.borrow_mut()
                    .entry(*module)
                    .or_default()
                    .push(world.module_state(*module));
            },
        );
    }

    fn qualified_name(&self, module_id: ModuleId) -> String {
        if module_id == ModuleId::GLOBAL {
            return "<top-level>".to_string();
        }
        let module = self
            .defs
            .borrow()
            .get(&module_id)
            .and_then(|defs| defs.last())
            .cloned()
            .unwrap_or_else(|| panic!("module.defined for {}", module_id.as_u32()));
        Self::qualified_name_from(module, self)
    }

    fn try_qualified_name(&self, module_id: ModuleId) -> Option<String> {
        if module_id == ModuleId::GLOBAL {
            return Some("<top-level>".to_string());
        }
        let module = self
            .defs
            .borrow()
            .get(&module_id)
            .and_then(|defs| defs.last())
            .cloned()?;
        Some(Self::qualified_name_from(module, self))
    }

    fn qualified_name_from(module: ModuleState, modules: &Self) -> String {
        match &module {
            crate::compiler2::ModuleState::Defined { source, .. }
            | crate::compiler2::ModuleState::Scoped { source, .. }
            | crate::compiler2::ModuleState::Indexed { source, .. } => {
                if source.parent == ModuleId::GLOBAL {
                    source.local_name.clone()
                } else {
                    format!("{}.{}", modules.qualified_name(source.parent), source.local_name)
                }
            }
            crate::compiler2::ModuleState::Placeholder { .. } => {
                panic!("defined module capture should not contain placeholders")
            }
        }
    }

    fn defined_names(&self) -> Vec<String> {
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
    fn settled_activations(&self, root_id: crate::compiler2::RootId) -> HashSet<ActivationKey> {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.activation.root == root_id)
            .map(|record| record.activation.clone())
            .collect()
    }
}

impl ActivationInputCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
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

    fn last_for_function(&self, root_id: crate::compiler2::RootId, function_id: FunctionId) -> ActivationInputRecord {
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
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
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

    fn last(&self, root_id: crate::compiler2::RootId) -> BackendProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("RootBackendProduct settlement for {root_id:?}"))
    }

    fn records(&self, root_id: crate::compiler2::RootId) -> Vec<BackendProgramRecord> {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.root_id == root_id)
            .cloned()
            .collect()
    }
}

impl NativeProgramCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
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

    fn last(&self, root_id: crate::compiler2::RootId) -> NativeProgramRecord {
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
    fn new() -> Self {
        Self {
            dispatches: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
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

    fn take(&self, function: FunctionId) -> Option<PatternGuardDispatch<Ty>> {
        let mut dispatches = self.dispatches.borrow_mut();
        let matches = dispatches.get_mut(&function)?;
        let dispatch = matches.pop();
        if matches.is_empty() {
            dispatches.remove(&function);
        }
        dispatch
    }

    fn last(&self, function: FunctionId) -> Option<PatternGuardDispatch<Ty>> {
        self.dispatches
            .borrow()
            .get(&function)
            .and_then(|matches| matches.last())
            .cloned()
    }
}

impl EntryDispatchCapture {
    fn new() -> Self {
        Self {
            plans: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
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

    fn take(&self, function: FunctionId) -> Option<PatternDispatchPlan<Ty>> {
        let mut plans = self.plans.borrow_mut();
        let matches = plans.get_mut(&function)?;
        let plan = matches.pop();
        if matches.is_empty() {
            plans.remove(&function);
        }
        plan
    }

    fn last(&self, function: FunctionId) -> Option<PatternDispatchPlan<Ty>> {
        self.plans
            .borrow()
            .get(&function)
            .and_then(|matches| matches.last())
            .cloned()
    }
}

impl LoweredBodyCapture {
    fn new() -> Self {
        Self {
            bodies: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let bodies = Rc::clone(&self.bodies);
        telemetry.attach_raw_event2::<crate::compiler2::World, FunctionId, _>(
            &["fz", "compiler2", "lowered_body", "defined"],
            move |_, _, _, world, function| {
                bodies
                    .borrow_mut()
                    .entry(*function)
                    .or_default()
                    .push(world.lowered_body(*function));
            },
        );
    }

    fn take(&self, function: FunctionId) -> Option<LoweredBody> {
        let mut bodies = self.bodies.borrow_mut();
        let matches = bodies.get_mut(&function)?;
        let body = matches.pop();
        if matches.is_empty() {
            bodies.remove(&function);
        }
        body
    }
}

struct SourceNoteCapture {
    notes: SourceNotes,
    // The source-publication event this capture observes. `noted` is the
    // body-pull signal; `stashed` is the eager per-code-fact interface signal
    // (fz-f98.14.5). Tests pick the tier whose intent they assert.
    event: &'static [&'static str],
}

fn reusable_cons_counts(program: &BackendProgram) -> (u64, u64) {
    let mut birth_count = 0_u64;
    let mut transport_count = 0_u64;
    for executable in program.executables() {
        let BackendBody::Clauses { clauses, entries, .. } = &executable.body else {
            continue;
        };
        for clause in clauses {
            birth_count += clause
                .projections
                .iter()
                .filter(|step| matches!(step, BackendStep::SplitList { .. }))
                .count() as u64;
        }
        for entry in entries {
            birth_count += entry
                .steps
                .iter()
                .filter(|step| matches!(step, BackendStep::SplitList { .. }))
                .count() as u64;
            transport_count += entry.reusable_cons_captures.len() as u64;
        }
    }
    (birth_count, transport_count)
}

fn record_function_definition(
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
            .pending_function_source(function_id)
            .and_then(|source| crate::compiler2::quoted_function::derive_function_surface(&source.source).ok())
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

fn metadata_str<'a>(event: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
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

fn assert_primary_span_contains(diagnostic: &Diagnostic, source: &str, needle: &str) {
    let span = diagnostic.primary.span;
    assert!(!span.is_dummy(), "diagnostic span must be a real source span");
    let source_slice = source
        .get(span.start as usize..span.end as usize)
        .unwrap_or_else(|| panic!("diagnostic span {span:?} should slice the submitted source"));
    assert!(
        source_slice.contains(needle),
        "diagnostic span should cover `{needle}`; got {span:?} -> `{source_slice}`"
    );
}

fn guard_dispatch(capture: &GuardDispatchCapture, function: FunctionId) -> PatternGuardDispatch<Ty> {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("guard_dispatch.defined for {function:?}"))
}

fn entry_dispatch(capture: &EntryDispatchCapture, function: FunctionId) -> PatternDispatchPlan<Ty> {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("entry_dispatch.defined for {function:?}"))
}

fn latest_guard_dispatch(capture: &GuardDispatchCapture, function: FunctionId) -> PatternGuardDispatch<Ty> {
    capture
        .last(function)
        .unwrap_or_else(|| panic!("guard_dispatch.defined for {function:?}"))
}

fn latest_entry_dispatch(capture: &EntryDispatchCapture, function: FunctionId) -> PatternDispatchPlan<Ty> {
    capture
        .last(function)
        .unwrap_or_else(|| panic!("entry_dispatch.defined for {function:?}"))
}

fn lowered_body(capture: &LoweredBodyCapture, function: FunctionId) -> LoweredBody {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("lowered_body.defined for {function:?}"))
}

fn summary_has_callee(summary: &CallSiteSummary, callee: SelectedCallee) -> bool {
    summary.targets.iter().any(|target| target.callee == callee)
}

fn summary_is_single_callee(summary: &CallSiteSummary, callee: SelectedCallee) -> bool {
    matches!(summary.single_target(), Some(target) if target.callee == callee)
}

fn local_call_target<T>(target: &CallTarget<T>) -> &T {
    match target {
        CallTarget::Local(target) => target,
        CallTarget::ProviderBoundary(function) => {
            panic!("expected local call target, got provider-boundary function {function:?}")
        }
    }
}

fn backend_executable(program: &BackendProgram, function: FunctionId) -> (usize, &crate::compiler2::BackendExecutable) {
    program
        .executables()
        .iter()
        .enumerate()
        .find(|(_, executable)| executable.key.activation.function == function)
        .map(|(index, executable)| (index, executable.as_ref()))
        .unwrap_or_else(|| panic!("backend executable for {function:?}"))
}

fn backend_direct_call(executable: &crate::compiler2::BackendExecutable, callee: FunctionId) -> &BackendTail {
    match &executable.body {
        crate::compiler2::BackendBody::Extern { .. } => panic!("expected clause body with a direct call"),
        crate::compiler2::BackendBody::Clauses { clauses, entries, .. } => {
            for clause in clauses {
                if let Some(found) = backend_direct_call_in_entry(entries, clause.entry, callee) {
                    return found;
                }
            }
            panic!("backend direct call to {callee:?} not found")
        }
    }
}

fn backend_direct_call_in_entry(
    entries: &[BackendEntry],
    entry_id: crate::compiler2::ControlEntryId,
    callee: FunctionId,
) -> Option<&BackendTail> {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        BackendTail::DirectCall {
            target: CallEdge::Direct(target),
            ..
        } if local_call_target(&target.callee).activation.function == callee => Some(&entry.tail),
        BackendTail::If {
            then_entry, else_entry, ..
        } => backend_direct_call_in_entry(entries, *then_entry, callee)
            .or_else(|| backend_direct_call_in_entry(entries, *else_entry, callee)),
        _ => None,
    }
}

/// The capture unpack is keyed on the CONSTRUCTIONS that mint the layout the
/// callee grounded on, not on the callee's function (fz-kdt.127, fz-kdt.157).
///
/// `same_lambda_two_capture_types_dynamic` mints ONE lambda through boundaries
/// that disagree about slot 0 -- a raw int in one, a raw float in the other --
/// and hands the value to `P.run/2` through a `case` no key can pin, so the
/// whole closure really does travel to a callee that wants its captures as
/// lanes. A prim keyed on the function would ask both boundaries how slot 0
/// was stored, get two answers, and refuse to compile. So the two halves below
/// are the invariant and its witness in one program.
///
/// The static twin carries the capture type in its forwarder KEY, so it lowers
/// no unpack at all and cannot witness this; that is
/// `compiler2_a_forwarded_lambdas_capture_layout_is_the_static_key`.
///
/// This is also fz-kdt.157's missing coverage. Its refusing half had no
/// program that could reach it, because a function minted at two capture
/// layouts compiled on no path; loosening the keying back to the function is
/// exactly what the first assertion detects.
#[test]
fn compiler2_a_capture_unpack_reads_the_constructions_that_minted_its_layout() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let mut compiler = Compiler2::new(tel);
    let fixture = "fixtures2/behavior/same_lambda_two_capture_types_dynamic.fz";
    compiler.submit_code(CodeSubmission {
        name: Some(fixture.to_string()),
        text: std::fs::read_to_string(fixture).unwrap_or_else(|error| panic!("read {fixture}: {error}")),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert!(
        matches!(compiler.drive(), DriveOutcome::Resolved),
        "native lowering of {fixture} must settle",
    );
    let program = native.last(root_id).program;

    let mut by_function: BTreeMap<u32, Vec<&crate::compiler2::artifact::NativeCallableBoundary>> = BTreeMap::new();
    for boundary in &program.callable_boundaries {
        let Some(shape) = boundary.shape.as_ref() else {
            continue;
        };
        by_function.entry(shape.target.0).or_default().push(boundary);
    }
    let split = by_function
        .values()
        .find(|boundaries| {
            let mut reprs = boundaries
                .iter()
                .map(|boundary| boundary.capture_reprs.first().copied());
            let Some(first) = reprs.next() else {
                return false;
            };
            reprs.any(|other| other != first)
        })
        .expect(
            "this fixture mints one lambda at an int capture and at a float capture, so some \
             function must have boundaries that disagree about slot 0",
        );
    assert!(
        split.len() >= 2,
        "a disagreement needs two boundaries: {:?}",
        split
            .iter()
            .map(|boundary| boundary.capture_reprs.clone())
            .collect::<Vec<_>>(),
    );

    let reprs_by_construction = program
        .callable_boundaries
        .iter()
        .map(|boundary| (boundary.identity_fn, boundary.capture_reprs.clone()))
        .collect::<HashMap<_, _>>();
    let mut unpacks = 0;
    for body in &program.bodies {
        for block in &program.module.fn_by_id(body.fn_id).blocks {
            for stmt in &block.stmts {
                let IrStmt::Let(
                    _,
                    IrPrim::ClosureCapture {
                        constructions, index, ..
                    },
                ) = stmt
                else {
                    continue;
                };
                unpacks += 1;
                assert!(
                    !constructions.is_empty(),
                    "a capture unpack that names no construction has no authority to read from",
                );
                let mut reprs = constructions.iter().map(|construction| {
                    reprs_by_construction
                        .get(construction)
                        .unwrap_or_else(|| panic!("construction {construction:?} mints no boundary"))
                        .get(*index as usize)
                        .copied()
                });
                let first = reprs.next().expect("a non-empty construction list has a first repr");
                assert!(
                    first.is_some() && reprs.all(|other| other == first),
                    "the constructions a capture unpack names must agree about the slot they \
                     minted, or there is no single answer to read: {constructions:?} slot {index}",
                );
            }
        }
    }
    assert!(
        unpacks > 0,
        "the forwarder hands a whole closure to a callee that wants its captures as lanes, so \
         this fixture must lower at least one capture unpack",
    );
}

fn native_function_contains_nil_const(program: &NativeProgram, fn_id: FnId) -> bool {
    program.module.fn_by_id(fn_id).blocks.iter().any(|block| {
        block
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, IrStmt::Let(_, IrPrim::Const(crate::fz_ir::Const::Nil))))
    })
}

fn return_flow_is_distinct_return_payload(flow: &BackendReturnFlow, caller: &BackendReturnLayout) -> bool {
    matches!(flow, BackendReturnFlow::Continue { source } if source.as_ref() != caller)
}

fn native_executable_functions(program: &NativeProgram) -> HashSet<FunctionId> {
    program
        .bodies
        .iter()
        .filter_map(|body| match &body.origin {
            NativeBodyOrigin::Executable(key) => Some(key.activation.function),
            NativeBodyOrigin::Clause { .. }
            | NativeBodyOrigin::Continuation { .. }
            | NativeBodyOrigin::CallableWrapper { .. } => None,
        })
        .collect()
}

fn native_executable_fn(program: &NativeProgram, function: FunctionId) -> crate::fz_ir::FnId {
    program
        .bodies
        .iter()
        .find_map(|body| match &body.origin {
            NativeBodyOrigin::Executable(key) if key.activation.function == function => Some(body.fn_id),
            NativeBodyOrigin::Executable(_)
            | NativeBodyOrigin::Clause { .. }
            | NativeBodyOrigin::Continuation { .. }
            | NativeBodyOrigin::CallableWrapper { .. } => None,
        })
        .unwrap_or_else(|| panic!("native executable fn for {function:?}"))
}

fn native_executable_body(program: &NativeProgram, function: FunctionId) -> &crate::compiler2::artifact::NativeBody {
    program
        .bodies
        .iter()
        .find(|body| matches!(&body.origin, NativeBodyOrigin::Executable(key) if key.activation.function == function))
        .unwrap_or_else(|| panic!("native executable body for {function:?}"))
}

/// Count of indirect closure-call terminators. A `CallClosure`/
/// `TailCallClosure` term IS the indirect form: exact calls lower as
/// `Call`/`TailCall` direct edges where the grounding decision is made.
fn native_closure_call_count(program: &NativeProgram) -> usize {
    program
        .module
        .fns
        .iter()
        .flat_map(|function| function.blocks.iter())
        .filter(|block| {
            matches!(
                block.terminator,
                IrTerm::CallClosure { .. } | IrTerm::TailCallClosure { .. }
            )
        })
        .count()
}

fn native_exact_call_targets(program: &NativeProgram) -> Vec<FnId> {
    let mut out = Vec::new();
    for function in &program.module.fns {
        for block in &function.blocks {
            match &block.terminator {
                IrTerm::Call { callee, .. } | IrTerm::TailCall { callee, .. } => {
                    if let crate::fz_ir::DirectCallTarget::Local(fn_id) = callee {
                        out.push(*fn_id);
                    }
                }
                _ => {}
            }
        }
    }
    out
}

fn native_callable_boundary_uses(program: &NativeProgram) -> HashSet<NativeCallableBoundaryId> {
    program
        .module
        .fns
        .iter()
        .flat_map(|function| function.blocks.iter())
        .flat_map(|block| block.stmts.iter())
        .filter_map(|stmt| match stmt {
            IrStmt::Let(_, IrPrim::MakeFnRef(_, identity_fn) | IrPrim::MakeClosure(_, identity_fn, _)) => program
                .callable_boundaries
                .iter()
                .find(|boundary| boundary.identity_fn == *identity_fn)
                .map(|boundary| boundary.id()),
            _ => None,
        })
        .collect()
}

fn sorted_extern_marshals(body: &crate::compiler2::artifact::NativeBody) -> Vec<ExternTy> {
    let mut marshals = body
        .extern_marshals
        .iter()
        .map(|(site, ty)| (site.arg_idx, *ty))
        .collect::<Vec<_>>();
    marshals.sort_by_key(|(arg_idx, _)| *arg_idx);
    marshals.into_iter().map(|(_, ty)| ty).collect()
}

fn direct_call_in_body(body: LoweredBody, callee: FunctionId) -> (CallSiteId, ValueId) {
    match body {
        LoweredBody::Extern { .. } => panic!("expected clause body with a direct call"),
        LoweredBody::Clauses { clauses, entries, .. } => {
            for clause in &clauses {
                if let Some(found) = direct_call_in_entry(&entries, clause.entry, callee) {
                    return found;
                }
            }
            let available = clauses
                .iter()
                .filter_map(|clause| direct_callee_in_entry(&entries, clause.entry))
                .collect::<Vec<_>>();
            panic!("direct call to {callee:?} not found in lowered body; saw {available:?}")
        }
    }
}

fn direct_call_in_entry(
    entries: &[crate::compiler2::LoweredEntry],
    entry_id: crate::compiler2::ControlEntryId,
    callee: FunctionId,
) -> Option<(CallSiteId, ValueId)> {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        crate::compiler2::LoweredTail::DirectCall {
            value,
            callsite,
            callee: function,
            ..
        } if *function == callee => Some((*callsite, *value)),
        crate::compiler2::LoweredTail::If {
            then_entry, else_entry, ..
        } => direct_call_in_entry(entries, *then_entry, callee)
            .or_else(|| direct_call_in_entry(entries, *else_entry, callee)),
        _ => None,
    }
}

fn direct_callee_in_entry(
    entries: &[crate::compiler2::LoweredEntry],
    entry_id: crate::compiler2::ControlEntryId,
) -> Option<FunctionId> {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        crate::compiler2::LoweredTail::DirectCall { callee: function, .. } => Some(*function),
        crate::compiler2::LoweredTail::If {
            then_entry, else_entry, ..
        } => direct_callee_in_entry(entries, *then_entry).or_else(|| direct_callee_in_entry(entries, *else_entry)),
        _ => None,
    }
}

fn plan_has_nested_guard_dispatch(plan: &PatternDispatchPlan<Ty>) -> bool {
    plan.guards.iter().any(expr_has_nested_dispatch)
}

fn plan_body_has_type_question(plan: &PatternDispatchPlan<Ty>, body_id: u32) -> bool {
    let outcome = plan
        .outcomes
        .iter()
        .find(|outcome| outcome.body_id == body_id)
        .unwrap_or_else(|| panic!("entry-dispatch outcome for body {body_id}"));
    let arm = plan
        .matrix
        .arms
        .iter()
        .find(|arm| arm.outcome == outcome.outcome)
        .unwrap_or_else(|| panic!("dispatch arm for body {body_id}"));
    arm.questions
        .iter()
        .any(|question| matches!(question.predicate.region, Region::Type(_)))
}

fn guard_dispatch_has_nested_dispatch(dispatch: &PatternGuardDispatch<Ty>) -> bool {
    dispatch.plan.guards.iter().any(expr_has_nested_dispatch) || dispatch.bodies.iter().any(expr_has_nested_dispatch)
}

fn expr_has_nested_dispatch(expr: &PatternGuardExpr<Ty>) -> bool {
    match expr {
        PatternGuardExpr::Dispatch { .. } => true,
        PatternGuardExpr::Unary { expr, .. } => expr_has_nested_dispatch(expr),
        PatternGuardExpr::Binary { lhs, rhs, .. } => expr_has_nested_dispatch(lhs) || expr_has_nested_dispatch(rhs),
        PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => false,
    }
}

fn guard_dispatch_has_binary_nested_input(dispatch: &PatternGuardDispatch<Ty>) -> bool {
    dispatch.bodies.iter().any(expr_has_binary_nested_input)
}

fn expr_has_binary_nested_input(expr: &PatternGuardExpr<Ty>) -> bool {
    match expr {
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            inputs
                .iter()
                .any(|input| matches!(input, PatternGuardExpr::Binary { .. }))
                || dispatch.bodies.iter().any(expr_has_binary_nested_input)
                || dispatch.plan.guards.iter().any(expr_has_binary_nested_input)
        }
        PatternGuardExpr::Unary { expr, .. } => expr_has_binary_nested_input(expr),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            expr_has_binary_nested_input(lhs) || expr_has_binary_nested_input(rhs)
        }
        PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => false,
    }
}

pub(crate) fn assert_resolved(outcome: DriveOutcome<Job, DependencyKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

pub(crate) fn function_id(capture: &FunctionCapture, name: &str, arity: u64) -> FunctionId {
    capture.id(name, arity)
}

/// Records every `ActivationKey` the semantic pass publishes through
/// `activation_analysis.defined`. A key can be republished across rounds (and,
/// before convergence, a transient key can appear); callers dedup by key and
/// filter to the live frontier via `world.activation_analysis` to recover the
/// settled analyzed-activation set.
struct ActivationAnalysisCapture {
    keys: Rc<RefCell<Vec<ActivationKey>>>,
}

impl ActivationAnalysisCapture {
    fn new() -> Self {
        Self {
            keys: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let keys = Rc::clone(&self.keys);
        telemetry.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
            &["fz", "compiler2", "activation_analysis", "defined"],
            move |_, _, _, _, activation| keys.borrow_mut().push(activation.clone()),
        );
    }

    fn keys_for_root(&self, root: crate::compiler2::RootId) -> Vec<ActivationKey> {
        self.keys
            .borrow()
            .iter()
            .filter(|key| key.root == root)
            .cloned()
            .collect()
    }
}

fn generated_functions_owned_by(capture: &FunctionCapture, owner: FunctionId) -> Vec<FunctionDefinedRecord> {
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
            record.function_ref.name == name
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

fn function_fq_name(function: &FunctionDefinedRecord, modules: &ModuleCapture) -> String {
    if function.module_id == ModuleId::GLOBAL {
        function.function_ref.name.clone()
    } else {
        format!(
            "{}.{}",
            modules.qualified_name(function.module_id),
            function.function_ref.name
        )
    }
}

fn function_module_name(function: &FunctionDefinedRecord, modules: &ModuleCapture) -> String {
    modules
        .try_qualified_name(function.module_id)
        .unwrap_or_else(|| format!("<module:{}>", function.module_id.as_u32()))
}

fn module_indexed_ids(outputs: &OutputFacts) -> Vec<crate::compiler2::ModuleId> {
    outputs
        .iter()
        .filter_map(|(fact, _)| match fact {
            FactKey::ModuleIndexed(module_id) => Some(*module_id),
            _ => None,
        })
        .collect()
}

fn named_module_id(world: &crate::compiler2::World, modules: &[ModuleId], name: &str) -> ModuleId {
    modules
        .iter()
        .copied()
        .find(|module| world.module_name(*module) == Some(name))
        .unwrap_or_else(|| panic!("indexed module `{name}`"))
}

fn sorted_strings(mut values: Vec<String>) -> Vec<String> {
    values.sort();
    values
}

#[test]
fn compiler2_recursive_first_round_reads_absence_not_the_empty_type() {
    // A self-recursive function's first analysis round reads its own
    // not-yet-published return. Absence must surface as a summary with NO
    // return evidence — never the empty type (which would prove the call
    // dead) and never an `any` placeholder (`any` is earned at boundaries).
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let callsites = CallsiteCapture::new();
    callsites.install(&tel);

    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("count.fz".to_string()),
        concat!(
            "fn count(0), do: 0\n",
            "fn count(n), do: count(n - 1)\n",
            "fn main(), do: count(3)\n",
        )
        .to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "the recursive count program should converge",
    );

    let count_id = function_id(&functions, "count", 1);
    let self_calls: Vec<_> = callsites
        .all()
        .into_iter()
        .filter(|record| record.key.activation.function == count_id)
        .filter(|record| {
            record
                .summary
                .targets
                .iter()
                .any(|target| target.callee == SelectedCallee::Function(count_id))
        })
        .collect();
    assert!(!self_calls.is_empty(), "the self-callsite should publish summaries");
    assert!(
        self_calls.last().expect("self calls").summary.return_ty.is_some(),
        "the ascent should land on real return evidence",
    );

    // Mid-ascent, not-yet-derived callee returns surface as ABSENT evidence
    // (return_ty None) — the honest snapshot the engine now records.
    assert!(
        callsites.all().iter().any(|record| record.summary.return_ty.is_none()),
        "some round must record absent return evidence",
    );

    // The two lies are gone. Every function in this program returns, so the
    // empty type may never appear as a return (the old absent-reads-as-none
    // lie), and there are no boundaries or dynamic callables, so `any` may
    // never appear either (the old wait-placeholder lie).
    let any = world.types_mut().any();
    for record in callsites.all() {
        for target in &record.summary.targets {
            if let Some(ty) = target.return_ty {
                assert!(
                    !world.types().is_empty(&ty),
                    "the empty type must never stand in for absent evidence: {:?}",
                    record.key,
                );
                assert!(
                    !world.types().is_equivalent(&ty, &any),
                    "no `any` placeholder may reach a summary: {:?}",
                    record.key,
                );
            }
        }
    }
}

#[test]
fn compiler2_never_returning_function_settles_with_empty_evidence() {
    // fn forever(), do: forever() — the least fixpoint of its return is
    // bottom. The drive must quiesce (absent evidence is the join identity,
    // so the activation stops waking itself), and the settled evidence stays
    // empty: at the fixpoint, "no evidence" IS the fact "never returns".
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut world = crate::compiler2::World::new();
    let mut sessions = super::pull::ProductSessions::default();
    world.submit_code(
        Some("forever.fz".to_string()),
        concat!("fn forever(), do: forever()\n", "fn main(), do: forever()\n").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    drive_world_backend_product(&mut world, &tel, &mut sessions, root);
    assert_resolved(
        super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        "a never-returning program still quiesces",
    );

    // The two reachable activations both have bottom returns: analysis reaches
    // them (main/0 calls forever/0, forever/0 calls itself) but neither ever
    // produces a value, so their settled return evidence stays absent — at the
    // fixpoint "no evidence" IS the fact "never returns".
    let main_id = function_id(&functions, "main", 0);
    let forever_id = function_id(&functions, "forever", 0);
    let main_activation = ActivationKey::from_inputs(root, main_id, &[], world.types_mut());
    let forever_activation = ActivationKey::from_inputs(root, forever_id, &[], world.types_mut());
    assert_eq!(
        world.activation_return(&main_activation),
        None,
        "settled evidence for the never-returning main/0 activation stays empty",
    );
    assert_eq!(
        world.activation_return(&forever_activation),
        None,
        "settled evidence for the never-returning forever/0 activation stays empty",
    );
}

#[test]
fn compiler2_unproductive_deepening_settles_at_bottom_without_widening() {
    // fn deep(x), do: [deep(x)] — the inner call must produce a value before
    // the list ever exists, so this function NEVER returns: its least
    // fixpoint is bottom. Under the old absent-reads-as-none lie this very
    // program manufactured a divergent ascent (list(none), list(list(none)),
    // …); honest paths never start the chain.
    let tel = ConfiguredTelemetry::new();
    let widened = Rc::new(Cell::new(false));
    let widened_sink = Rc::clone(&widened);
    tel.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
        &["fz", "compiler2", "return_type", "widened"],
        move |_, _, _, _, _| widened_sink.set(true),
    );
    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("deep_unproductive.fz".to_string()),
        concat!("fn deep(x), do: [deep(x)]\n", "fn main(), do: deep(1)\n").to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "an unproductive deepening program quiesces at bottom",
    );
    assert!(
        !widened.get(),
        "no evidence ever ascends, so widening must never engage",
    );
}

#[test]
fn compiler2_productive_deepening_terminates_by_widening() {
    // fn deep(0), do: []
    // fn deep(n), do: [deep(n - 1)]
    // Every round produces REAL evidence one list deeper — the true value is
    // the recursive type μt.([] | list(t)), which the lattice cannot
    // express, so the precise ascent provably never lands. Termination must
    // come from the widening operator, not from a timeout.
    let tel = ConfiguredTelemetry::new();
    let widened = Rc::new(Cell::new(false));
    let widened_sink = Rc::clone(&widened);
    tel.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
        &["fz", "compiler2", "return_type", "widened"],
        move |_, _, _, _, _| widened_sink.set(true),
    );
    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("deep_productive.fz".to_string()),
        concat!(
            "fn deep(0), do: []\n",
            "fn deep(n), do: [deep(n - 1)]\n",
            "fn main(), do: deep(3)\n",
        )
        .to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "the productive deepening program must converge",
    );
    assert!(
        widened.get(),
        "termination of a true divergent ascent must come from widening",
    );
}

#[test]
fn compiler2_quicksort_return_revisions_stay_bounded() {
    // THE runaway invariant (fz-rh2.21): in the oscillating engine, one
    // activation's ReturnType was re-defined 32,356 times and job counts hit
    // 54,000+. Under monotone joins every activation's return is defined a
    // small bounded number of times, on every schedule.
    let tel = ConfiguredTelemetry::new();
    #[derive(Default)]
    struct ReturnStats {
        define_calls: u64,
    }
    let defines: Rc<RefCell<HashMap<(u64, u64), ReturnStats>>> = Rc::new(RefCell::new(HashMap::new()));
    let sink = Rc::clone(&defines);
    tel.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
        &["fz", "compiler2", "return_type", "defined"],
        move |_, _, _, _, activation| {
            let mut defines = sink.borrow_mut();
            let entry = defines
                .entry((activation.root.as_u32() as u64, activation.function.as_u32() as u64))
                .or_default();
            entry.define_calls += 1;
        },
    );

    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("quicksort.fz".to_string()),
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "quicksort converges by theorem, on every schedule",
    );

    for ((root, function), stats) in defines.borrow().iter() {
        assert!(
            stats.define_calls <= 64,
            "fn {function} (root {root}) was re-analyzed {} times — the runaway re-ran one activation 32,366 times",
            stats.define_calls,
        );
    }
}

fn sweep_corpus_for_return_widening(shard: usize, shards: usize) {
    let mut swept = 0u32;
    let mut corpus_max_return_changes = 0u64;
    let mut entries = std::fs::read_dir("fixtures2")
        .expect("fixtures2 corpus")
        .map(|entry| entry.expect("corpus entry").path())
        .collect::<Vec<_>>();
    entries.sort();
    for (index, path) in entries.into_iter().enumerate() {
        if index % shards != shard {
            continue;
        }
        if path.extension().is_none_or(|ext| ext != "fz") {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("fixture source");
        if !text.contains("fn main()") {
            continue;
        }
        swept += 1;

        let tel = ConfiguredTelemetry::new();
        let widened = Rc::new(Cell::new(false));
        let widened_sink = Rc::clone(&widened);
        tel.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
            &["fz", "compiler2", "return_type", "widened"],
            move |_, _, _, _, _| widened_sink.set(true),
        );
        let return_changes: Rc<RefCell<HashMap<ActivationKey, u64>>> = Rc::new(RefCell::new(HashMap::new()));
        let sink = Rc::clone(&return_changes);
        tel.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
            &["fz", "compiler2", "return_type", "defined"],
            move |_, _, _, _, activation| {
                *sink.borrow_mut().entry(activation.clone()).or_default() += 1;
            },
        );

        let mut world = crate::compiler2::World::new();
        world.submit_code(Some(path.display().to_string()), text);
        world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
        // Diagnostics are fixture-specific; the corpus invariants are that
        // the drive terminates (it returned) and never widened a return.
        let _ = super::drive::ExecutionContext::new(&mut world, &tel).drive();
        assert!(
            !widened.get(),
            "return widening engaged on corpus fixture {}",
            path.display(),
        );
        let fixture_max_return_changes = return_changes.borrow().values().copied().max().unwrap_or_default();
        corpus_max_return_changes = corpus_max_return_changes.max(fixture_max_return_changes);
    }
    assert!(
        swept >= 25,
        "corpus shard {shard}/{shards} swept only {swept} fixtures — wrong path?"
    );
    assert!(
        corpus_max_return_changes <= 5,
        "corpus max return changes grew to {corpus_max_return_changes} — \
         re-derive RETURN_WIDENING_BUDGET's headroom before loosening this",
    );
}

#[test]
fn compiler2_corpus_never_engages_return_widening_shard_0() {
    sweep_corpus_for_return_widening(0, 4);
}

#[test]
fn compiler2_corpus_never_engages_return_widening_shard_1() {
    sweep_corpus_for_return_widening(1, 4);
}

#[test]
fn compiler2_corpus_never_engages_return_widening_shard_2() {
    sweep_corpus_for_return_widening(2, 4);
}

#[test]
fn compiler2_corpus_never_engages_return_widening_shard_3() {
    sweep_corpus_for_return_widening(3, 4);
}

#[test]
fn compiler2_quicksort_converges_identically_on_every_schedule() {
    // The runaway was bimodal: per-process hash seeds picked the wake order,
    // and one order in a handful locked the engine into a period-2
    // oscillation. Monotone joins make the least fixpoint unique and the
    // schedule irrelevant: twenty fresh drives that each pull the whole
    // backend product must do identical, bounded work AND settle the exact
    // same activation frontier. If this test ever flakes, the design has a
    // hole and the flake has found it — do not loosen it. The frontier is the
    // rooted, reachability-pruned settled call graph (see
    // `rooted_reachable_frontier`), and the same derivation
    // `compiler2_quicksort_root_closes_with_a_finite_recursive_frontier` pins to
    // its exact size.
    let mut shapes = Vec::new();
    for _ in 0..20 {
        let tel = ConfiguredTelemetry::new();
        let jobs_ran: Rc<RefCell<u64>> = Rc::new(RefCell::new(0));
        let sink = Rc::clone(&jobs_ran);
        tel.attach(
            &["fz", "compiler2", "job"],
            Box::new(move |event: &Event<'_, '_, '_>| {
                if event.kind == EventKind::SpanStart {
                    *sink.borrow_mut() += 1;
                }
            }),
        );

        let mut world = crate::compiler2::World::new();
        let mut sessions = super::pull::ProductSessions::default();
        world.submit_code(
            Some("quicksort.fz".to_string()),
            include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
        );
        let root = world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
        drive_world_backend_product(&mut world, &tel, &mut sessions, root);
        assert_resolved(
            super::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
            "every schedule converges",
        );
        let entry = world.root_function(root);
        let frontier = rooted_reachable_frontier(&mut world, root, entry);
        let normalized = frontier
            .iter()
            .map(|activation| {
                (
                    world.function_ref(activation.function).name.clone(),
                    activation
                        .inputs(world.types())
                        .iter()
                        .map(|ty| world.types().display(ty))
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<BTreeSet<_>>();
        let names = normalized.iter().map(|(name, _)| name.as_str()).collect::<HashSet<_>>();
        assert!(
            names.contains("main")
                && names.contains("qsort")
                && names.contains("partition")
                && names.contains("append")
        );
        assert!(!names.contains("foo"));
        assert!(
            frontier.len() <= 17,
            "quicksort frontier exceeded the proven bound: {frontier:?}"
        );
        shapes.push((*jobs_ran.borrow(), normalized));
    }
    let expected = &shapes[0].1;
    assert!(
        shapes.iter().all(|(_, frontier)| frontier == expected),
        "all schedules must settle the same activation frontier: {shapes:?}",
    );
    let min_jobs = shapes.iter().map(|(jobs, _)| *jobs).min().expect("runs");
    let max_jobs = shapes.iter().map(|(jobs, _)| *jobs).max().expect("runs");
    assert!(
        max_jobs <= min_jobs + min_jobs / 10 && max_jobs < 1000,
        "work must stay in a tight band across schedules: {shapes:?}",
    );
}

#[test]
fn compiler2_resolved_drive_is_quiescent() {
    // After Resolved, the fixpoint is a fixpoint: re-driving with no new
    // submissions runs zero jobs. Self-wake loops (the runaway's engine)
    // would fail this immediately.
    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("quicksort.fz".to_string()),
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "first drive settles",
    );

    let jobs_ran: Rc<RefCell<u64>> = Rc::new(RefCell::new(0));
    let sink = Rc::clone(&jobs_ran);
    tel.attach(
        &["fz", "compiler2", "job"],
        Box::new(move |event: &Event<'_, '_, '_>| {
            if event.kind == EventKind::SpanStart {
                *sink.borrow_mut() += 1;
            }
        }),
    );
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "a settled world re-drives to Resolved",
    );
    assert_eq!(*jobs_ran.borrow(), 0, "a settled world has nothing to do");
}

#[test]
#[ignore = "manual end-to-end smoke: shells the release fz2 binary 20x; run when touching the fact engine"]
fn compiler2_quicksort_cli_builds_are_stable_smoke() {
    // The original symptom: the same build command produced 2.5MB telemetry
    // logs or 700MB runaways, decided by the process hash seed. Twenty
    // builds must produce small logs of identical event counts.
    let binary = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/release/fz2");
    assert!(
        binary.exists(),
        "build the release binary first: cargo build --release --bin fz2",
    );
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures2/behavior/quicksort.fz");
    let mut line_counts = Vec::new();
    for run in 0..20 {
        let dir = std::env::temp_dir().join(format!("fz2-smoke-{run}"));
        let _ = std::fs::create_dir_all(&dir);
        let log = dir.join("telemetry.jsonl");
        let out = dir.join("out");
        let status = std::process::Command::new(&binary)
            .arg("build")
            .arg("-o")
            .arg(&out)
            .arg("--log-telemetry")
            .arg(&log)
            .arg(&fixture)
            .status()
            .expect("fz2 build should run");
        assert!(status.success(), "fz2 build should succeed on run {run}");
        let bytes = std::fs::metadata(&log).expect("telemetry log").len();
        assert!(
            bytes < 8 * 1024 * 1024,
            "telemetry log must stay in the megabytes on run {run}: {bytes} bytes",
        );
        let lines = std::fs::read_to_string(&log).expect("log").lines().count();
        line_counts.push(lines);
        let _ = std::fs::remove_dir_all(&dir);
    }
    let min = line_counts.iter().min().expect("runs");
    let max = line_counts.iter().max().expect("runs");
    assert!(
        max <= &(min + min / 10),
        "event counts must stay in a tight band: {line_counts:?}",
    );
}

#[test]
fn compiler2_string_constant_dispatch_keeps_the_miss_arm_reachable() {
    // String literals have no singleton types (GroundValue::Binary types as
    // str_t), so no subtype check can ever witness "the scrutinee always
    // equals this string". The old miss-side proof !is_subtype(str, str)
    // evaluated false and silently pruned the live wildcard clause — the
    // value test happens at RUNTIME, so the statically pruned body was
    // simply gone. Both clauses must stay reachable.
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    type ReachableByFunction = Vec<(u64, Vec<u32>)>;
    let analyses: Rc<RefCell<ReachableByFunction>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&analyses);
    tel.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
        &["fz", "compiler2", "activation_analysis", "defined"],
        move |_, _, _, world, activation| {
            let Some(analysis) = world.activation_analysis(activation) else {
                return;
            };
            sink.borrow_mut().push((
                activation.function.as_u32() as u64,
                analysis.entry_reachability.clauses().to_vec(),
            ));
        },
    );

    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("string_dispatch.fz".to_string()),
        concat!(
            "fn pick(\"a\"), do: 1\n",
            "fn pick(_), do: 2\n",
            "fn main(), do: pick(\"b\")\n",
        )
        .to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "string-constant dispatch should settle",
    );

    let pick_id = function_id(&functions, "pick", 1).as_u32() as u64;
    let last = analyses
        .borrow()
        .iter()
        .rev()
        .find(|(function, _)| *function == pick_id)
        .map(|(_, clauses)| clauses.clone())
        .expect("pick/1 should be analyzed");
    assert_eq!(
        last,
        vec![0, 1],
        "a string constant cannot prove its miss edge dead; the wildcard clause must stay reachable",
    );
}

/// Reachability is a SET — clauses union across the correlated input rows an
/// activation collects — so which row arrived first is schedule, not meaning.
/// Here the schedule is upside down on purpose: the outer call supplies a
/// non-empty list, so the cons clause is reached first, and the base clause
/// only once the recursion has widened its way down to `[]`. The published
/// fact must still name the clauses by their own identity, source order, or
/// every artifact built from it moves whenever the key population changes.
#[test]
fn compiler2_entry_reachability_names_clauses_in_source_order_not_arrival_order() {
    let reachable = reachable_clauses_for_source(
        "arrival_order_reachability.fz",
        r#"
fn count([], acc), do: acc
fn count([_head | tail], acc), do: count(tail, acc + 1)

fn main(), do: count([1, 2, 3], 0)
"#,
        "count",
        2,
    );
    assert_eq!(
        reachable,
        vec![0, 1],
        "both clauses are reachable; the base clause is written first and must be named first, \
         however late its row arrived",
    );
}

#[test]
fn compiler2_dispatch_reachability_preserves_correlated_tuple_inputs() {
    let (direct, direct_return) = semantic_reachability_for_source(
        "correlated_tuple_dispatch.fz",
        r#"
fn choose() do
  if true, do: {:a, :x}, else: {:b, :y}
end

fn classify({:a, :x}), do: :left
fn classify({:b, :y}), do: :right
fn classify(_), do: :fallback

fn main(), do: classify(choose())
"#,
        "classify",
        1,
    );
    assert_eq!(
        direct,
        vec![0, 1],
        "the exact tuple alternatives must not invent cross-wired or wildcard reachability",
    );
    assert!(
        direct_return.contains(":left") && direct_return.contains(":right") && !direct_return.contains(":fallback"),
        "the published classifier return must exclude the phantom fallback, got {direct_return}",
    );

    let projected = reachable_clauses_for_source(
        "projected_tuple_dispatch.fz",
        r#"
fn choose() do
  if true, do: {:a, [true]}, else: {:b, [false]}
end

fn classify({:a, [true | _tail]}), do: :left
fn classify({:b, [false | _tail]}), do: :right
fn classify(_), do: :fallback

fn main(), do: classify(choose())
"#,
        "classify",
        1,
    );
    assert_eq!(
        projected,
        vec![0, 1],
        "tuple alternatives must stay correlated through list-head projections",
    );

    let nested = reachable_clauses_for_source(
        "nested_tuple_dispatch.fz",
        r#"
fn choose() do
  if true, do: {:outer, {:a, :x}}, else: {:outer, {:b, :y}}
end

fn classify({:outer, {:a, :x}}), do: :left
fn classify({:outer, {:b, :y}}), do: :right
fn classify(_), do: :fallback

fn main(), do: classify(choose())
"#,
        "classify",
        1,
    );
    assert_eq!(
        nested,
        vec![0, 1],
        "nested tuple products must retain sibling correlation"
    );

    let list_of_tuples = reachable_clauses_for_source(
        "list_of_tuples_dispatch.fz",
        r#"
fn choose() do
  if true, do: [{:a, :x}], else: [{:b, :y}]
end

fn classify([{:a, :x} | _tail]), do: :left
fn classify([{:b, :y} | _tail]), do: :right
fn classify(_), do: :fallback

fn main(), do: classify(choose())
"#,
        "classify",
        1,
    );
    assert_eq!(
        list_of_tuples,
        vec![0, 1],
        "correlated list alternatives must preserve the tuple product observed at their head",
    );
}

#[test]
fn compiler2_dispatch_reachability_keeps_list_positions_and_unknown_tests_conservative() {
    let list_positions = reachable_clauses_for_source(
        "list_position_dispatch.fz",
        r#"
fn classify([true, true | _tail]), do: :same
fn classify(_), do: :fallback

fn main(), do: classify([true, false])
"#,
        "classify",
        1,
    );
    assert_eq!(
        list_positions,
        vec![0, 1],
        "one observed head must not globally narrow later positions of a homogeneous list type",
    );

    let guarded = reachable_clauses_for_source(
        "guarded_dispatch.fz",
        r#"
fn classify(value) when value == :a, do: :guarded
fn classify(_), do: :fallback

fn main(), do: classify(:a)
"#,
        "classify",
        1,
    );
    assert_eq!(
        guarded,
        vec![0, 1],
        "guard predicates remain conservative in semantic reachability"
    );
}

#[test]
fn compiler2_declared_domains_drive_function_head_exhaustiveness() {
    let diagnostics = no_matching_clause_diagnostics(
        "declared_domain_exhaustiveness.fz",
        r#"
@spec tuple_total({:a, :x} | {:b, :y}) :: atom
fn tuple_total({:a, :x}), do: :left
fn tuple_total({:b, :y}), do: :right

@spec overload_total(:a, :x) :: atom
@spec overload_total(:b, :y) :: atom
fn overload_total(:a, :x), do: :left
fn overload_total(:b, :y), do: :right

@spec count_a([:a]) :: integer
fn count_a([]), do: 0
fn count_a([:a | tail]), do: 1 + count_a(tail)

fn main() do
  {tuple_total({:a, :x}), overload_total(:b, :y), count_a([:a, :a])}
end
"#,
    );

    assert!(diagnostics.is_empty(), "total declared domains warned: {diagnostics:?}");
}

#[test]
fn compiler2_bounded_contract_domains_drive_function_head_exhaustiveness() {
    let diagnostics = no_matching_clause_diagnostics(
        "bounded_contract_exhaustiveness.fz",
        r#"
@spec bounded(t) :: atom when t: :a | :b
fn bounded(:a), do: :left
fn bounded(:b), do: :right

@spec nested({:tag, t}) :: atom when t: :a | :b
fn nested({:tag, :a}), do: :left
fn nested({:tag, :b}), do: :right

fn main(), do: {bounded(:a), nested({:tag, :b})}
"#,
    );

    assert!(
        diagnostics.is_empty(),
        "bounded declared domains warned: {diagnostics:?}"
    );
}

#[test]
fn compiler2_partial_bounded_contract_domain_still_warns() {
    let diagnostics = no_matching_clause_diagnostics(
        "partial_bounded_contract.fz",
        r#"
@spec partial(t) :: atom when t: :a | :b
fn partial(:a), do: :a

fn main(), do: partial(:a)
"#,
    );

    assert_eq!(
        diagnostics.len(),
        1,
        "the uncovered bounded atom must warn: {diagnostics:?}"
    );
    assert_eq!(diagnostics[0].1.message, "`fn` clauses don't cover every input");
}

#[test]
fn compiler2_partial_declared_domains_warn_with_and_without_guards() {
    let diagnostics = no_matching_clause_diagnostics(
        "partial_declared_domains.fz",
        r#"
@spec partial(:a | :b | :c) :: atom
fn partial(:a), do: :a
fn partial(:b), do: :b

@spec guarded(:a | :b) :: atom
fn guarded(value) when value == :a, do: :a

fn main(), do: {partial(:a), guarded(:a)}
"#,
    );

    assert_eq!(
        diagnostics
            .iter()
            .map(|(_, diagnostic)| diagnostic.message.as_str())
            .collect::<Vec<_>>(),
        vec![
            "`fn` clauses don't cover every input",
            "`fn` clauses don't cover every input",
        ],
        "both real fallthroughs must warn: {diagnostics:?}",
    );
    assert!(
        diagnostics
            .iter()
            .all(|(source, _)| source == "partial_declared_domains.fz")
    );
}

#[test]
fn compiler2_contracted_functions_keep_nested_match_diagnostics() {
    let diagnostics = no_matching_clause_diagnostics(
        "contracted_nested_case.fz",
        r#"
@spec nested(:ok) :: integer
fn nested(:ok) do
  case :a do
    :a -> 1
    :b -> 2
  end
end

fn main(), do: nested(:ok)
"#,
    );

    assert_eq!(
        diagnostics.len(),
        1,
        "only the nested case should warn: {diagnostics:?}"
    );
    assert_eq!(diagnostics[0].1.message, "`case` clauses don't cover every input");
}

#[test]
fn compiler2_invalid_contract_does_not_invent_a_domain_warning() {
    let diagnostics = no_matching_clause_diagnostics(
        "invalid_contract_domain.fz",
        r#"
@spec invalid(Missing.t) :: atom
fn invalid(:a), do: :a
fn invalid(:b), do: :b

fn main(), do: invalid(:a)
"#,
    );

    assert!(
        diagnostics.is_empty(),
        "an unresolved contract has no valid domain: {diagnostics:?}"
    );
}

#[test]
fn compiler2_enum_reduce_operator_ref_has_no_function_head_warnings() {
    let diagnostics = no_matching_clause_diagnostics(
        "fixtures2/00181_enum_reduce_operator_ref.fz",
        include_str!("../../fixtures2/00181_enum_reduce_operator_ref.fz"),
    );

    assert!(
        diagnostics.is_empty(),
        "runtime reducers should be total in their contracts: {diagnostics:?}"
    );
}

#[test]
fn compiler2_enum_runtime_domains_are_total_without_hiding_user_partiality() {
    for (source_name, source) in [
        (
            "fixtures2/behavior/enum_take_drop_split.fz",
            include_str!("../../fixtures2/behavior/enum_take_drop_split.fz"),
        ),
        (
            "fixtures2/behavior/enum_predicate_search.fz",
            include_str!("../../fixtures2/behavior/enum_predicate_search.fz"),
        ),
    ] {
        let runtime_diagnostics = no_matching_clause_diagnostics(source_name, source);
        assert!(
            runtime_diagnostics.is_empty(),
            "Enum and List runtime domains should be exhaustive for {source_name}: {runtime_diagnostics:?}"
        );
    }

    let user_diagnostics = no_matching_clause_diagnostics(
        "user_partial_function.fz",
        r#"
@spec partial(:a | :b) :: atom
fn partial(:a), do: :a

fn main(), do: partial(:a)
"#,
    );
    assert_eq!(
        user_diagnostics.len(),
        1,
        "a genuine user fallthrough must still warn: {user_diagnostics:?}"
    );
    assert_eq!(user_diagnostics[0].0, "user_partial_function.fz");
    assert_eq!(user_diagnostics[0].1.message, "`fn` clauses don't cover every input");
}

fn no_matching_clause_diagnostics(source_name: &str, source: &str) -> Vec<(String, Diagnostic)> {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);

    let mut world = crate::compiler2::World::new();
    let user_code = world.submit_code(Some(source_name.to_string()), source.to_string());
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    let outcome = super::drive::ExecutionContext::new(&mut world, &tel).drive();
    assert!(
        !matches!(outcome, DriveOutcome::Fatal { .. }),
        "diagnostic fixture must not fail fatally: {outcome:?}; diagnostics: {:?}",
        diagnostics.find(&["fz", "diag"]),
    );

    diagnostics
        .find(&["fz", "diag"])
        .into_iter()
        .filter_map(|event| event.diagnostic)
        .filter(|diagnostic| diagnostic.code == codes::TYPE_NO_MATCHING_CLAUSE)
        .map(|diagnostic| {
            let source = if diagnostic.primary.span.code_id.0 == user_code.as_u32() {
                source_name.to_string()
            } else {
                "<runtime>".to_string()
            };
            (source, diagnostic)
        })
        .collect()
}

fn reachable_clauses_for_source(source_name: &str, source: &str, function_name: &str, arity: u64) -> Vec<u32> {
    semantic_reachability_for_source(source_name, source, function_name, arity).0
}

fn semantic_reachability_for_source(
    source_name: &str,
    source: &str,
    function_name: &str,
    arity: u64,
) -> (Vec<u32>, String) {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);
    type ReachableByFunction = Vec<(u64, Vec<u32>)>;
    let analyses: Rc<RefCell<ReachableByFunction>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&analyses);
    tel.attach_raw_event2::<crate::compiler2::World, ActivationKey, _>(
        &["fz", "compiler2", "activation_analysis", "defined"],
        move |_, _, _, world, activation| {
            let Some(analysis) = world.activation_analysis(activation) else {
                return;
            };
            sink.borrow_mut().push((
                activation.function.as_u32() as u64,
                analysis.entry_reachability.clauses().to_vec(),
            ));
        },
    );

    let mut world = crate::compiler2::World::new();
    world.submit_code(Some(source_name.to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "dispatch reachability fixture should settle",
    );

    let function_id = function_id(&functions, function_name, arity);
    let function_measurement = function_id.as_u32() as u64;
    let reachable = analyses
        .borrow()
        .iter()
        .rev()
        .find(|(function, _)| *function == function_measurement)
        .map(|(_, clauses)| clauses.clone())
        .unwrap_or_else(|| panic!("{function_name}/{arity} should be analyzed"));
    let return_ty = returns.last_for_function(root, function_id).return_ty;
    (reachable, world.types().display(&return_ty))
}

#[test]
fn compiler2_int_keyed_map_index_types_through_the_carried_literal() {
    // Map keys are VALUES: the lowering carries the written constant
    // alongside the runtime key (LoweredMapKey), so %{1 => 10}[1] keeps its
    // precise int field type without numeric singleton types in the lattice.
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);

    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("map_int_key.fz".to_string()),
        concat!(
            "fn pick() do\n",
            "  m = %{1 => 10, 2 => 20}\n",
            "  m[1]\n",
            "end\n",
            "fn main(), do: pick()\n",
        )
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "int-keyed map program settles",
    );

    let pick_id = function_id(&functions, "pick", 0);
    let settled = returns.last_for_function(root, pick_id).return_ty;
    assert_eq!(
        world.types().display(&settled),
        "int",
        "the int-keyed lookup must keep its precise field type",
    );
}

#[test]
fn compiler2_numeric_literal_in_type_position_widens_with_a_warning() {
    // The lattice cannot express a numeric singleton: `@type digit :: 0`
    // means integer(), and the compiler says so once instead of silently
    // changing what the annotation filters.
    let tel = ConfiguredTelemetry::new();
    let diags = Capture::new();
    diags.install(&tel, &["fz", "diag"]);
    let rendered = rendered_type_defs(&tel);

    let mut world = crate::compiler2::World::new();
    world.submit_code(
        Some("digit.fz".to_string()),
        concat!(
            "@type digit :: 0\n",
            "fn pick(d :: digit), do: d\n",
            "fn main(), do: pick(7)\n",
        )
        .to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "the literal-typed program settles",
    );

    assert!(
        diags.find(&["fz", "diag", "warning"]).iter().any(|event| {
            event
                .diagnostic
                .as_ref()
                .is_some_and(|diagnostic| diagnostic.code.0 == "type/numeric-literal-widened")
        }),
        "widening a numeric literal type must warn",
    );
    let digit = rendered
        .borrow()
        .iter()
        .rev()
        .find(|def| def.name == "digit")
        .map(|def| def.rendered.clone())
        .expect("digit resolves");
    assert_eq!(digit, "int", "the literal type means its kind");
}
#[test]
fn compiler2_native_program_jit_adapts_callable_raw_returns_back_to_value_refs() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/repr_seam_closure_predicate.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/repr_seam_closure_predicate.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);

    assert_resolved(
        compiler.drive(),
        "native lowering should preserve callable return seams for closure predicates and reducers",
    );

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run_with_output(compiler.telemetry(), &dbg, program.entry),
        2,
        "the fixture should still return the final count after native callable-entry adaptation",
    );
    assert_eq!(
        dbg.lines().as_slice(),
        ["false", "false", "true", ":no", "2", "2", "2"],
        "callable-entry adapters should box raw predicate/reducer returns back onto the ValueRef callable seam",
    );
}

#[test]
fn compiler2_connected_callable_returns_share_one_public_value_ref_contract() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("connected_callable_returns.fz".to_string()),
        text: r#"
fn run(flag) do
  p = fn (x) -> {:p, x} end
  r = fn (x) -> {:r, x} end
  q = fn (x) -> x end
  left = if flag, do: p, else: r
  a = left.(1)
  right = if flag, do: p, else: q
  b = right.(2)
  {a, b, p}
end

fn main() do
  {a1, b1, _} = run(true)
  {a2, b2, _} = run(false)
  dbg({a1, b1, a2, b2})
  0
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(compiler.drive(), "connected callable returns should lower natively");

    let program = native.last(root_id).program;
    let returning_boundaries = program
        .callable_boundaries
        .iter()
        .filter(|boundary| {
            boundary
                .members
                .iter()
                .any(|member| !member.target_return.diverges && !member.target_return.layout.reprs.is_empty())
        })
        .collect::<Vec<_>>();
    assert!(!returning_boundaries.is_empty());
    assert!(
        returning_boundaries
            .iter()
            .all(|boundary| boundary.return_form == BackendCallableReturn::ValueRef)
    );
    assert!(returning_boundaries.iter().all(|boundary| {
        program.bodies.iter().any(|body| {
            body.origin
                == (NativeBodyOrigin::CallableWrapper {
                    identity: boundary.id.as_u32(),
                })
                && body.return_reprs == [AbiValueRepr::ValueRef]
        })
    }));

    let indirect_return_continuations = program
        .module
        .fns
        .iter()
        .flat_map(|function| &function.blocks)
        .filter_map(|block| match &block.terminator {
            IrTerm::CallClosure { continuation, .. } => {
                program.bodies.iter().find(|body| body.fn_id == continuation.fn_id)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(indirect_return_continuations.len() >= 2);
    assert!(indirect_return_continuations.iter().all(|body| {
        matches!(body.entry_abi, NativeEntryAbi::Continuation { extra_params: 1 })
            && body.param_reprs.last() == Some(&AbiValueRepr::ValueRef)
    }));

    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(compiled.run_with_output(compiler.telemetry(), &dbg, program.entry), 0);
    assert_eq!(dbg.lines(), ["{{:p, 1}, {:p, 2}, {:r, 1}, 2}"]);
}

#[test]
fn compiler2_published_captured_closure_keeps_its_public_return_contract() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("published_captured_closure.fz".to_string()),
        text: r#"
fn main() do
  n = 40
  f = fn (x) -> n + x end
  dbg(f)
  dbg(f.(2))
end
"#
        .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root);
    assert_resolved(compiler.drive(), "published captured closure should lower natively");
    let program = native.last(root).program;
    let [boundary] = program.callable_boundaries.as_slice() else {
        panic!("the published captured closure should own one boundary")
    };
    assert_eq!(boundary.captures.len(), 1);
    assert_eq!(boundary.return_form, BackendCallableReturn::ValueRef);
    let [member] = boundary.members.as_ref() else {
        panic!("the captured closure boundary should have one member")
    };
    assert_eq!(member.target_return.layout.reprs.as_ref(), [AbiValueRepr::RawInt]);

    // The closure call surviving as a `CallClosure` term is itself the
    // claim: a first-class construction calls through its wrapper.
    let closure_call = program
        .module
        .fns
        .iter()
        .flat_map(|function| &function.blocks)
        .find_map(|block| match &block.terminator {
            IrTerm::CallClosure { continuation, .. } => Some(continuation),
            _ => None,
        })
        .expect("the captured closure should emit one indirect closure call");
    let continuation = program
        .bodies
        .iter()
        .find(|body| body.fn_id == closure_call.fn_id)
        .expect("the captured closure call should own a return continuation");
    assert!(matches!(
        continuation.entry_abi,
        NativeEntryAbi::Continuation { extra_params: 1 }
    ));
    assert_eq!(continuation.param_reprs.first(), Some(&AbiValueRepr::ValueRef));

    compiler
        .run_root_interp(root)
        .expect("the backend interpreter should run the published captured closure");
    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(compiled.run_with_output(compiler.telemetry(), &dbg, program.entry), 42);
    let lines = dbg.lines();
    assert_eq!(lines.len(), 4);
    assert!(lines[0].starts_with("#fn<") && lines[2].starts_with("#fn<"));
    assert_eq!(lines[1], "42");
    assert_eq!(lines[3], "42");
}

#[test]
fn compiler2_multi_target_closure_arg_floor_clears_the_shared_reducer_demand_crash() {
    // INTENT: `Enum.find` and `Enum.find_value` share one generic reduce body
    // whose `_acc` reducer parameter `find` never reads and `find_value` does.
    // Before the arg-floor generalization, the per-target join of that
    // parameter's demand collapsed to `Ignore` (find contributes `Ignore`,
    // find_value's contribution joins against it) at the shared body's
    // ambiguous (2-target) closure callsite, so the accumulator's input was
    // never demanded as a runtime-materializable value: interp failed with
    // "backend value 6 is unbound" before ever reaching a resolved callee.
    // The generalized floor demands the FULL argument tuple at any ambiguous
    // multi-target closure callsite (matching the boxed-apply ABI, which
    // transmits every lane regardless of which target is selected at
    // runtime), so that crash must be gone. Depending on which closure-entry
    // evidence has already settled, the interpreter may now either complete
    // this fixture or still stop at the separate callable-entry resolution gap.
    // Both outcomes are past the demand-floor bug. Native lowering's own
    // closure-target-surface consistency check that used to fault on this same
    // shared body has since been proven sound and deleted, not merely deferred
    // -- see `compiler2_multi_target_closure_arg_floor_shares_one_capture_surface_across_boundaries`.
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00279_enum_find_find_value.fz".to_string()),
        text: include_str!("../../fixtures2/00279_enum_find_find_value.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    match compiler.run_root_interp(root_id) {
        Ok(_) => assert_eq!(
            dbg.lines().as_slice(),
            ["3", "{:even, 2}"],
            "if callable-entry evidence is settled, the fixture should complete with both Enum results",
        ),
        Err(error) => assert!(
            !error.contains("is unbound"),
            "the demand-floor fix should stop the shared-body accumulator from being left as an unbound \
             backend value, but got: {error}",
        ),
    }
}

#[test]
fn compiler2_multi_target_closure_arg_floor_keeps_unique_member_on_producer_construction() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let functions = FunctionCapture::new();
    functions.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00279_enum_find_find_value.fz".to_string()),
        text: include_str!("../../fixtures2/00279_enum_find_find_value.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "native program lowering must settle for a shared reducer body named by two boundaries with differing \
         call-site return shapes -- this used to panic in build_codegen_closure_targets' deleted consistency loop",
    );

    let program = native.last(root_id).program;
    let predicate = functions
        .all()
        .into_iter()
        .find(|record| {
            record
                .function_ref
                .name
                .strip_prefix("#lambda:0:")
                .is_some_and(|range| {
                    range.split_once('-').is_some_and(|(start, end)| {
                        start
                            .parse::<usize>()
                            .ok()
                            .zip(end.parse::<usize>().ok())
                            .and_then(|(start, end)| {
                                include_str!("../../fixtures2/00279_enum_find_find_value.fz").get(start..end)
                            })
                            .is_some_and(|source| source.contains("x > 2"))
                    })
                })
        })
        .expect("find predicate producer should be indexed")
        .function_id;
    let boundary = program
        .callable_boundaries
        .iter()
        .find(|boundary| {
            boundary.members.len() == 1
                && boundary
                    .members
                    .iter()
                    .all(|member| member.target.activation.function == predicate)
        })
        .expect("the find predicate should remain the unique member of its producer construction");
    let target = boundary.members[0].target_fn;
    assert_ne!(
        boundary.wrapper_fn, target,
        "producer target {target:?} must stay behind its construction wrapper",
    );
}

/// fz-kdt.183 re-aimed this gate from `enum_predicate_search` at
/// `enum_take_drop_split`. The old subject stopped building multi-member
/// callable constructions at all -- its wrappers each carried three reducer
/// specializations keyed on a list element the key did not name, and with the
/// element in the key each wrapper has ONE member -- so the gate's own
/// coverage assertion (`saw_multi_member_construction`) went vacuous. The new
/// subject still builds sixteen multi-member wrappers with physical captures,
/// measured over the 469 backend dumps of the corpus, and it is the widest
/// such fixture that is not one of the two slowest.
#[test]
fn compiler2_backend_construction_members_use_target_owned_capture_surfaces() {
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    backend.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/behavior/enum_take_drop_split.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/enum_take_drop_split.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    demand_backend_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "enum_take_drop_split should settle the backend product cleanly",
    );

    let program = backend.last(root_id).program;
    let mut by_target: HashMap<&ExecutableKey, Vec<Vec<AbiValueRepr>>> = HashMap::new();
    for member in program
        .construction_wrappers()
        .iter()
        .flat_map(|wrapper| wrapper.members.iter())
    {
        let capture_reprs = member
            .capture_semantic_inputs
            .iter()
            .flat_map(|semantic_index| {
                member
                    .target_inputs
                    .iter()
                    .find(|input| input.semantic_index == *semantic_index)
                    .into_iter()
                    .flat_map(|input| input.layout.reprs.iter().copied())
            })
            .collect::<Vec<_>>();
        by_target.entry(&member.target).or_default().push(capture_reprs);
    }

    let saw_multi_member_construction = program
        .construction_wrappers()
        .iter()
        .any(|wrapper| wrapper.members.len() > 1);
    let mut saw_physical_capture = false;
    for (target, capture_surfaces) in &by_target {
        if capture_surfaces.iter().any(|surface| !surface.is_empty()) {
            saw_physical_capture = true;
        }
        if capture_surfaces.len() < 2 {
            continue;
        }
        let first = &capture_surfaces[0];
        for capture_surface in &capture_surfaces[1..] {
            assert_eq!(
                capture_surface, first,
                "construction members naming target {target:?} should use its one settled capture surface",
            );
        }
    }
    assert!(
        saw_multi_member_construction,
        "enum_take_drop_split should exercise multi-member callable constructions",
    );
    assert!(
        saw_physical_capture,
        "enum_take_drop_split should exercise callable members with physical captures",
    );
}

#[test]
fn compiler2_native_program_publishes_construction_owned_callable_wrappers() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/behavior/enum_predicate_search.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/enum_predicate_search.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    settle_native_product(&mut compiler, root_id);
    assert_resolved(
        compiler.drive(),
        "enum_predicate_search should settle native lowering with construction-owned callable wrappers",
    );

    let program = native.last(root_id).program;
    assert!(
        !program.callable_boundaries.is_empty(),
        "enum_predicate_search should publish callable construction wrappers",
    );
    assert!(
        program
            .callable_boundaries
            .iter()
            .any(|boundary| !boundary.captures.is_empty()),
        "non-vacuous guard: at least one construction should carry a real capture surface",
    );
    for boundary in &program.callable_boundaries {
        assert!(
            !boundary.members.is_empty(),
            "every construction wrapper needs a member adapter"
        );
        assert!(
            boundary.members.iter().all(|member| {
                member
                    .target_inputs
                    .windows(2)
                    .all(|inputs| inputs[0].semantic_index < inputs[1].semantic_index)
            }),
            "construction member adapters must publish target semantic input order",
        );
    }
}

#[test]
fn activation_jobs_facts_and_uses_share_one_order_across_display_collisions_and_mint_histories() {
    use crate::compiler2::semantic::SemanticOrd;

    let ordered = |non_empty_first: bool| {
        let mut types = Types::new();
        let int = types.int();
        let root = crate::compiler2::RootId::for_test(0);
        let function = FunctionId::for_test(0);
        let (list, non_empty, list_key, non_empty_key) = if non_empty_first {
            let non_empty = types.non_empty_list(int);
            let non_empty_key = ActivationKey::from_inputs(root, function, &[non_empty], &mut types);
            let list = types.list(int);
            let list_key = ActivationKey::from_inputs(root, function, &[list], &mut types);
            (list, non_empty, list_key, non_empty_key)
        } else {
            let list = types.list(int);
            let list_key = ActivationKey::from_inputs(root, function, &[list], &mut types);
            let non_empty = types.non_empty_list(int);
            let non_empty_key = ActivationKey::from_inputs(root, function, &[non_empty], &mut types);
            (list, non_empty, list_key, non_empty_key)
        };
        assert_eq!(types.display(&list), types.display(&non_empty));
        let raw_order = list_key.arrow < non_empty_key.arrow;

        let jobs = [
            Job::AnalyzeActivation(list_key.clone()),
            Job::AnalyzeActivation(non_empty_key.clone()),
        ];
        let facts = [
            FactKey::ReturnType(list_key.clone()),
            FactKey::ReturnType(non_empty_key.clone()),
        ];
        let uses = [
            FactUse::settled(FactKey::ReturnType(list_key)),
            FactUse::settled(FactKey::ReturnType(non_empty_key)),
        ];

        let before = types.comparison_cache_stats();
        let job_order = jobs[0].semantic_cmp(&jobs[1], &types);
        let after_job = types.comparison_cache_stats();
        assert_eq!(after_job.semantic_order_misses, before.semantic_order_misses + 1);
        assert_eq!(after_job.semantic_order_hits, before.semantic_order_hits);
        let fact_order = facts[0].semantic_cmp(&facts[1], &types);
        let use_order = uses[0].semantic_cmp(&uses[1], &types);
        let reverse_order = jobs[1].semantic_cmp(&jobs[0], &types);
        let after_repeats = types.comparison_cache_stats();
        assert_eq!(after_repeats.semantic_order_misses, after_job.semantic_order_misses);
        assert_eq!(after_repeats.semantic_order_hits, after_job.semantic_order_hits + 3);
        assert_eq!(
            reverse_order,
            job_order.reverse(),
            "the normalized pair must reuse its inverse"
        );
        assert_ne!(job_order, std::cmp::Ordering::Equal);
        assert_ne!(fact_order, std::cmp::Ordering::Equal);
        assert_ne!(use_order, std::cmp::Ordering::Equal);
        (raw_order, job_order, fact_order, use_order)
    };

    let list_first = ordered(false);
    let non_empty_first = ordered(true);
    assert_ne!(
        list_first.0, non_empty_first.0,
        "the fixture must reverse raw activation-arrow order"
    );
    assert_eq!(
        (list_first.1, list_first.2, list_first.3),
        (non_empty_first.1, non_empty_first.2, non_empty_first.3),
        "Job, FactKey, and FactUse must retain one semantic order"
    );
}

#[test]
fn shared_fact_readers_and_waiters_use_typed_activation_job_order() {
    use crate::compiler2::facts::DerivationId;
    use crate::compiler2::scheduler::{DerivationEffects, Scheduler};
    use crate::compiler2::semantic::SemanticOrd;

    let mut types = Types::new();
    let int = types.int();
    let root = crate::compiler2::RootId::for_test(0);
    let function = FunctionId::for_test(0);
    let list = types.list(int);
    let non_empty = types.non_empty_list(int);
    let mut jobs = vec![
        Job::AnalyzeActivation(ActivationKey::from_inputs(root, function, &[non_empty], &mut types)),
        Job::AnalyzeActivation(ActivationKey::from_inputs(root, function, &[list], &mut types)),
    ];
    jobs.sort_by(|left, right| left.semantic_cmp(right, &types));
    let shared = FactKey::CodeIndexed(crate::compiler2::CodeId::ZERO);
    let writer = Job::IndexCode(crate::compiler2::CodeId::ZERO);

    let complete = |scheduler: &mut Scheduler<Job, FactKey>,
                    job: &Job,
                    reads: HashSet<FactUse<FactKey>>,
                    waits: HashSet<FactUse<FactKey>>,
                    outputs: Vec<FactKey>,
                    changed: Vec<FactKey>| {
        scheduler.complete_ordered(
            job,
            waits.clone(),
            vec![DerivationEffects {
                derivation: DerivationId::SOLE,
                reads,
                outputs,
                changed,
                concluded: waits.is_empty(),
            }],
            &types,
        )
    };

    let reader_run = |registration: &[Job]| {
        let mut scheduler = Scheduler::new();
        for job in registration {
            complete(
                &mut scheduler,
                job,
                HashSet::from([FactUse::current(shared.clone())]),
                HashSet::new(),
                Vec::new(),
                Vec::new(),
            );
        }
        let step = complete(
            &mut scheduler,
            &writer,
            HashSet::new(),
            HashSet::new(),
            vec![shared.clone()],
            vec![shared.clone()],
        );
        let wakes = step
            .wakes
            .into_iter()
            .map(|wake| (wake.job, wake.disposition))
            .collect::<Vec<_>>();
        let popped = std::iter::from_fn(|| scheduler.pop()).collect::<Vec<_>>();
        (wakes, popped)
    };
    assert_eq!(reader_run(&jobs), reader_run(&[jobs[1].clone(), jobs[0].clone()]));

    let waiter_run = |registration: &[Job]| {
        let mut scheduler = Scheduler::new();
        for job in registration {
            complete(
                &mut scheduler,
                job,
                HashSet::new(),
                HashSet::from([FactUse::current(shared.clone())]),
                Vec::new(),
                Vec::new(),
            );
        }
        let unresolved = scheduler.unresolved(&types);
        let step = complete(
            &mut scheduler,
            &writer,
            HashSet::new(),
            HashSet::new(),
            vec![shared.clone()],
            vec![shared.clone()],
        );
        let wakes = step
            .wakes
            .into_iter()
            .map(|wake| (wake.job, wake.disposition))
            .collect::<Vec<_>>();
        let popped = std::iter::from_fn(|| scheduler.pop()).collect::<Vec<_>>();
        (unresolved, wakes, popped)
    };
    assert_eq!(waiter_run(&jobs), waiter_run(&[jobs[1].clone(), jobs[0].clone()]));
}

/// The fixtures whose backend products carry the `[] -> [τ]` ascent ladder,
/// and how many rung/slot readings each one holds.
///
/// The corpus census (the recipe in `.agent/docs/type-specialization.md`, over
/// `--dump backend=` on all 597 fixtures) reads 58 rungs over 16 fixtures at
/// fz-kdt.183, up from 53 over 15. These five carry the two runtime modules the
/// six NEW rungs live in plus the three heaviest ladder fixtures, so the gate
/// below walks real ladders rather than asserting a vacuous zero.
const ASCENT_RUNG_FIXTURES: &[&str] = &[
    "fixtures2/behavior/map_enumerable.fz",
    "fixtures2/behavior/range_enumerable.fz",
    "fixtures2/behavior/enum_take_drop_split.fz",
    "fixtures2/behavior/fz_f98_range_map_converges.fz",
    "fixtures2/behavior/dead_closure_capture_empty_list.fz",
];

/// fz-kdt.183 / fz-kdt.124: an ascent rung never climbs a slot nothing demands.
///
/// A RUNG is two keys of one function where one is the other with a list
/// position EMPTIED -- `empty_list()` where the sibling has a list family that
/// contains it. It exists because `list_element_type([])` is `none`, so `[]`
/// never converges with `list(τ)`, and a slot that keeps its element therefore
/// keys the accumulator's first call apart from every later one. That is
/// fz-kdt.124's ladder and fz-kdt.182 owns the duplicate executables it mints.
///
/// What THIS gate holds is the boundary fz-kdt.183 drew and fz-kdt.199 widened
/// by one axis. A slot BOTH axes leave at `Ignore` is FREIGHT: the collapse
/// maps every list family reaching it to one addressed class, so `[]` and
/// `list(τ)` cannot key apart there, and a rung on such a slot would mean the
/// collapse did not run. The measured count is 0 and it is 0 by construction,
/// which is why the assertion is an emptiness and not a number.
///
/// The six rungs fz-kdt.183 ADDED are all on demanded slots and all honest:
/// `Map.to_list/4` slot 3 and `Map.reverse/2` slot 0 (map.fz's `reverse(acc,
/// [])` forwards the accumulator into `Map.reverse/2`'s dispatch slot),
/// `Range.slice_from/5` slot 4 and `Range.reverse/2` slot 0 (range.fz the
/// same), and `Kernel.dbg/1` / `Kernel.fz_dbg_value/1` on
/// `00277_enum_tier0_fixture`, whose final mask is `[Ignore]` on a
/// NON-recursive body -- the key is precise evidence there and no mask plays
/// any part. `Range.reduce/5`'s rung retires in the same motion. One
/// accumulator per function, not a product: bounded by the rule's own law.
#[test]
fn compiler2_no_ascent_rung_sits_on_a_freight_slot_of_a_recursive_key() {
    let mut readings = 0_usize;
    let mut on_freight = Vec::new();
    for fixture in ASCENT_RUNG_FIXTURES {
        let (compiler, program) = driven_backend_program(fixture);
        let world = compiler.world();
        let types = world.types();
        // `Types::display` renders `list(int)` and `non_empty_list(int)` alike
        // (`canon_test`'s display hole), and those two are DISJOINT rather than
        // a ladder. `TyCanon` is the comparand the `--dump backend=` keys and
        // the corpus census both read, so the gate reads what they read.
        let labels = |fn_id| crate::compiler2::canon::function_label(world, FunctionId::from_fn_id(fn_id));
        let mut canon = crate::compiler2::TyCanon::new(&labels);
        let mut columns_by_function: HashMap<crate::compiler2::FunctionId, Vec<Vec<String>>> = HashMap::new();
        for executable in program.executables() {
            let activation = &executable.key.activation;
            let columns = activation
                .inputs(types)
                .iter()
                .map(|input| canonical_type_body(&canon.render(types, *input)))
                .collect::<Vec<_>>();
            let seen = columns_by_function.entry(activation.function).or_default();
            if !seen.contains(&columns) {
                seen.push(columns);
            }
        }
        for (function, columns) in &columns_by_function {
            if !world.body_keying(*function).is_some_and(|keying| keying.recursive) {
                // A non-recursive key is precise evidence; no collapse runs and
                // the demand plays no part in it.
                continue;
            }
            let demand = world
                .input_demand(*function)
                .expect("a keyed activation should have published its input demand");
            for low in columns {
                for high in columns {
                    for (slot, (low, high)) in low.iter().zip(high.iter()).enumerate() {
                        if !is_ascent_rung(low, high) {
                            continue;
                        }
                        readings += 1;
                        let ignored = |axis: &Vec<crate::compiler2::keying::DispatchDemand>| {
                            matches!(
                                axis.get(slot),
                                None | Some(crate::compiler2::keying::DispatchDemand::Ignore)
                            )
                        };
                        // A rung may sit on a slot EITHER axis names: the
                        // dispatch axis keeps a demanded list's element, and
                        // the `returned` axis keeps a returned position's
                        // ground class (fz-kdt.199). Freight is the slot
                        // neither names.
                        if ignored(&demand.forwarded_dispatch) && ignored(&demand.returned) {
                            on_freight.push(format!(
                                "{fixture} {} slot {slot}: `{low}` keys apart from `{high}` on a slot \
                                 nothing demands",
                                crate::compiler2::canon::function_label(world, *function),
                            ));
                        }
                    }
                }
            }
        }
    }
    println!(
        "ascent rung readings over {} fixtures: {readings}",
        ASCENT_RUNG_FIXTURES.len()
    );
    assert!(
        on_freight.is_empty(),
        "a freight slot collapses every list family to one addressed class, so a rung there means the \
         collapse did not run: {on_freight:#?}",
    );
    assert!(
        readings > 0,
        "the gate proved no rung at all, so it cannot have held anything: re-aim \
         `ASCENT_RUNG_FIXTURES` at fixtures that still carry the ladder",
    );
}

/// Whether `low` is `high` with one or more list positions EMPTIED, at any
/// structural depth.
///
/// The comparand is the one the corpus census recipe in
/// `.agent/docs/type-specialization.md` reads off `--dump backend=` -- the
/// canonical type body -- but the relation here is BROADER: this gate asks the
/// question of each slot independently, where the census counts a sibling pair
/// only when EVERY column stands in the relation. That is deliberate (a gate
/// should over-read, not under-read) and it is why the two report different
/// populations off the same dumps. `non_empty_list` is disjoint from
/// `empty_list`, so an `empty_list()` beside a `non_empty_list(τ)` is two
/// clause specializations, not a ladder rung.
fn is_ascent_rung(low: &str, high: &str) -> bool {
    fn absorbing_list_element(ty: &str) -> Option<&str> {
        ty.strip_prefix("list(")?.strip_suffix(')')
    }
    fn same_kind_element<'a>(ty: &'a str, kind: &str) -> Option<&'a str> {
        ty.strip_prefix(kind)?.strip_suffix(')')
    }
    fn list_kind(ty: &str) -> Option<&'static str> {
        if ty.starts_with("list(") {
            Some("list(")
        } else if ty.starts_with("non_empty_list(") {
            Some("non_empty_list(")
        } else {
            None
        }
    }
    fn tuple_fields(ty: &str) -> Option<Vec<&str>> {
        let inner = ty.strip_prefix('{')?.strip_suffix('}')?;
        Some(split_top_level(inner))
    }
    fn walk(low: &str, high: &str) -> Option<usize> {
        if low == high {
            return Some(0);
        }
        if (low == "[]" || low == "empty_list()") && absorbing_list_element(high).is_some() {
            return Some(1);
        }
        if let (Some(low_fields), Some(high_fields)) = (tuple_fields(low), tuple_fields(high))
            && low_fields.len() == high_fields.len()
        {
            let mut total = 0;
            for (low, high) in low_fields.iter().zip(high_fields.iter()) {
                total += walk(low, high)?;
            }
            return Some(total);
        }
        let (low_kind, high_kind) = (list_kind(low)?, list_kind(high)?);
        if low_kind != high_kind {
            return None;
        }
        walk(same_kind_element(low, low_kind)?, same_kind_element(high, high_kind)?)
    }
    walk(low, high).is_some_and(|depth| depth > 0)
}

/// A canonical rendering is `<fingerprint> <body>`; the body is the structural
/// text the ladder is a relation over.
fn canonical_type_body(rendered: &str) -> String {
    rendered
        .split_once(' ')
        .map(|(_fingerprint, body)| body)
        .unwrap_or(rendered)
        .to_string()
}

/// The comma-separated parts of `text` at bracket depth zero.
fn split_top_level(text: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0_i32;
    let mut start = 0_usize;
    for (index, ch) in text.char_indices() {
        match ch {
            '[' | '{' | '(' => depth += 1,
            ']' | '}' | ')' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(text[start..index].trim());
                start = index + 1;
            }
            _ => {}
        }
    }
    parts.push(text[start..].trim());
    parts
}

/// The keying laws fz-kdt.183 and fz-kdt.199 must hold in BOTH directions,
/// each as the smallest program that states one: source, the function the law
/// is about, and how many activations of it the program may key.
///
/// The first four are the rules' LOWER bound -- a slot nothing demands and
/// nothing returns is freight and must not split, which is what makes this a
/// demand rule rather than "keep every element" (measured: keeping every list
/// element splits `partition/4` 1 -> 4 and `split4/6` 1 -> 16, all bodies
/// identical).
///
/// `tag/3`'s accumulator states fz-kdt.199's exclusion, and it is a COST law
/// rather than a precision one. `tag/3` returns its accumulator, so the return
/// does depend on a slot the key erases -- but the recursion SUPPLIES that
/// slot, so the seed activation is the one every caller passes through and its
/// `[]` is the same `[]` for all of them. Keying it mints one activation per
/// ascent state (measured: three) and the seed still publishes the join, so the
/// split is cost with nothing bought.
///
/// `fwd/2` is fz-6gb's law, and it is why `InputDemand`'s dispatch demand
/// carries two halves. `fwd/2` only TRANSPORTS its callable: no clause of
/// `fwd/2` tests it, so two same-shape lambdas must key one activation. But
/// `apply2/2` -- which `fwd/2` forwards both slots to -- tests slot 0 against
/// `:none`, so the FORWARDED demand on that slot is `Whole`. Erasing brands
/// against the forwarded half would un-share `fwd/2` into one activation per
/// lambda; erasing against the LOCAL half keeps fz-6gb's law intact while the
/// key collapse still reads the forwarded demand.
///
/// The last three are the rules' UPPER bound: a position the activation
/// RETURNS and the recursion does NOT supply must key its users apart, or one
/// activation answers for both with the join of their returns (fz-kdt.199).
/// `loop/2` states it at a whole slot and `walk/2` one tuple field down, where
/// the key names the tag and the return IS the payload. `walk/2`'s four are two
/// tags times two payload element types.
///
/// `loop/2` is a CORRECTION of a landed law. fz-kdt.183 blessed exactly this
/// program at ONE activation as its freight law. Measured on the tree that law
/// landed on: `loop(0, junk), do: junk` keys one activation publishing
/// `non_empty_list(binary) | non_empty_list(int)`, and a `@spec` consumer
/// asking `[binary]` for the first user rejects the program with
/// `error[spec/violation] ([binary] | [int])`. So the blessed row was pinning a
/// live wrong-typing as correct: it was a COST law, not a correctness one, and
/// this axis is what makes freight collapse safe. `carry/2` -- the same shape
/// that does NOT return the slot -- is the true freight statement and stays
/// at 1.
///
/// `go/3` states the exclusion's boundary. It is a pure PERMUTATION: each
/// self-call hands a slot the value the caller held at the OTHER slot, so the
/// recursion supplies neither and both stay carried. That is why the exclusion
/// is a LEAST FIXPOINT over "held nowhere, or held only at supplied positions"
/// rather than the eager "not held at this same position" -- the eager test
/// marks both slots supplied here and re-blends the two users into the base's
/// wrong diagnostic.
///
/// What these rows prove, stated exactly: for every shape here the published
/// return depends only on what the key names. They do NOT prove the invariant
/// in general. The exclusion reads SELF calls only, so a position supplied
/// across a mutual cycle or through a generated lambda is keyed anyway (cost,
/// never unsoundness -- fz-kdt.213), and the axis rides fz-kdt.183's dispatch
/// edge set, which does not see a reconstructed or projected forwarding
/// argument (a missed cure -- fz-kdt.214).
const ONE_ACTIVATION_KEYING_LAWS: &[(&str, &str, &str, usize)] = &[
    (
        "a slot no callee reads and the body does not return is freight",
        "carry/2",
        "fn carry(0, junk), do: 0\n\
         fn carry(n, junk), do: carry(n - 1, junk)\n\
         fn main() do\n  dbg(carry(3, [1, 2]))\n  dbg(carry(3, [\"a\", \"b\"]))\nend\n",
        1,
    ),
    (
        "an accumulator the recursion itself supplies stays collapsed",
        "tag/3",
        "fn tag(_f, [], acc), do: acc\n\
         fn tag(f, [h | t], acc), do: tag(f, t, [f.(h) | acc])\n\
         fn main() do\n  dbg(tag(fn (_x) -> \"n\" end, [1, 2], []))\n\
         \x20 dbg(tag(fn (x) -> x + 1 end, [1, 2], []))\nend\n",
        1,
    ),
    (
        "three accumulators built by consing are opaque, not forwarded",
        "split3/5",
        "fn split3(_, [], a, b, c), do: {a, b, c}\n\
         fn split3(p, [h | t], a, b, c) when h < p, do: split3(p, t, [h | a], b, c)\n\
         fn split3(p, [h | t], a, b, c) when h == p, do: split3(p, t, a, [h | b], c)\n\
         fn split3(p, [h | t], a, b, c), do: split3(p, t, a, b, [h | c])\n\
         fn main() do\n  {a, b, c} = split3(4, [3, 1, 4, 1, 5, 9, 2, 6], [], [], [])\n\
         \x20 dbg(a)\n  dbg(b)\n  dbg(c)\nend\n",
        1,
    ),
    (
        "four accumulators do not become a product either",
        "split4/6",
        "fn split4(_, [], a, b, c, d), do: {a, b, c, d}\n\
         fn split4(p, [h | t], a, b, c, d) when h < p, do: split4(p, t, [h | a], b, c, d)\n\
         fn split4(p, [h | t], a, b, c, d) when h == p, do: split4(p, t, a, [h | b], c, d)\n\
         fn split4(p, [h | t], a, b, c, d) when h > 6, do: split4(p, t, a, b, [h | c], d)\n\
         fn split4(p, [h | t], a, b, c, d), do: split4(p, t, a, b, c, [h | d])\n\
         fn main() do\n  {a, b, c, d} = split4(4, [3, 1, 4, 1, 5, 9, 2, 6], [], [], [], [])\n\
         \x20 dbg(a)\n  dbg(b)\n  dbg(c)\n  dbg(d)\nend\n",
        1,
    ),
    (
        "a transported callable is freight to its forwarder even when a callee tests it",
        "fwd/2",
        "fn apply2(:none, x), do: x\n\
         fn apply2(f, x), do: f.(x)\n\
         fn fwd(f, x), do: apply2(f, x)\n\
         fn main() do\n  dbg(fwd(fn (a) -> a + 1 end, 1))\n  dbg(fwd(fn (a) -> a + 2 end, 1))\nend\n",
        1,
    ),
    (
        "a slot the body RETURNS and the recursion carries keys its users apart",
        "loop/2",
        "fn loop(0, junk), do: junk\n\
         fn loop(n, junk), do: loop(n - 1, junk)\n\
         fn main() do\n  dbg(loop(3, [1, 2]))\n  dbg(loop(3, [\"a\", \"b\"]))\nend\n",
        2,
    ),
    (
        "a self-call that PERMUTES two carried slots supplies neither, so a returned one still keys",
        "go/3",
        "fn go(0, a, _b), do: a\n\
         fn go(n, a, b), do: go(n - 1, b, a)\n\
         fn main() do\n  dbg(go(2, [\"x\"], [\"y\"]))\n  dbg(go(2, [9], [8]))\nend\n",
        2,
    ),
    (
        "a returned tuple FIELD keys its users apart while the key names the tag",
        "walk/2",
        "fn walk({:stop, acc}, _n), do: acc\n\
         fn walk({:go, acc}, 0), do: walk({:stop, acc}, 0)\n\
         fn walk({:go, acc}, n), do: walk({:go, acc}, n - 1)\n\
         fn main() do\n  dbg(walk({:go, [1, 2]}, 2))\n  dbg(walk({:go, [\"a\"]}, 2))\nend\n",
        4,
    ),
];

#[test]
fn compiler2_input_demand_keys_one_activation_where_nothing_demands_the_slot() {
    let mut moved = Vec::new();
    for (law, label, source, expected) in ONE_ACTIVATION_KEYING_LAWS {
        let tel = ConfiguredTelemetry::new();
        let backend = BackendProgramCapture::new();
        backend.install(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some(format!("{label} keying law")),
            text: (*source).to_string(),
        });
        let root_id = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        demand_backend_product(&mut compiler, root_id);
        assert_resolved(
            compiler.drive(),
            &format!("{law}: the program must settle to a backend product"),
        );

        let program = backend.last(root_id).program;
        let world = compiler.world();
        let keyed = program
            .executables()
            .iter()
            .filter(|executable| {
                crate::compiler2::canon::function_label(world, executable.key.activation.function) == *label
            })
            .count();
        if keyed != *expected {
            moved.push(format!(
                "{law}: {label} keys {keyed} activations, the law says {expected}"
            ));
        }
    }
    assert!(
        moved.is_empty(),
        "a slot is keyed on DEMAND, not on structure, and demand has TWO axes: a dispatch question \
         reaching it (fz-kdt.183) or the published return being built from it and the recursion not \
         supplying it (fz-kdt.199). A slot NEITHER axis reaches stays collapsed, and brand erasure \
         keeps asking the local question: {moved:#?}",
    );
}
