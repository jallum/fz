use super::{AppliedStep, CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, Job, RootSubmission};
use crate::compiler2::artifact::{BackendEntry, BackendTail};
use crate::compiler2::artifact::{NativeBodyOrigin, NativeCallableBoundaryId, NativeEntryAbi, NativeProgram};
use crate::compiler2::drive::JobEffects;
use crate::compiler2::{
    AbiReadyProgram, AbiValueRepr, ActivationKey, BackendProgram, CallSiteId, CallSiteKey, CallSiteSummary, CallTarget,
    CallableEntry, ControlEntryOrigin, EmissionReadyProgram, ExecutableKey, FactKey, FactUse, FunctionId, FunctionRef,
    LoweredBody, LoweredStep, LoweredTail, MaterializedProgram, ModuleId, ModuleState, QuotedSourceHeap,
    QuotedSourceMetadata, ReturnAbi, SelectedCallee, SemanticClosure, Ty, TypeName, TypeVarId, Types, ValueId,
    parse_quoted_program,
};
use crate::diag::codes;
use crate::dispatch_matrix::Region;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::exec::runtime::DbgCapture;
use crate::fz_ir::{
    Block as IrBlock, CallsiteId as IrCallsiteId, CallsiteIdent, Cont as IrCont, ExternTy, ExternalCallEdge, FnId,
    FnIr as IrFn, Module as IrModule, PhysicalCapability, Prim as IrPrim, ReceiveAfter, ReceiveClause, Stmt as IrStmt,
    Term as IrTerm,
};
use crate::ir_interp::{
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset, tests_support_lock,
};
use crate::telemetry::handler::{Event, EventKind, Handler};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

type OutputFacts = Vec<(FactKey, bool)>;
type JobOutputMap = Rc<RefCell<HashMap<Job, Vec<OutputFacts>>>>;
type AppliedSteps = Rc<RefCell<Vec<AppliedStep<Job, FactKey>>>>;
type EntryDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<PatternDispatchPlan<Ty>>>>>;
type GuardDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<PatternGuardDispatch<Ty>>>>>;
type LoweredBodyDefs = Rc<RefCell<HashMap<FunctionId, Vec<LoweredBody>>>>;
type SpanJobs = Rc<RefCell<HashMap<u64, Job>>>;
type FunctionDefs = Rc<RefCell<HashMap<FunctionId, FunctionDefinedRecord>>>;
type ModuleDefs = Rc<RefCell<HashMap<ModuleId, Vec<ModuleState>>>>;
type CallsiteDefs = Rc<RefCell<Vec<CallsiteDefinedRecord>>>;
type SemanticClosedDefs = Rc<RefCell<Vec<SemanticClosedRecord>>>;
type MaterializedProgramDefs = Rc<RefCell<Vec<MaterializedProgramRecord>>>;
type AbiReadyProgramDefs = Rc<RefCell<Vec<AbiReadyProgramRecord>>>;
type EmissionReadyProgramDefs = Rc<RefCell<Vec<EmissionReadyProgramRecord>>>;
type BackendProgramDefs = Rc<RefCell<Vec<BackendProgramRecord>>>;
type NativeProgramDefs = Rc<RefCell<Vec<NativeProgramRecord>>>;
type ReturnTypeDefs = Rc<RefCell<Vec<ReturnTypeRecord>>>;

fn jit_compile_native_program(
    compiler: &mut Compiler2<'_>,
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

#[test]
fn compiler2_runtime_prelude_does_not_run_frontend_before_drive() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    // Unique `tkf_` names so the assertions ignore the runtime prelude's own
    // @types, which are noted in the same drive when the user scope pulls it.
    let mut compiler = Compiler2::new(&tel);
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

    let mine = capture
        .find(&["fz", "compiler2", "type", "noted"])
        .into_iter()
        .filter(|event| metadata_str(event, "name").starts_with("tkf_"))
        .collect::<Vec<_>>();
    assert_eq!(mine.len(), 2, "each top-level @type is noted exactly once");
    for event in &mine {
        assert_eq!(
            measurement_u64(event, "module_id"),
            u64::from(ModuleId::GLOBAL.as_u32()),
            "a top-level @type is noted under the GLOBAL module",
        );
        assert_ne!(
            measurement_u64(event, "namespace"),
            0,
            "the captured namespace is the built scope, never the empty namespace",
        );
    }
    let mut by_name = mine
        .iter()
        .map(|event| (metadata_str(event, "name").to_string(), measurement_u64(event, "arity")))
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
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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

    // The event carries the consumer as raw state — a kind tag and the bare
    // name — so the `kind:name` rendering happens here, in the observer.
    let consumers_of = |ref_name: &str| {
        let mut consumers = capture
            .find(&["fz", "compiler2", "type", "referenced"])
            .into_iter()
            .filter(|event| metadata_str(event, "ref_name") == ref_name)
            .map(|event| {
                format!(
                    "{}:{}",
                    metadata_str(&event, "consumer_kind"),
                    metadata_str(&event, "consumer")
                )
            })
            .collect::<Vec<_>>();
        consumers.sort();
        consumers
    };

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
    let box_refs = capture
        .find(&["fz", "compiler2", "type", "referenced"])
        .into_iter()
        .filter(|event| metadata_str(event, "ref_name") == "tkf_box")
        .collect::<Vec<_>>();
    assert_eq!(
        box_refs.len(),
        1,
        "the parametric type tkf_box is referenced exactly once"
    );
    assert_eq!(
        measurement_u64(&box_refs[0], "ref_arity"),
        1,
        "tkf_box is referenced at arity 1",
    );
    assert_eq!(metadata_str(&box_refs[0], "consumer_kind"), "type");
    assert_eq!(metadata_str(&box_refs[0], "consumer"), "tkf_wrapper");
    assert_eq!(
        consumers_of("tkf_box"),
        vec!["type:tkf_wrapper".to_string()],
        "the parametric type is a dep of the wrapper that applies it",
    );
}

struct RenderedTypeDef {
    name: String,
    arity: u64,
    changed: u64,
    rendered: String,
}

/// Event-time projection of `type.defined`: the event carries the raw
/// definition and the interner as opaque refs, so observers that want the
/// resolved surface render it themselves while the event's borrows are alive.
fn rendered_type_defs(tel: &ConfiguredTelemetry) -> Rc<RefCell<Vec<RenderedTypeDef>>> {
    let rendered: Rc<RefCell<Vec<RenderedTypeDef>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&rendered);
    tel.attach(
        &["fz", "compiler2", "type", "defined"],
        Box::new(move |event: &Event<'_, '_, '_>| {
            let Some(Value::Str(name)) = event.metadata.get("name") else {
                return;
            };
            let (Some(Value::U64(arity)), Some(Value::U64(changed))) =
                (event.measurements.get("arity"), event.measurements.get("changed"))
            else {
                return;
            };
            let Some(types) = event
                .metadata
                .get("types")
                .and_then(|value| value.downcast_ref::<Types>())
            else {
                return;
            };
            let Some(def) = event
                .metadata
                .get("def")
                .and_then(|value| value.downcast_ref::<crate::compiler2::typedef::TypeDef>())
            else {
                return;
            };
            sink.borrow_mut().push(RenderedTypeDef {
                name: name.to_string(),
                arity: *arity,
                changed: *changed,
                rendered: types.display(&def.ty),
            });
        }),
    );
    rendered
}

#[test]
fn compiler2_derive_type_def_pulls_a_referenced_type_and_its_wait_set_leaving_others_cold() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let rendered = rendered_type_defs(&tel);

    let mut compiler = Compiler2::new(&tel);
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
        capture
            .find(&["fz", "compiler2", "type", "defined"])
            .into_iter()
            .filter(|event| metadata_str(event, "name") == name)
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

    let mut compiler = Compiler2::new(&tel);
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
    let mut world = crate::compiler2::World::new(&tel);
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

    assert_resolved(world.drive(), "source should index protocol and owner modules");
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "top-level scope should be demandable"
    );
    assert_resolved(world.drive(), "top-level scope should prepare module definitions");

    let protocol = world.reference_module("Proof");
    assert!(
        world.demand(Job::DefineModule(protocol)),
        "protocol definition should be demandable"
    );
    assert_resolved(world.drive(), "protocol definition should publish callback facts first");

    let owner = world.reference_module("Box");
    assert!(
        world.demand(Job::DefineModule(owner)),
        "owner module definition should be demandable",
    );
    assert_resolved(
        world.drive(),
        "owner-module remote calls inside defimpl callbacks should use the live source namespace, not wait on ModuleDefined(owner)",
    );
}

#[test]
fn compiler2_nested_defimpl_resolves_protocol_and_target_through_namespace() {
    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new(&tel);
    let code_id = world.submit_code(
        Some("nested_protocol_impl_dispatch.fz".to_string()),
        include_str!("../../fixtures2/00272_protocol_impl_dispatch.fz").to_string(),
    );

    assert_resolved(
        world.drive(),
        "first drive should index the nested protocol/provider module and the caller module",
    );
    assert!(
        world.demand(Job::ScopeCode(code_id)),
        "scoping the nested protocol fixture should be demandable",
    );
    assert_resolved(
        world.drive(),
        "top-level scoping should bind nested definition macros before root demand",
    );

    let _root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(
        world.drive(),
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
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let rendered_defs = rendered_type_defs(&tel);
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let mut world = crate::compiler2::World::new(&tel);
    let code_id = world.submit_code(
        Some("protocol_domain.fz".to_string()),
        include_str!("../../fixtures2/00006_protocol_domain.fz").to_string(),
    );
    assert_resolved(
        world.drive(),
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
    assert_resolved(world.drive(), "second drive should scope the protocol source");
    assert!(
        world.demand(Job::DefineModule(protocol)),
        "defining the protocol module should be demandable",
    );
    assert_resolved(world.drive(), "third drive should define the protocol callback surface");
    let protocol_defined = outputs
        .take(Job::DefineModule(protocol))
        .expect("DefineModule job effects for the protocol surface");

    let noted = capture
        .find(&["fz", "compiler2", "type", "noted"])
        .into_iter()
        .filter(|event| metadata_str(event, "name") == "t")
        .map(|event| measurement_u64(&event, "arity"))
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
        world.drive(),
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
    let marker = expect.opaque_of(&crate::frontend::protocols::protocol_domain_tag(
        &crate::modules::identity::ModuleName::parse_dotted("Proof").expect("protocol name should parse"),
    ));
    let rendered = expect.display(&marker);
    assert_eq!(type_events[0].0, 0);
    assert_eq!(type_events[0].1, 1);
    assert_eq!(type_events[0].2, *rendered);
    assert_eq!(type_events[1].0, 1);
    assert_eq!(type_events[1].1, 1);
    assert_eq!(type_events[1].2, *rendered);
    assert_eq!(t0_def.params, Vec::new(), "t/0 should remain monomorphic");
    assert_eq!(
        t1_def.params,
        vec![TypeVarId(0)],
        "t/1 should remain a parametric type definition",
    );
    let world_marker = world
        .types_mut()
        .opaque_of(&crate::frontend::protocols::protocol_domain_tag(
            &crate::modules::identity::ModuleName::parse_dotted("Proof").expect("protocol name should parse"),
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

    assert!(
        world.demand(Job::DefineModule(owner)),
        "defining the impl owner module should be demandable",
    );
    assert_resolved(
        world.drive(),
        "defining the impl owner should revise the protocol facts",
    );
    let owner_defined = outputs
        .take(Job::DefineModule(owner))
        .expect("DefineModule job effects for the impl owner");
    assert!(
        owner_defined.contains(&presence(FactKey::ProtocolDispatch(protocol), true)),
        "adding an impl should revise the dispatch fact",
    );
    assert!(
        !owner_defined
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::TypeDefined(name) if name == &t0 || name == &t1)),
        "adding an impl should not revise protocol-domain type facts",
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
fn compiler2_index_code_defines_owned_functions_without_lowering_or_activating_bodies() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let work_graph = WorkGraphCapture::new();
    tel.attach(&["fz", "compiler2", "work_graph", "applied"], work_graph.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
    assert!(
        work_graph
            .all()
            .into_iter()
            .any(|step| step.coalesced.contains(&Job::SealSemanticClosure(root_id))),
        "work-graph telemetry should report coalesced closure checks instead of hiding duplicate wakeups"
    );

    let root_submitted = capture
        .last(&["fz", "compiler2", "root", "submitted"])
        .expect("root submitted event");
    assert_eq!(
        measurement_u64(&root_submitted, "root_id"),
        root_id.as_u32() as u64,
        "root submission should report the returned root id"
    );
    assert_eq!(
        measurement_u64(&root_submitted, "module_id"),
        ModuleId::GLOBAL.as_u32() as u64,
        "root submission should mark top-level entries with the global module id"
    );
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
    assert!(
        seed_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::RootEntry(root_id)),
        "SeedRoot should publish the root entry fact"
    );
    assert!(
        seed_outputs.iter().any(|(fact, _)| {
            *fact
                == FactKey::Activation(ActivationKey {
                    root: root_id,
                    function: main_id,
                    input: Vec::new(),
                })
        }),
        "SeedRoot should publish the entry activation"
    );
    assert!(
        seed_outputs.iter().any(|(fact, _)| {
            *fact
                == FactKey::ActivationInputs(ActivationKey {
                    root: root_id,
                    function: main_id,
                    input: Vec::new(),
                })
        }),
        "SeedRoot should publish the entry activation-input evidence fact",
    );
    assert!(
        seed_outputs.iter().any(|(fact, _)| {
            *fact
                == FactKey::Executable(ExecutableKey {
                    activation: ActivationKey {
                        root: root_id,
                        function: main_id,
                        input: Vec::new(),
                    },
                    need: ExecutableNeed::Value,
                })
        }),
        "SeedRoot should publish the entry executable request"
    );

    let closure_outputs = outputs
        .take(Job::SealSemanticClosure(root_id))
        .expect("SealSemanticClosure job effects");
    assert!(
        !closure_outputs
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::Activation(_))),
        "semantic closure should read activation facts rather than publish them"
    );
    assert!(
        closure_outputs
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::Executable(_))),
        "semantic closure should publish the executable frontier it derives from activation-local facts"
    );
    assert!(
        !closure_outputs.iter().any(|(fact, _)| {
            matches!(
                fact,
                FactKey::Activation(ActivationKey {
                    function,
                    ..
                }) if *function == foo_id
            ) || matches!(
                fact,
                FactKey::Executable(ExecutableKey {
                    activation: ActivationKey {
                        function,
                        ..
                    },
                    ..
                }) if *function == foo_id
            )
        }),
        "submitting a root should keep uncalled foo/0 semantically cold"
    );
    assert!(
        closure_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::SemanticClosed(root_id)),
        "semantic closure should publish once the seeded entry facts exist"
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
        !outputs
            .stops_matching(|job| matches!(job, Job::SealSemanticClosure(_)))
            .is_empty(),
        "root submission should run semantic closure checks while the entry frontier settles"
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
fn compiler2_macro_executable_runs_quote_unquote_on_the_source_heap() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
    assert!(compiler.demand(Job::BuildMacroExecutable(inc)));
    assert_resolved(
        compiler.drive(),
        "macro executable readiness should drive the shared backend artifact ladder",
    );
    let macro_outputs = outputs
        .take(Job::BuildMacroExecutable(inc))
        .expect("BuildMacroExecutable job effects");
    assert!(
        macro_outputs.contains(&presence(FactKey::MacroExecutable(inc), true)),
        "macro readiness should publish a first-class macro executable fact"
    );
    assert!(
        outputs
            .all()
            .into_iter()
            .any(|(fact, _)| matches!(fact, FactKey::BackendProgram(_))),
        "macro readiness should reuse the existing BackendProgram artifact, not a separate evaluator"
    );
    assert!(
        !outputs
            .all()
            .into_iter()
            .any(|(fact, _)| matches!(fact, FactKey::NativeProgram(_))),
        "compile-time macro roots should stop at backend interpreter readiness and not enter native codegen"
    );

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
    assert!(compiler.demand(Job::BuildMacroExecutable(quoted_var)));
    assert_resolved(
        compiler.drive(),
        "macro executable readiness should also handle quoted variables",
    );
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
    assert!(compiler.demand(Job::BuildMacroExecutable(forward_define)));
    assert_resolved(
        compiler.drive(),
        "macro executable readiness should lower quoted remote compiler-service calls",
    );
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
        &tel,
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
    crate::compiler2::quoted_function::derive_function_surface(
        &forwarded_group,
        crate::compiler2::CodeId::ZERO,
        Some("long_doc_forwarded.fz"),
        r#"
@doc "Removes the first matching left-side item for each item in the right list."
@spec subtract([a], [a]) :: [a]
fn subtract(left, []), do: left
fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
"#,
        &tel,
    )
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
        &tel,
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
    let forwarded_module_surface = crate::compiler2::quoted_surface::read_scope_surface(
        &forwarded_module_root,
        &crate::compiler2::quoted_surface::SurfaceSourceContext::new(
            crate::compiler2::CodeId::ZERO,
            r#"
defmodule M do
  @doc "Removes the first matching left-side item for each item in the right list."
  @spec subtract([a], [a]) :: [a]
  fn subtract(left, []), do: left
  fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
end
"#,
        ),
    )
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
            let compiler_fragment = crate::compiler2::quoted_surface::read_compiler_fragment_surface(
                &compiler_fragment_root,
                &crate::compiler2::quoted_surface::SurfaceSourceContext::new(
                    crate::compiler2::CodeId::ZERO,
                    r#"
defmodule M do
  @doc "Removes the first matching left-side item for each item in the right list."
  @spec subtract([a], [a]) :: [a]
  fn subtract(left, []), do: left
  fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
end
"#,
                ),
            )
            .expect("forwarded macro-call source should still decode as compiler fragment");
            let module_form = match compiler_fragment
                .forms
                .first()
                .expect("forwarded compiler fragment should contain one form")
            {
                crate::compiler2::quoted_surface::ScopeForm::Module(module) => module,
                other => panic!("expected compiler fragment module form, got {other:?}"),
            };
            crate::compiler2::quoted_surface::read_module_body_surface(
                module_form,
                &crate::compiler2::quoted_surface::SurfaceSourceContext::new(
                    crate::compiler2::CodeId::ZERO,
                    r#"
defmodule M do
  @doc "Removes the first matching left-side item for each item in the right list."
  @spec subtract([a], [a]) :: [a]
  fn subtract(left, []), do: left
  fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
end
"#,
                ),
            )
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
    crate::compiler2::quoted_function::derive_function_surface(
        &function.source,
        crate::compiler2::CodeId::ZERO,
        Some("forwarded_module.fz"),
        r#"
defmodule M do
  @doc "Removes the first matching left-side item for each item in the right list."
  @spec subtract([a], [a]) :: [a]
  fn subtract(left, []), do: left
  fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
end
"#,
        &tel,
    )
    .expect("whole-module forwarding should preserve nested procbin-backed @doc payloads too");
}

#[test]
fn compiler2_runtime_roots_reject_macro_entries() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
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
        outputs
            .stops_matching(
                |job| matches!(job, Job::LowerBackendProgram(id) | Job::LowerNativeProgram(id) if *id == root),
            )
            .is_empty(),
        "rejected macro runtime roots must not reach backend or native lowering for the rejected runtime root"
    );
}

#[test]
fn compiler2_runtime_refs_pull_only_the_reached_runtime_modules() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let activation = ActivationKey {
        root: root_id,
        function: main_id,
        input: Vec::new(),
    };
    let activation_job = Job::AnalyzeActivation(activation.clone());
    let effects = outputs.effects(activation_job.clone());
    let outputs = outputs
        .take(activation_job)
        .expect("AnalyzeActivation job effects for main/0");
    let callsite_facts = outputs
        .iter()
        .filter(|(fact, _)| matches!(fact, FactKey::CallSiteSummary(_)))
        .count();

    assert_eq!(
        callsite_facts, 1,
        "an activation with one reached direct call should publish one whole callsite-summary fact",
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
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());
    let returns = ReturnTypeCapture::new();
    tel.attach(&["fz", "compiler2", "return_type", "defined"], returns.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let enum_map_id = function_id_in_module(&functions, &modules, "Enum", "map", 2);
    let enum_reverse_id = function_id_in_module(&functions, &modules, "Enum", "reverse", 1);
    let list_id = module_id(&modules, "List");

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
            record.function_ref.name == "reduce"
                && record.arity == 3
                && record.owner_module_id == Some(list_id)
                && record.module_id != list_id
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

    let activation_ids = semantic
        .last(root_id)
        .activations
        .iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    assert!(
        activation_ids.contains(&main_id)
            && activation_ids.contains(&enum_reduce_id)
            && activation_ids.contains(&list_impl_reduce_id)
            && activation_ids.contains(&bridge_reducer_id)
            && activation_ids.contains(&user_reducer_id),
        "the settled root should keep the public reduce path, selected protocol impl, bridge lambda, and user reducer activation live",
    );
    assert!(
        !activation_ids.contains(&enum_map_id) && !activation_ids.contains(&enum_reverse_id),
        "unrelated Enum functions should stay outside the settled semantic closure",
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
fn compiler2_enum_reduce_operator_ref_activates_kernel_plus() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());
    let returns = ReturnTypeCapture::new();
    tel.attach(&["fz", "compiler2", "return_type", "defined"], returns.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_operator_ref.fz".to_string()),
        text: include_str!("../type_infer/fixtures/enum_reduce_operator_ref.fz").to_string(),
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
    let enum_map_id = function_id_in_module(&functions, &modules, "Enum", "map", 2);
    let kernel_plus_id = function_id_in_module(&functions, &modules, "Kernel", "+", 2);
    let list_id = module_id(&modules, "List");
    let list_impl_reduce = functions
        .all()
        .into_iter()
        .find(|record| {
            record.function_ref.name == "reduce"
                && record.arity == 3
                && record.owner_module_id == Some(list_id)
                && record.module_id != list_id
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

    let closed = semantic.last(root_id);
    let activation_ids = closed
        .activations
        .iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    assert!(
        activation_ids.contains(&main_id)
            && activation_ids.contains(&enum_reduce_id)
            && activation_ids.contains(&list_impl_reduce_id)
            && activation_ids.contains(&kernel_plus_id),
        "the settled operator-ref root should keep Kernel.+/2 live alongside the selected reduce path",
    );
    assert!(
        !activation_ids.contains(&enum_map_id),
        "unrelated Enum functions should stay outside the operator-ref semantic closure",
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
fn compiler2_materialization_projects_only_the_closed_quicksort_frontier() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());
    let materialized = MaterializedProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "materialized_program", "defined"],
        materialized.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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
        "materialization should project only the closed quicksort frontier into backend-owned data",
    );

    let program = materialized.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);
    let executable_ids = program
        .executables
        .keys()
        .map(|key| key.activation.function)
        .collect::<HashSet<_>>();

    assert_eq!(
        program.entry.activation.function, main_id,
        "the materialized program entry should stay rooted at main/0",
    );
    assert!(
        executable_ids.contains(&main_id)
            && executable_ids.contains(&qsort_id)
            && executable_ids.contains(&partition_id)
            && executable_ids.contains(&append_id),
        "materialization should keep the closed quicksort path",
    );
    assert!(
        !executable_ids.contains(&foo_id),
        "materialization should keep uncalled foo/0 out of the backend snapshot",
    );

    let (_, main_plan) = materialized_executable(&program, main_id);
    match &main_plan.body {
        crate::compiler2::LoweredBody::Clauses { clauses, entries, .. } => {
            let entry = &entries[clauses[0].entry.as_u32() as usize];
            assert!(
                matches!(entry.origin, ControlEntryOrigin::Clause),
                "materialization should preserve clause entry ids when it prunes and reindexes control entries",
            );
        }
        other => panic!("expected clause body for materialized main/0, got {other:?}"),
    }
    let (main_callsite, main_call_value) = direct_call_in_body(lowered_body(&bodies, main_id), qsort_id);
    let qsort_edge = main_plan
        .call_edges
        .get(&main_callsite)
        .unwrap_or_else(|| panic!("materialized call edge for main/0 -> qsort/1 at {main_callsite:?}"));
    let qsort_callee = local_call_target(&qsort_edge.callee);
    assert_eq!(
        qsort_callee.activation.function, qsort_id,
        "materialization should freeze main/0's qsort/1 call to an exact executable key",
    );
    assert!(
        program.executables.contains_key(qsort_callee),
        "materialized direct-call edges should point at a reachable executable plan",
    );
    assert_eq!(
        main_plan.value_types.get(&main_call_value),
        Some(&qsort_edge.return_ty),
        "materialization should retain the settled type of a direct-call result value",
    );
    assert!(
        main_plan.effects.observable && main_plan.effects.reads_allocation_stats,
        "main/0's executable effects should include dbg/heap-alloc observation through the closed call graph",
    );

    let (_, qsort_plan) = materialized_executable(&program, qsort_id);
    assert!(
        qsort_plan.effects.allocates && !qsort_plan.effects.observable,
        "qsort/1 should remain allocation-heavy but locally unobservable in the materialized plan",
    );

    let materialize_outputs = outputs
        .take(Job::MaterializeRoot(root_id))
        .expect("MaterializeRoot job effects for quicksort root");
    assert!(
        materialize_outputs
            .iter()
            .all(|(fact, _)| *fact == FactKey::MaterializedProgram(root_id)),
        "materialization should publish only the materialized-program fact and no semantic facts",
    );
    assert!(
        !outputs
            .stops_matching(|job| matches!(job, Job::MaterializeRoot(root) if *root == root_id))
            .is_empty(),
        "materialization should run as an ordinary root-owned job",
    );
    assert!(
        capture.find(&["fz", "planner"]).is_empty(),
        "Compiler2 materialization should not invoke the legacy planner pipeline",
    );
}

#[test]
fn compiler2_materialization_turns_semantically_cold_cond_arms_into_halt_stubs() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let materialized = MaterializedProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "materialized_program", "defined"],
        materialized.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("cond_specialization.fz".to_string()),
        text: include_str!("../../fixtures2/00011_cond_specialization.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "materialization should specialize semantically cold cond arms before ABI projection",
    );

    let program = materialized.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let (_, executable) = materialized_executable(&program, main_id);
    let LoweredBody::Clauses { entries, .. } = &executable.body else {
        panic!("main/0 should materialize as a clause body");
    };
    let direct_calls = entries
        .iter()
        .filter(|entry| matches!(entry.tail, LoweredTail::DirectCall { .. }))
        .count();
    let cold_halts = entries
        .iter()
        .filter(|entry| {
            matches!(
                entry.tail,
                LoweredTail::Halt {
                    ref atom
                } if atom == "compiler2_unreachable_control"
            )
        })
        .count();
    assert_eq!(
        executable.call_edges.len(),
        3,
        "materialization should prune the cold dbg arm while keeping the live Kernel.+/2, Kernel.==/2, and dbg/1 calls",
    );
    assert_eq!(
        direct_calls, 3,
        "the specialized materialized body should keep the live condition-evaluation calls plus the surviving dbg/1 tail",
    );
    assert!(
        cold_halts >= 1,
        "materialization should turn impossible local-control arms into explicit halt stubs",
    );
}

#[test]
fn compiler2_materialization_freezes_only_the_selected_enum_reduce_path() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let materialized = MaterializedProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "materialized_program", "defined"],
        materialized.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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
        "materialization should freeze only the selected runtime, protocol, and callable reduce path",
    );

    let program = materialized.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let enum_reduce_id = function_id_in_module(&functions, &modules, "Enum", "reduce", 3);
    let enum_map_id = function_id_in_module(&functions, &modules, "Enum", "map", 2);
    let enum_reverse_id = function_id_in_module(&functions, &modules, "Enum", "reverse", 1);
    let list_id = module_id(&modules, "List");
    let main_generated = generated_functions_owned_by(&functions, main_id);
    let user_reducer_id = main_generated[0].function_id;
    let enum_generated = generated_functions_owned_by(&functions, enum_reduce_id);
    let bridge_reducer_id = enum_generated[0].function_id;
    let list_impl_reduce_id = functions
        .all()
        .into_iter()
        .find(|record| {
            record.function_ref.name == "reduce"
                && record.arity == 3
                && record.owner_module_id == Some(list_id)
                && record.module_id != list_id
        })
        .unwrap_or_else(|| panic!("function.defined for the selected List-backed protocol callback"))
        .function_id;

    let executable_ids = program
        .executables
        .keys()
        .map(|key| key.activation.function)
        .collect::<HashSet<_>>();
    assert!(
        executable_ids.contains(&main_id)
            && executable_ids.contains(&enum_reduce_id)
            && executable_ids.contains(&list_impl_reduce_id)
            && executable_ids.contains(&bridge_reducer_id)
            && executable_ids.contains(&user_reducer_id),
        "materialization should keep the selected public reduce path, protocol callback, bridge lambda, and user reducer",
    );
    assert!(
        !executable_ids.contains(&enum_map_id) && !executable_ids.contains(&enum_reverse_id),
        "materialization should keep unrelated Enum paths cold",
    );

    let enum_reduce_edges = &program
        .executables
        .iter()
        .find(|(key, _)| key.activation.function == enum_reduce_id)
        .expect("materialized executable for Enum.reduce/3")
        .1
        .call_edges;
    assert!(
        enum_reduce_edges
            .values()
            .any(|edge| local_call_target(&edge.callee).activation.function == list_impl_reduce_id),
        "materialization should freeze Enum.reduce/3's protocol call to the selected List-backed callback executable",
    );

    let bridge_edges = &program
        .executables
        .iter()
        .find(|(key, _)| key.activation.function == bridge_reducer_id)
        .expect("materialized executable for the bridge reducer lambda")
        .1
        .call_edges;
    assert!(
        bridge_edges
            .values()
            .any(|edge| local_call_target(&edge.callee).activation.function == user_reducer_id),
        "materialization should freeze the bridge reducer call to the exact user reducer executable",
    );
    let (_, bridge_plan) = materialized_executable(&program, bridge_reducer_id);
    assert!(
        !bridge_plan.effects.calls_opaque,
        "once the reducer closure target is known, the bridge lambda should not carry an opaque-call effect",
    );

    let materialize_outputs = outputs
        .take(Job::MaterializeRoot(root_id))
        .expect("MaterializeRoot job effects for Enum.reduce root");
    assert!(
        materialize_outputs
            .iter()
            .all(|(fact, _)| *fact == FactKey::MaterializedProgram(root_id)),
        "materialization should publish only the materialized-program fact and no semantic facts",
    );
    assert!(
        capture.find(&["fz", "planner"]).is_empty(),
        "Compiler2 materialization should not invoke the legacy planner pipeline",
    );
}

#[test]
fn compiler2_abi_ready_makes_tuple_field_return_delivery_explicit_for_quicksort() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let abi_ready = AbiReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "abi_ready_program", "defined"],
        abi_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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
        "ABI-ready projection should derive tuple-field return ABI from the closed quicksort frontier",
    );

    let program = abi_ready.last(root_id).program;
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let foo_id = function_id(&functions, "foo", 0);
    let (_, qsort_plan) = abi_ready_executable(&program, qsort_id);
    let partition_edge = qsort_plan
        .call_edges
        .values()
        .find(|edge| local_call_target(&edge.callee).activation.function == partition_id)
        .expect("ABI-ready call edge for partition/4");
    assert_eq!(
        partition_edge.return_abi,
        ReturnAbi::TupleFields(vec![AbiValueRepr::ValueRef, AbiValueRepr::ValueRef]),
        "the partition/4 edge should carry the two-field tuple delivery contract explicitly",
    );
    assert!(
        program.executables.keys().all(|key| key.activation.function != foo_id),
        "ABI-ready projection should stay closed over the reached quicksort frontier and keep foo/0 cold",
    );
    assert!(
        program.callable_entries.is_empty(),
        "quicksort plus an uncalled foo/0 should not manufacture callable-entry obligations",
    );

    let abi_outputs = outputs
        .take(Job::DeriveAbiReady(root_id))
        .expect("DeriveAbiReady job effects for quicksort root");
    assert!(
        abi_outputs
            .iter()
            .all(|(fact, _)| *fact == FactKey::AbiReadyProgram(root_id)),
        "ABI-ready projection should publish only the ABI-ready fact",
    );
    assert!(
        capture.find(&["fz", "planner"]).is_empty() && capture.find(&["fz", "codegen"]).is_empty(),
        "deriving ABI facts should not wake the legacy planner or codegen pipelines",
    );
    assert!(
        capture
            .find(&["fz", "compiler2", "abi_ready_program", "defined"])
            .into_iter()
            .all(|event| event.metadata.len() == 0),
        "generic capture should not durable-copy opaque ABI-ready metadata",
    );
}

#[test]
fn compiler2_abi_ready_boxes_heap_projection_returns_at_function_boundaries() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let abi_ready = AbiReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "abi_ready_program", "defined"],
        abi_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_projection_boundary_abi.fz".to_string()),
        text: include_str!("../../fixtures2/00012_projection_boundary_abi.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "ABI-ready projection should keep heap observations boxed across function boundaries",
    );

    let tuple_first_id = function_id(&functions, "tuple_first", 1);
    let map_first_id = function_id(&functions, "map_first", 1);
    let program = abi_ready.last(root_id).program;

    for function in [tuple_first_id, map_first_id] {
        let (_, executable) = abi_ready_executable(&program, function);
        assert_eq!(
            executable.return_abi,
            ReturnAbi::Value(AbiValueRepr::ValueRef),
            "projection-only helpers should box their boundary return lane instead of exporting a guessed raw scalar ABI",
        );
    }
}

#[test]
fn compiler2_abi_ready_derives_only_the_closed_enum_reduce_callable_entries() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let abi_ready = AbiReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "abi_ready_program", "defined"],
        abi_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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
    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "ABI-ready projection should publish only the reducer callable entries that survive the settled Enum.reduce path: {outcome:?}; diagnostic={message}"
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

    let program = abi_ready.last(root_id).program;
    let callable_functions = program
        .callable_entries
        .iter()
        .map(|entry| entry.target.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_functions,
        HashSet::from([user_reducer_id, bridge_reducer_id]),
        "the settled Enum.reduce path should need one callable entry for the bridge reducer and one for the user reducer",
    );

    let user_entries = abi_ready_callable_entries(&program, user_reducer_id);
    assert!(
        !user_entries.is_empty(),
        "the user reducer should surface at least one closed callable entry",
    );
    assert!(
        user_entries.iter().all(|entry| entry.capture_count == 0),
        "the user reducer should stay a thin zero-capture callable value across every settled callable entry",
    );
    assert!(
        user_entries
            .iter()
            .all(|entry| entry.target.need == ExecutableNeed::Value),
        "callable entries should always target value-return executables",
    );
    assert!(
        user_entries
            .iter()
            .all(|entry| entry.target.activation.input.len() == 2),
        "user reducer callable entries should specialize over two runtime call arguments",
    );
    assert!(
        user_entries
            .iter()
            .any(|entry| entry.return_abi == ReturnAbi::Value(AbiValueRepr::RawInt)),
        "the closed user reducer callable inventory should preserve a raw integer accumulator return lane",
    );
    assert!(
        user_entries
            .iter()
            .all(|entry| program.executables.contains_key(&entry.target)),
        "callable-entry targets must already exist in the closed executable frontier",
    );

    let bridge_entries = abi_ready_callable_entries(&program, bridge_reducer_id);
    assert!(
        !bridge_entries.is_empty(),
        "the bridge reducer should surface at least one closed callable entry",
    );
    assert!(
        bridge_entries.iter().all(|entry| entry.capture_count == 1),
        "the bridge reducer should keep the captured user reducer in every callable-entry contract",
    );
    assert!(
        bridge_entries
            .iter()
            .all(|entry| entry.target.need == ExecutableNeed::Value),
        "bridge reducer callable entries should still target value-return executables",
    );
    assert!(
        bridge_entries
            .iter()
            .all(|entry| entry.target.activation.input.len() == 3),
        "bridge reducer callable entries should include one capture plus two runtime args",
    );
    assert!(
        bridge_entries
            .iter()
            .all(|entry| entry.return_abi == ReturnAbi::Value(AbiValueRepr::ValueRef)),
        "the bridge reducer should return the tagged reduce-step tuple as an ordinary value reference",
    );
    assert!(
        bridge_entries
            .iter()
            .all(|entry| program.executables.contains_key(&entry.target)),
        "bridge callable-entry targets must already exist in the closed executable frontier",
    );
}

#[test]
fn compiler2_abi_ready_keeps_returned_suspend_continuation_callable_entry() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let abi_ready = AbiReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "abi_ready_program", "defined"],
        abi_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_suspend_callable_frontier.fz".to_string()),
        text: r#"
fn main() do
  Enumerable.reduce([1, 2, 3], {:suspend, 0}, fn (x, acc) -> {:cont, acc + x} end)
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

    assert_resolved(
        compiler.drive(),
        "returned suspend continuations should be closed before ABI-ready callable inventory is derived",
    );

    let list_reduce_id = function_id_in_module(&functions, &modules, "List", "reduce", 3);
    let continuation_id = generated_functions_owned_by(&functions, list_reduce_id)
        .into_iter()
        .find(|record| record.arity == 0)
        .expect("List.reduce suspend branch should generate a zero-arity continuation")
        .function_id;

    let program = abi_ready.last(root_id).program;
    let continuation_entries = abi_ready_callable_entries(&program, continuation_id);
    assert!(
        continuation_entries.iter().all(|entry| entry.capture_count == 3),
        "the suspend continuation captures the list, accumulator, and reducer"
    );
    assert!(
        continuation_entries
            .iter()
            .all(|entry| entry.target.need == ExecutableNeed::Value),
        "callable entries should target value-return executables"
    );
    assert!(
        continuation_entries
            .iter()
            .all(|entry| program.executables.contains_key(&entry.target)),
        "returned continuation callable-entry targets must already exist in the closed executable frontier",
    );
}

#[test]
fn compiler2_abi_ready_matches_callable_entries_by_canonical_activation_key() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let abi_ready = AbiReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "abi_ready_program", "defined"],
        abi_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/callable_canonical_capture_frontier.fz".to_string()),
        text: r#"
fn reduce_plain([], acc, _reducer), do: acc
fn reduce_plain([head | tail], acc, reducer), do: reduce_plain(tail, reducer.(head, acc), reducer)

fn main() do
  predicate = fn x -> x > 2 end
  reducer = fn (entry, acc) ->
    if predicate.(entry), do: acc + 1, else: acc
  end

  reduce_plain([1, 2, 3, 4], 0, reducer)
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

    assert_resolved(
        compiler.drive(),
        "callable entries should resolve through canonical activation keys, not raw capture Ty ids",
    );

    let main_id = function_id(&functions, "main", 0);
    let reducer_id = generated_functions_owned_by(&functions, main_id)
        .into_iter()
        .find(|record| record.arity == 2)
        .expect("main should generate the captured reducer closure")
        .function_id;

    let program = abi_ready.last(root_id).program;
    let reducer_entries = abi_ready_callable_entries(&program, reducer_id);
    assert!(
        reducer_entries.iter().all(|entry| entry.capture_count == 1),
        "the reducer callable captures the predicate closure"
    );
    assert!(
        reducer_entries
            .iter()
            .all(|entry| program.executables.contains_key(&entry.target)),
        "captured callable-entry targets must resolve to canonical executable keys in the closed frontier",
    );
}

#[test]
fn compiler2_abi_ready_does_not_publish_unused_callable_constructors() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let abi_ready = AbiReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "abi_ready_program", "defined"],
        abi_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/unused_callable_constructor_frontier.fz".to_string()),
        text: r#"
fn ignore(_fun), do: 0

fn main() do
  fun = fn x -> x + 1 end
  ignore(fun)
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

    assert_resolved(
        compiler.drive(),
        "constructing and passing a callable should not publish its executable unless a call or escape demands it",
    );

    let main_id = function_id(&functions, "main", 0);
    let lambda_id = generated_functions_owned_by(&functions, main_id)
        .into_iter()
        .next()
        .expect("main should generate the unused closure body")
        .function_id;

    let program = abi_ready.last(root_id).program;
    assert!(
        program
            .callable_entries
            .iter()
            .all(|entry| entry.target.activation.function != lambda_id),
        "callable constructors should not create callable-entry inventory without a demand site",
    );
    assert!(
        program
            .executables
            .keys()
            .all(|key| key.activation.function != lambda_id),
        "the unused closure body should stay outside the closed executable frontier",
    );
}

#[test]
fn compiler2_materialization_projects_variadic_extern_signatures_and_callsite_marshals() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let materialized = MaterializedProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "materialized_program", "defined"],
        materialized.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "variadic extern calls should settle to a backend-ready executable and callsite marshal plan",
    );

    let program = materialized.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let open_id = function_id(&functions, "libc::open", 2);
    let (_, open_plan) = materialized_executable(&program, open_id);
    let (_, main_plan) = materialized_executable(&program, main_id);

    match &open_plan.body {
        LoweredBody::Extern { signature } => {
            assert_eq!(signature.symbol, "open");
            assert_eq!(signature.params, vec![ExternTy::CString, ExternTy::I64]);
            assert!(signature.variadic);
            assert_eq!(signature.ret, ExternTy::I64);
        }
        other => panic!("expected variadic extern body for libc::open, got {other:?}"),
    }

    let open_edge = main_plan
        .call_edges
        .values()
        .find(|edge| local_call_target(&edge.callee).activation.function == open_id)
        .expect("materialized call edge for libc::open");
    assert_eq!(
        open_edge.extern_marshals.as_deref(),
        Some(&[ExternTy::CString, ExternTy::I64, ExternTy::I64][..]),
        "materialization should freeze the exact C marshal classes for a variadic extern callsite",
    );
    assert!(
        main_plan.effects.observable,
        "calling a variadic extern should make the executable plan externally observable",
    );
}

#[test]
fn compiler2_lowering_rejects_unbound_local_function_refs_before_artifact_planning() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_emission_ready_projects_only_the_closed_quicksort_inventory() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let emission_ready = EmissionReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "emission_ready_program", "defined"],
        emission_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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
        "emission-ready projection should publish only the closed quicksort executable inventory",
    );

    let program = emission_ready.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);
    let executable_ids = program
        .executables
        .iter()
        .map(|executable| executable.key.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        program.executables[program.entry].key.activation.function, main_id,
        "the emission-ready entry should point at the main/0 executable inventory slot",
    );
    assert!(
        executable_ids.contains(&main_id)
            && executable_ids.contains(&qsort_id)
            && executable_ids.contains(&partition_id)
            && executable_ids.contains(&append_id),
        "emission inventory should keep the closed quicksort executable frontier",
    );
    assert!(
        !executable_ids.contains(&foo_id),
        "emission inventory should keep uncalled foo/0 out of the backend handoff",
    );
    assert!(
        program.callable_entries.is_empty(),
        "quicksort should not produce callable-entry inventory",
    );

    let (_, main_exec) = emission_ready_executable(&program, main_id);
    let qsort_edge = main_exec
        .call_edges
        .iter()
        .find(|edge| {
            program.executables[*local_call_target(&edge.callee)]
                .key
                .activation
                .function
                == qsort_id
        })
        .expect("emission-ready main/0 -> qsort/1 call edge");
    assert_eq!(
        program.executables[*local_call_target(&qsort_edge.callee)]
            .key
            .activation
            .function,
        qsort_id,
        "emission-ready call edges should resolve through executable inventory ids",
    );

    let emission_outputs = outputs
        .take(Job::DeriveEmissionReady(root_id))
        .expect("DeriveEmissionReady job effects for quicksort root");
    assert!(
        emission_outputs
            .iter()
            .all(|(fact, _)| *fact == FactKey::EmissionReadyProgram(root_id)),
        "emission-ready projection should publish only the emission-ready fact",
    );
    assert!(
        capture.find(&["fz", "planner"]).is_empty() && capture.find(&["fz", "codegen"]).is_empty(),
        "deriving emission inventory should not wake the legacy planner or codegen pipelines",
    );
    assert!(
        capture
            .find(&["fz", "compiler2", "emission_ready_program", "defined"])
            .into_iter()
            .all(|event| event.metadata.len() == 0),
        "generic capture should not durable-copy opaque emission-ready metadata",
    );
}

#[test]
fn compiler2_emission_ready_includes_the_required_enum_reduce_callable_entries() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let emission_ready = EmissionReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "emission_ready_program", "defined"],
        emission_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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
        "emission-ready projection should inventory the surviving Enum.reduce callable entries",
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

    let program = emission_ready.last(root_id).program;
    let callable_functions = program
        .callable_entries
        .iter()
        .map(|entry| program.executables[entry.target].key.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_functions,
        HashSet::from([user_reducer_id, bridge_reducer_id]),
        "the emission-ready callable inventory should contain exactly the user reducer and bridge reducer entries",
    );

    let user_entries = emission_ready_callable_entries(&program, user_reducer_id);
    assert!(
        !user_entries.is_empty(),
        "the user reducer should keep at least one emission-ready callable entry",
    );
    assert!(
        user_entries.iter().all(|(_, entry)| entry.capture_count == 0),
        "the user reducer should stay a zero-capture callable entry",
    );
    assert!(
        user_entries
            .iter()
            .all(|(_, entry)| program.executables[entry.target].key.activation.input.len() == 2),
        "user reducer executable inventory slots should specialize over two runtime call arguments",
    );
    assert!(
        user_entries.iter().any(|(_, entry)| {
            program.executables[entry.target].return_abi == ReturnAbi::Value(AbiValueRepr::RawInt)
        }),
        "the emission-ready user reducer inventory should preserve a raw integer return lane",
    );

    let bridge_entries = emission_ready_callable_entries(&program, bridge_reducer_id);
    assert!(
        !bridge_entries.is_empty(),
        "the bridge reducer should keep at least one emission-ready callable entry",
    );
    assert!(
        bridge_entries.iter().all(|(_, entry)| entry.capture_count == 1),
        "the bridge reducer should keep its captured reducer in the callable-entry inventory",
    );
    assert!(
        bridge_entries
            .iter()
            .all(|(_, entry)| program.executables[entry.target].key.activation.input.len() == 3),
        "bridge reducer executable inventory slots should include one capture plus two runtime args",
    );
    assert!(
        bridge_entries.iter().all(|(_, entry)| {
            program.executables[entry.target].return_abi == ReturnAbi::Value(AbiValueRepr::ValueRef)
        }),
        "the bridge reducer executable inventory should return the tagged reduce-step tuple as a value reference",
    );
}

#[test]
fn compiler2_emission_ready_revision_stays_stable_for_identical_recompute() {
    let tel = ConfiguredTelemetry::new();
    let emission_ready = EmissionReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "emission_ready_program", "defined"],
        emission_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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
        "initial emission-ready derivation should settle for quicksort",
    );
    assert!(
        compiler.demand(Job::DeriveEmissionReady(root_id)),
        "explicitly re-demanding unchanged emission inventory should enqueue one fresh derivation",
    );
    assert_resolved(
        compiler.drive(),
        "re-deriving unchanged emission inventory should resolve without bumping the revision",
    );

    let records = emission_ready.records(root_id);
    assert_eq!(
        records.len(),
        2,
        "the emission-ready program should have one initial definition and one unchanged re-derivation",
    );
    assert!(
        records[0].changed && !records[1].changed,
        "initial derivation should be changed=true; re-derivation of identical state should be changed=false",
    );
    assert_eq!(
        records[0].program, records[1].program,
        "identical emission-ready recomputation should produce byte-for-byte equal program facts",
    );
}

#[test]
fn compiler2_artifact_ladder_consumes_only_the_previous_rung() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
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
        "artifact projection should settle as a one-way ladder over the closed quicksort root",
    );

    let materialize = outputs.effects(Job::MaterializeRoot(root_id));
    assert_eq!(
        materialize.reads,
        vec![settled_fact(FactKey::SemanticClosed(root_id))],
        "materialization should consume only the closed semantic root fact",
    );
    assert!(
        materialize.waits.is_empty(),
        "materialization should not stay blocked once the closure is sealed",
    );
    assert_eq!(
        materialize.follow_up,
        vec![Job::DeriveAbiReady(root_id)],
        "materialization should hand off directly to the ABI-ready projection",
    );
    assert!(
        materialize
            .outputs
            .iter()
            .all(|fact| *fact == FactKey::MaterializedProgram(root_id)),
        "materialization should publish only the materialized artifact fact",
    );

    let abi_ready = outputs.effects(Job::DeriveAbiReady(root_id));
    assert_eq!(
        abi_ready.reads,
        vec![settled_fact(FactKey::MaterializedProgram(root_id))],
        "ABI-ready derivation should consume only the materialized artifact fact",
    );
    assert!(
        abi_ready.waits.is_empty(),
        "ABI-ready derivation should not reopen semantic or reachability work",
    );
    assert_eq!(
        abi_ready.follow_up,
        vec![Job::DeriveEmissionReady(root_id)],
        "ABI-ready derivation should hand off directly to emission-ready inventory",
    );
    assert!(
        abi_ready
            .outputs
            .iter()
            .all(|fact| *fact == FactKey::AbiReadyProgram(root_id)),
        "ABI-ready derivation should publish only the ABI-ready artifact fact",
    );

    let emission_ready = outputs.effects(Job::DeriveEmissionReady(root_id));
    assert_eq!(
        emission_ready.reads,
        vec![settled_fact(FactKey::AbiReadyProgram(root_id))],
        "emission-ready derivation should consume only the ABI-ready artifact fact",
    );
    assert!(
        emission_ready.waits.is_empty(),
        "emission-ready derivation should not ask semantic, type, or reachability questions upstream of the artifact ladder",
    );
    assert_eq!(
        emission_ready.follow_up,
        vec![Job::LowerBackendProgram(root_id)],
        "emission-ready derivation should hand off directly to backend lowering",
    );
    assert!(
        emission_ready
            .outputs
            .iter()
            .all(|fact| *fact == FactKey::EmissionReadyProgram(root_id)),
        "emission-ready derivation should publish only the emission-ready artifact fact",
    );

    let backend = outputs.effects(Job::LowerBackendProgram(root_id));
    assert_eq!(
        backend.reads,
        vec![settled_fact(FactKey::EmissionReadyProgram(root_id))],
        "backend lowering should consume only the emission-ready artifact fact",
    );
    assert!(
        backend.waits.is_empty(),
        "backend lowering should not reopen semantic or planner discovery upstream of the artifact ladder",
    );
    assert!(
        backend.follow_up == vec![Job::LowerNativeProgram(root_id)],
        "backend lowering should hand off directly to the native handoff projection",
    );
    assert!(
        backend
            .outputs
            .iter()
            .all(|fact| *fact == FactKey::BackendProgram(root_id)),
        "backend lowering should publish only the backend handoff fact",
    );

    let native = outputs.effects(Job::LowerNativeProgram(root_id));
    assert_eq!(
        native.reads,
        vec![settled_fact(FactKey::BackendProgram(root_id))],
        "native lowering should consume only the backend handoff fact",
    );
    assert!(
        native.waits.is_empty(),
        "native lowering should not reopen semantic, planner, or backend discovery work upstream of the artifact ladder",
    );
    assert!(
        native.follow_up.is_empty(),
        "native lowering should be the end of the current Compiler2-owned artifact ladder",
    );
    assert!(
        native
            .outputs
            .iter()
            .all(|fact| *fact == FactKey::NativeProgram(root_id)),
        "native lowering should publish only the native handoff fact",
    );
}

#[test]
fn compiler2_seed_root_does_not_depend_on_its_own_root_fact() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let backend = BackendProgramCapture::new();
    tel.attach(&["fz", "compiler2", "backend_program", "defined"], backend.handler());

    let mut compiler = Compiler2::new(&tel);
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
        "backend lowering should keep only the closed quicksort frontier and attach settled call targets",
    );

    let program = backend.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);

    let executable_ids = program
        .executables
        .iter()
        .map(|executable| executable.key.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        program.executables[program.entry].key.activation.function, main_id,
        "the backend-program entry should still point at the main/0 executable inventory slot",
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
        program.callable_entries.is_empty(),
        "quicksort should not manufacture callable-entry inventory in the backend handoff",
    );

    let (_, main_exec) = backend_executable(&program, main_id);
    let call = backend_direct_call(main_exec, &program, qsort_id);
    match call {
        BackendTail::DirectCall { callee, args, .. } => {
            assert_eq!(
                program.executables[*local_call_target(callee)].key.activation.function,
                qsort_id,
                "backend direct-call steps should point at settled executable inventory indices",
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
    assert!(
        capture
            .find(&["fz", "compiler2", "backend_program", "defined"])
            .into_iter()
            .all(|event| event.metadata.len() == 0),
        "generic capture should not durable-copy opaque backend-program metadata",
    );
}

#[test]
fn compiler2_backend_program_attaches_the_closed_enum_reduce_callable_boundaries() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let backend = BackendProgramCapture::new();
    tel.attach(&["fz", "compiler2", "backend_program", "defined"], backend.handler());

    let mut compiler = Compiler2::new(&tel);
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
        "backend lowering should carry only the callable entries that survive the closed Enum.reduce path",
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
    let callable_functions = program
        .callable_entries
        .iter()
        .map(|entry| program.executables[entry.target].key.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_functions,
        HashSet::from([user_reducer_id, bridge_reducer_id]),
        "the backend callable-entry inventory should keep exactly the user reducer and bridge reducer entries",
    );

    assert!(
        program.callable_entries.iter().all(|entry| {
            let function = program.executables[entry.target].key.activation.function;
            function == user_reducer_id || function == bridge_reducer_id
        }),
        "backend callable-entry inventory should be the single source of callable dispatch obligations",
    );
}

#[test]
fn compiler2_backend_program_preserves_variadic_extern_wire_classes() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let backend = BackendProgramCapture::new();
    tel.attach(&["fz", "compiler2", "backend_program", "defined"], backend.handler());

    let mut compiler = Compiler2::new(&tel);
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

    let call = backend_direct_call(main_exec, &program, open_id);
    match call {
        BackendTail::DirectCall {
            callee,
            args,
            extern_marshals,
            ..
        } => {
            assert_eq!(
                program.executables[*local_call_target(callee)].key.activation.function,
                open_id,
                "backend extern calls should still target the settled extern executable inventory slot",
            );
            assert_eq!(
                extern_marshals.as_deref(),
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
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

#[test]
fn compiler2_native_program_matches_tuple_field_call_continuations_to_the_callee_return_abi() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        2,
        "the rooted quicksort frontier reaches two qsort executables, and each should own one tuple-field continuation from partition/4",
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
        assert_eq!(
            tuple_field_cont.param_reprs.len(),
            3,
            "the tuple-field continuation should still carry exactly one captured pivot lane after the returned fields",
        );
        assert_eq!(
            entry_block.params.len(),
            tuple_field_cont.param_reprs.len(),
            "tuple-field continuations should publish one entry param per delivered field plus one per capture; they should not smuggle a synthetic tuple slot into the fz IR entry block",
        );
    }
}

#[test]
fn compiler2_native_program_keeps_the_closed_enum_reduce_callable_entries() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should carry only the callable entries that survive the closed Enum.reduce path: {outcome:?}; diagnostic={message}"
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
    let callable_functions = program
        .callable_boundaries
        .iter()
        .map(|entry| entry.target.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_functions,
        HashSet::from([user_reducer_id, bridge_reducer_id]),
        "the native callable-boundary inventory should keep exactly the user reducer and bridge reducer entries",
    );

    let used_entries = native_callable_boundary_uses(&program);
    let expected_entries = program
        .callable_boundaries
        .iter()
        .filter_map(|entry| {
            matches!(
                entry.target.activation.function,
                id if id == user_reducer_id || id == bridge_reducer_id
            )
            .then_some(entry.id())
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        used_entries, expected_entries,
        "native closure values should point at exactly the callable-boundary obligations that survive the closed Enum.reduce path",
    );
}

#[test]
fn compiler2_native_program_keeps_distinct_callable_boundaries_for_same_surface_when_capture_identity_differs() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/callable_boundary_capture_identity.fz".to_string()),
        text: r#"
fn reduce_plain([], acc, _reducer), do: acc
fn reduce_plain([head | tail], acc, reducer), do: reduce_plain(tail, reducer.(head, acc), reducer)

fn gt2(x), do: x > 2
fn even(x), do: (x % 2) == 0

fn make_reducer(predicate) do
  fn (entry, acc) ->
    if predicate.(entry), do: acc + 1, else: acc
  end
end

fn main() do
  xs = [1, 2, 3, 4]
  reduce_plain(xs, 0, make_reducer(gt2)) + reduce_plain(xs, 0, make_reducer(even))
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

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "native lowering should preserve distinct callable-boundary identities when the same reducer surface captures different predicates: {outcome:?}; diagnostic={message}"
        );
    }

    let make_reducer_id = function_id(&functions, "make_reducer", 1);
    let reducer_id = generated_functions_owned_by(&functions, make_reducer_id)
        .into_iter()
        .find(|record| record.arity == 2)
        .expect("make_reducer/1 should generate the reducer lambda")
        .function_id;

    let program = native.last(root_id).program;
    let reducer_boundaries = program
        .callable_boundaries
        .iter()
        .filter(|entry| entry.target.activation.function == reducer_id)
        .collect::<Vec<_>>();
    assert!(
        reducer_boundaries.iter().all(|entry| entry.capture_count == 1),
        "the reducer callable should capture exactly one predicate closure",
    );

    let capture_identities = reducer_boundaries
        .iter()
        .map(|entry| entry.target.activation.input[..entry.capture_count].to_vec())
        .collect::<HashSet<_>>();
    assert_eq!(
        capture_identities.len(),
        2,
        "the reducer lambda should keep two distinct captured predicate identities in the native callable-boundary inventory",
    );

    let mut outward_surface_groups: Vec<Vec<&crate::compiler2::artifact::NativeCallableBoundary>> = Vec::new();
    for boundary in &reducer_boundaries {
        if let Some(group) = outward_surface_groups.iter_mut().find(|group| {
            let representative = group[0];
            representative.arg_reprs == boundary.arg_reprs && representative.return_abi == boundary.return_abi
        }) {
            group.push(*boundary);
        } else {
            outward_surface_groups.push(vec![*boundary]);
        }
    }
    assert!(
        outward_surface_groups.iter().any(|group| {
            group
                .iter()
                .map(|entry| entry.target.activation.input[..entry.capture_count].to_vec())
                .collect::<HashSet<_>>()
                .len()
                == 2
        }),
        "at least one shared outward callable surface should keep both predicate capture identities distinct instead of collapsing them to one surface-only boundary",
    );

    let used_boundaries = native_callable_boundary_uses(&program);
    let used_reducer_boundaries = reducer_boundaries
        .iter()
        .copied()
        .filter(|entry| used_boundaries.contains(&entry.id()))
        .collect::<Vec<_>>();
    assert_eq!(
        used_reducer_boundaries
            .iter()
            .map(|entry| entry.target.activation.input[..entry.capture_count].to_vec())
            .collect::<HashSet<_>>()
            .len(),
        2,
        "native callable values should keep both captured predicate identities alive instead of collapsing them to one surface-only boundary",
    );
}

#[test]
fn compiler2_native_program_joins_callable_resume_before_materializing_closure_call() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        .map(|entry| entry.target.activation.function)
        .collect::<HashSet<_>>();
    assert!(
        callable_functions.contains(&add_a_id) && callable_functions.contains(&add_b_id),
        "native callable inventory should include both concrete functions flowing through the case join",
    );

    assert!(
        native_closure_call_targets(&program)
            .into_iter()
            .any(|target| target.is_none()),
        "opaque joined function values should stay explicit closure-call seams with no exact direct target",
    );
}

#[test]
fn compiler2_native_program_marks_settled_singleton_closure_calls_with_exact_targets() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    let program = native.last(root_id).program;
    assert!(
        native_closure_call_targets(&program)
            .into_iter()
            .any(|target| target.is_some()),
        "singleton closure-lits should carry their exact direct target through native lowering",
    );
}

#[test]
fn compiler2_native_program_preserves_variadic_extern_wrappers_and_marshals() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_native_program_revision_stays_stable_for_identical_recompute() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!("initial native lowering should settle for quicksort: {outcome:?}; diagnostic={message}");
    }
    assert!(
        compiler.demand(Job::LowerNativeProgram(root_id)),
        "explicitly re-demanding unchanged native lowering should enqueue one fresh derivation",
    );
    let outcome = compiler.drive();
    if !matches!(outcome, DriveOutcome::Resolved) {
        let message = capture
            .last(&["fz", "diag", "error"])
            .map(|event| metadata_str(&event, "message").to_string())
            .unwrap_or_else(|| "<missing diagnostic>".to_string());
        panic!(
            "re-lowering unchanged native state should resolve without bumping the revision: {outcome:?}; diagnostic={message}"
        );
    }

    let records = native.records(root_id);
    assert_eq!(
        records.len(),
        2,
        "the native program should have one initial definition and one unchanged re-derivation",
    );
    assert!(
        records[0].changed && !records[1].changed,
        "initial derivation should be changed=true; re-derivation of identical state should be changed=false",
    );
    assert!(
        native_programs_match(&records[0].program, &records[1].program),
        "identical native-program recomputation should reproduce the same closed handoff facts",
    );
}

#[test]
fn compiler2_native_program_jit_runs_quicksort_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let halt = compiled.run(&tel, program.entry);
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
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    // The native-compile span exists to make machine-code cost measurable, so
    // every define carries the emitted code size.
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
    for stop in &define_stops {
        let code_bytes = match stop.measurements.get("code_bytes") {
            Some(Value::U64(n)) => *n,
            other => panic!("define_function stop must carry code_bytes: {other:?}"),
        };
        assert!(
            code_bytes >= 1,
            "native compile emits machine code, so code_bytes must be positive"
        );
    }
}

#[test]
fn compiler2_native_program_jit_runs_spawn_then_receive_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
        .map(|boundary_id| {
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
                .target
                .activation
                .function
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_targets,
        HashSet::from([child_id]),
        "native closure values should resolve to the one closed callable boundary for child/0",
    );

    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run(&tel, program.entry),
        42,
        "compiler2-owned native codegen should preserve Compiler2 spawn/receive behavior through the callable-entry seam",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native spawn/receive JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_native_program_jit_runs_spawn_receive_and_assert_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        compiled.run(&tel, program.entry),
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
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        compiled.run(&tel, program.entry),
        15,
        "compiler2-owned native codegen should preserve the closed Enum.reduce result from Compiler2",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2-native Enum.reduce JIT should not reopen legacy planning or type inference",
    );
}

#[test]
fn compiler2_native_program_jit_runs_enum_map_reduce_with_direct_closure_targets() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let dbg = DbgCapture::new();
    tel.attach(&["fz", "runtime", "dbg"], dbg.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let main_id = function_id(&functions, "main", 0);
    let enum_map_reduce_id = function_id_in_module(&functions, &modules, "Enum", "map_reduce", 3);
    let enum_map_reduce_list_id = function_id_in_module(&functions, &modules, "Enum", "map_reduce_list", 3);
    let reducer_id = generated_functions_owned_by(&functions, main_id)
        .into_iter()
        .next()
        .expect("generated reducer")
        .function_id;
    eprintln!("main generated reducer fn_id={}", reducer_id.as_u32());
    eprintln!(
        "enum_map_reduce fn_id={} map_reduce_list fn_id={}",
        enum_map_reduce_id.as_u32(),
        enum_map_reduce_list_id.as_u32()
    );
    let reducer_executable_fn = native_executable_fn(&program, reducer_id);
    let map_reduce_executable_fn = native_executable_fn(&program, enum_map_reduce_id);
    let map_reduce_list_executable_fn = native_executable_fn(&program, enum_map_reduce_list_id);
    let mut extra_fns = vec![
        reducer_executable_fn.0,
        map_reduce_executable_fn.0,
        map_reduce_list_executable_fn.0,
        7,
        56,
        57,
        58,
        59,
    ];
    if let Some(reducer_body) = program
        .module
        .fns
        .iter()
        .find(|function| function.id == reducer_executable_fn)
        && let Some(crate::fz_ir::Term::TailCall {
            callee: crate::fz_ir::DirectCallTarget::Local(next),
            ..
        }) = reducer_body.blocks.first().map(|block| &block.terminator)
    {
        extra_fns.push(next.0);
        if let Some(clause_body) = program.module.fns.iter().find(|function| function.id == *next) {
            for block in &clause_body.blocks {
                if let crate::fz_ir::Term::Call {
                    callee: crate::fz_ir::DirectCallTarget::Local(inner),
                    continuation,
                    ..
                } = &block.terminator
                {
                    extra_fns.push(inner.0);
                    extra_fns.push(continuation.fn_id.0);
                    if let Some(resume_body) = program
                        .module
                        .fns
                        .iter()
                        .find(|function| function.id == continuation.fn_id)
                    {
                        for resume_block in &resume_body.blocks {
                            if let crate::fz_ir::Term::Call {
                                callee: crate::fz_ir::DirectCallTarget::Local(resume_inner),
                                continuation: resume_cont,
                                ..
                            } = &resume_block.terminator
                            {
                                extra_fns.push(resume_inner.0);
                                extra_fns.push(resume_cont.fn_id.0);
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!(
        "native executable fns reducer={} map_reduce={} map_reduce_list={}",
        reducer_executable_fn.0, map_reduce_executable_fn.0, map_reduce_list_executable_fn.0
    );
    for body in &program.bodies {
        if extra_fns.contains(&body.fn_id.0)
            || body.fn_id == reducer_executable_fn
            || body.fn_id == map_reduce_executable_fn
            || body.fn_id == map_reduce_list_executable_fn
            || matches!(body.origin, NativeBodyOrigin::Continuation { owner, .. } if owner == map_reduce_list_executable_fn)
        {
            eprintln!(
                "body fn={} origin={:?} entry_abi={:?} param_reprs={:?} return_abi={:?}",
                body.fn_id.0, body.origin, body.entry_abi, body.param_reprs, body.return_abi
            );
        }
    }
    for function in &program.module.fns {
        if extra_fns.contains(&function.id.0) {
            eprintln!("ir fn {} {}:", function.id.0, function.name);
            for block in &function.blocks {
                eprintln!("  block {:?} params={:?}", block.id, block.params);
                eprintln!("    term={:?}", block.terminator);
            }
        }
    }
    for boundary in &program.callable_boundaries {
        if boundary.target.activation.function == reducer_id
            || boundary.target.activation.function == enum_map_reduce_list_id
        {
            eprintln!(
                "boundary id={} identity={} target_fn={} function={} capture_count={} capture_reprs={:?} arg_reprs={:?} return_abi={:?} activation_input={:?}",
                boundary.id().as_u32(),
                boundary.identity_fn.0,
                boundary.target_fn.0,
                boundary.target.activation.function.as_u32(),
                boundary.capture_count,
                boundary.capture_reprs,
                boundary.arg_reprs,
                boundary.return_abi,
                boundary.target.activation.input
            );
        }
    }
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let _ = compiled.run(&tel, program.entry);
    assert_eq!(
        dbg.lines(),
        vec!["{[1, 3, 6, 10], 10}".to_string()],
        "compiler2-owned native codegen should preserve Enum.map_reduce when direct closure targets capture scalar lanes exactly",
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
    tel.attach(&[], capture.handler());
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        !program.callable_boundaries.is_empty() && !native_callable_boundary_uses(&program).is_empty(),
        "zero-capture lambda constructors should publish callable-boundary inventory for native materialization",
    );
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let _ = compiled.run(&tel, program.entry);
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
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        compiled.run(&tel, program.entry),
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
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        compiled.run(&tel, program.entry),
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
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_interp_runs_quicksort_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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

    assert_eq!(
        halt, 42,
        "quicksort entry/0 should halt with its explicit scalar result"
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
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_interp_runs_enum_with_index_mapper_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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

#[test]
fn compiler2_interp_runs_variadic_extern_from_backend_artifacts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_interp_uses_backend_runtime_self_and_send_intrinsics() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_native_program_routes_post_receive_resumes_through_delivered_continuations() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "receive_shared_tuple_arity should settle through native lowering before delivered-resume inspection",
    );

    let program = native.last(root_id).program;
    let receive_body_resume_fns = program
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
        receive_body_resume_fns.len(),
        2,
        "the fixture should expose one delivered post-receive resume per receive site",
    );
    for resume_fn in receive_body_resume_fns {
        let body = program
            .bodies
            .iter()
            .find(|body| body.fn_id == resume_fn)
            .unwrap_or_else(|| panic!("native body for receive resume {resume_fn:?}"));
        assert!(
            matches!(body.entry_abi, NativeEntryAbi::Continuation { .. }),
            "code reached from a receive-arm call must be published as a delivered continuation, not a local direct entry: fn={resume_fn:?} origin={:?} abi={:?}",
            body.origin,
            body.entry_abi,
        );
    }
}

#[test]
fn compiler2_native_receive_body_call_resumes_once() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], dbg.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_native_actor_ring_delivers_resume_values_through_continuation_abi() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_native_program_resource_fixture_shapes_callable_boundaries_explicitly() {
    let _lock = tests_support_lock().lock().unwrap();
    tests_support_dtor_reset();

    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
        .filter(|entry| entry.target.activation.function == lambda_id)
        .map(|entry| (entry.capture_count, entry.arg_reprs.clone(), entry.return_abi.clone()))
        .collect::<Vec<_>>();
    assert_eq!(
        callable_boundaries,
        vec![(0, vec![AbiValueRepr::RawInt], ReturnAbi::Value(AbiValueRepr::ValueRef))],
        "resource destructor lambdas should surface one zero-capture callable boundary that takes the raw payload lane and returns through the boxed nil seam",
    );
    assert_eq!(
        native_executable_body(&program, lambda_id).param_reprs,
        vec![AbiValueRepr::RawInt],
        "resource destructor executable bodies should specialize their native entry lane to the raw payload type",
    );
    let make_resource_id = function_id(&functions, "fz_make_resource", 2);
    assert_eq!(
        native_executable_body(&program, make_resource_id).return_abi,
        ReturnAbi::Value(AbiValueRepr::ValueRef),
        "fz_make_resource/2 must return a boxed resource ref through the native ABI",
    );

    let native_callable_boundary = program
        .callable_boundaries
        .iter()
        .find(|entry| entry.target.activation.function == lambda_id)
        .expect("native program should publish the dtor lambda callable boundary");
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let static_target = compiled
        .static_closure_targets()
        .iter()
        .find(|(_, fn_id, _, _)| *fn_id == native_callable_boundary.target_fn.0)
        .expect("compiled JIT module should publish one static closure target for the dtor entry target");
    let body_ptr = compiled
        .fn_ptr(native_callable_boundary.target_fn)
        .expect("compiled JIT module should publish the dtor entry target body address");
    assert_ne!(
        static_target.2, body_ptr,
        "static closure singletons should point at callable-boundary wrappers, not straight at the lambda body",
    );
}

#[test]
fn compiler2_native_codegen_materializes_the_settled_callable_boundary_for_opaque_closures() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "codegen", "callable_boundary_materialized"], capture.handler());
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "closure_typed_captures should settle through native lowering before JIT consumes it",
    );

    let program = native.last(root_id).program;
    let expected_boundary = program
        .callable_boundaries
        .iter()
        .find(|boundary| {
            boundary.capture_count == 2
                && boundary.arg_reprs == vec![AbiValueRepr::ValueRef]
                && boundary.return_abi == ReturnAbi::Value(AbiValueRepr::ValueRef)
        })
        .expect("native program should publish the widened ValueRef callable boundary for the captured lambda");

    let _compiled = jit_compile_native_program(&mut compiler, &program);

    let materialization = capture
        .find(&["fz", "codegen", "callable_boundary_materialized"])
        .into_iter()
        .find(|event| metadata_str(event, "materialization_kind") == "make_closure")
        .expect("JIT codegen should record one opaque closure boundary materialization for the captured lambda");
    assert_eq!(
        measurement_u64(&materialization, "callable_boundary_id"),
        expected_boundary.id().as_u32() as u64,
        "opaque closure construction should materialize the settled callable boundary instead of re-selecting a narrower executable body",
    );
}

#[test]
fn compiler2_backend_program_revision_stays_stable_for_identical_recompute() {
    let tel = ConfiguredTelemetry::new();
    let backend = BackendProgramCapture::new();
    tel.attach(&["fz", "compiler2", "backend_program", "defined"], backend.handler());

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(compiler.drive(), "initial backend lowering should settle for quicksort");
    assert!(
        compiler.demand(Job::LowerBackendProgram(root_id)),
        "explicitly re-demanding unchanged backend lowering should enqueue one fresh derivation",
    );
    assert_resolved(
        compiler.drive(),
        "re-lowering unchanged backend state should resolve without bumping the revision",
    );

    let records = backend.records(root_id);
    assert_eq!(
        records.len(),
        2,
        "the backend program should have one initial definition and one unchanged re-derivation",
    );
    assert!(
        records[0].changed && !records[1].changed,
        "initial derivation should be changed=true; re-derivation of identical state should be changed=false",
    );
    assert_eq!(
        records[0].program, records[1].program,
        "identical backend-program recomputation should produce byte-for-byte equal program facts",
    );
}

#[test]
fn compiler2_abi_ready_preserves_variadic_extern_marshals_and_integer_lanes() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let abi_ready = AbiReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "abi_ready_program", "defined"],
        abi_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "ABI-ready projection should preserve extern marshals and derive raw integer lanes",
    );

    let program = abi_ready.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let open_id = function_id(&functions, "libc::open", 2);
    let (_, open_plan) = abi_ready_executable(&program, open_id);
    let (_, main_plan) = abi_ready_executable(&program, main_id);
    assert_eq!(
        open_plan.param_reprs,
        vec![AbiValueRepr::ValueRef, AbiValueRepr::RawInt, AbiValueRepr::RawInt],
        "variadic extern activations should expose the fixed and extra callsite lanes directly in ABI-ready form",
    );
    assert_eq!(
        open_plan.return_abi,
        ReturnAbi::Value(AbiValueRepr::RawInt),
        "extern integer returns should be explicit raw integer ABI lanes",
    );

    let open_edge = main_plan
        .call_edges
        .values()
        .find(|edge| local_call_target(&edge.callee).activation.function == open_id)
        .expect("ABI-ready call edge for libc::open");
    assert_eq!(
        open_edge.extern_marshals.as_deref(),
        Some(&[ExternTy::CString, ExternTy::I64, ExternTy::I64][..]),
        "ABI-ready call edges should preserve the frozen variadic marshal classes",
    );
    assert_eq!(
        open_edge.return_abi,
        ReturnAbi::Value(AbiValueRepr::RawInt),
        "ABI-ready call edges should carry the callee return ABI explicitly",
    );
}

#[test]
fn compiler2_emission_ready_preserves_variadic_extern_inventory_and_marshals() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let emission_ready = EmissionReadyProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "emission_ready_program", "defined"],
        emission_ready.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "emission-ready projection should preserve the frozen variadic extern contract all the way to the final handoff",
    );

    let program = emission_ready.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let open_id = function_id(&functions, "libc::open", 2);
    let (_, open_exec) = emission_ready_executable(&program, open_id);
    let (_, main_exec) = emission_ready_executable(&program, main_id);
    assert_eq!(
        open_exec.param_reprs,
        vec![AbiValueRepr::ValueRef, AbiValueRepr::RawInt, AbiValueRepr::RawInt],
        "emission-ready inventory should preserve the fixed and variadic ABI lanes for libc::open",
    );
    assert_eq!(
        open_exec.return_abi,
        ReturnAbi::Value(AbiValueRepr::RawInt),
        "emission-ready inventory should preserve the raw integer return lane for libc::open",
    );

    let open_edge = main_exec
        .call_edges
        .iter()
        .find(|edge| {
            program.executables[*local_call_target(&edge.callee)]
                .key
                .activation
                .function
                == open_id
        })
        .expect("emission-ready call edge for libc::open");
    assert_eq!(
        open_edge.extern_marshals.as_deref(),
        Some(&[ExternTy::CString, ExternTy::I64, ExternTy::I64][..]),
        "emission-ready call edges should preserve the frozen C marshal classes for a variadic extern callsite",
    );
    assert_eq!(
        program.executables[*local_call_target(&open_edge.callee)].return_abi,
        ReturnAbi::Value(AbiValueRepr::RawInt),
        "emission-ready call edges should resolve through the callee inventory slot instead of re-deriving ABI",
    );
}

#[test]
fn compiler2_materialization_resolves_auto_variadic_marshals_from_value_types() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let materialized = MaterializedProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "materialized_program", "defined"],
        materialized.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "materialization should resolve auto variadic marshal classes from settled caller value types",
    );

    let program = materialized.last(root_id).program;
    let main_id = function_id(&functions, "main", 0);
    let printf_id = function_id(&functions, "libc::printf", 1);
    let (_, main_plan) = materialized_executable(&program, main_id);
    let printf_edge = main_plan
        .call_edges
        .values()
        .find(|edge| local_call_target(&edge.callee).activation.function == printf_id)
        .expect("materialized call edge for libc::printf");
    assert_eq!(
        printf_edge.extern_marshals.as_deref(),
        Some(&[ExternTy::CString, ExternTy::I64][..]),
        "a variadic extra integer should resolve to the I64 marshal class without an explicit ascription",
    );
}

#[test]
fn compiler2_variadic_extern_too_few_args_is_a_lower_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let closed = semantic.last(root_id);

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
        closed
            .executables
            .iter()
            .any(|executable| executable.activation.function == partition_id
                && executable.need == ExecutableNeed::TupleFields(2)),
        "the closed executable frontier should keep partition/4 under tuple-fields demand"
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
fn compiler2_materializes_closed_union_protocol_dispatch_as_local_dispatch() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "diag", "error"], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());
    let materialized = MaterializedProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "materialized_program", "defined"],
        materialized.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
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

    match compiler.drive() {
        DriveOutcome::Resolved => {}
        DriveOutcome::Fatal { job } => panic!(
            "closed-union protocol receivers should materialize as local dispatch instead of dying with a missing direct edge: {job:?}; diag={:?}",
            capture
                .last(&["fz", "diag", "error"])
                .map(|event| metadata_str(&event, "message").to_string())
        ),
        other => panic!(
            "closed-union protocol receivers should materialize as local dispatch instead of dying with a missing direct edge: {other:?}"
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

    let program = materialized.last(root_id).program;
    let (_, describe_exec) = materialized_executable(&program, describe_id);
    let LoweredBody::Clauses { entries, .. } = &describe_exec.body else {
        panic!("describe/1 should materialize as clauses");
    };
    let dispatch = entries
        .iter()
        .find_map(|entry| match &entry.tail {
            LoweredTail::Dispatch { dispatch, .. } => Some(dispatch),
            _ => None,
        })
        .unwrap_or_else(|| panic!("materialized describe/1 should contain a dispatch tail"));
    assert_eq!(
        dispatch.arm_entries.len(),
        2,
        "closed-union protocol dispatch should materialize one direct arm per viable impl",
    );
    let arm_targets = dispatch
        .arm_entries
        .iter()
        .map(|entry_id| {
            let entry = &entries[entry_id.as_u32() as usize];
            let LoweredTail::DirectCall { callsite, .. } = entry.tail else {
                panic!("protocol dispatch arm entry should lower to one direct call");
            };
            describe_exec
                .call_edges
                .get(&callsite)
                .unwrap_or_else(|| {
                    panic!(
                        "materialized call edge for synthetic protocol arm {}",
                        callsite.as_u32()
                    )
                })
                .callee
                .local()
                .expect("synthetic protocol arms should target local executables")
                .activation
                .function
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        arm_targets, expected_targets,
        "the synthetic arm entries should target the two settled impl executables from the semantic summary",
    );
    assert!(
        matches!(
            entries[dispatch.miss_entry.as_u32() as usize].tail,
            LoweredTail::Halt { .. }
        ),
        "protocol dispatch should keep an explicit no-match halt entry instead of an unlowerable stub",
    );
}

#[test]
fn compiler2_quicksort_root_closes_with_a_finite_recursive_frontier() {
    let tel = ConfiguredTelemetry::new();
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
        "quicksort root should settle to a finite semantic frontier",
    );

    let main_id = function_id(&functions, "main", 0);
    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);

    let closed = semantic.last(root_id);
    let activations = closed.activations.iter().cloned().collect::<HashSet<_>>();

    assert!(
        activations.contains(&ActivationKey {
            root: root_id,
            function: main_id,
            input: Vec::new(),
        }),
        "root closure should keep the entry activation in the settled frontier"
    );
    let qsort_activations = activations
        .iter()
        .filter(|activation| activation.function == qsort_id)
        .collect::<Vec<_>>();
    assert_eq!(
        qsort_activations.len(),
        2,
        "root closure should keep the narrow and widened qsort/1 recursive activations"
    );
    assert!(
        qsort_activations[0].input != qsort_activations[1].input,
        "the two qsort/1 recursive activations should remain distinct after canonical keying"
    );
    let mut partition_activations = activations
        .iter()
        .filter(|activation| activation.function == partition_id)
        .cloned()
        .collect::<Vec<_>>();
    partition_activations.sort_by(|left, right| left.input.cmp(&right.input));
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
            .all(|activation| activation.input.len() == 4),
        "partition/4 should stay keyed on its four inputs"
    );
    assert_eq!(
        partition_activations[0].input[2], partition_activations[0].input[3],
        "partition/4's recursive accumulator slots share one convergence class"
    );
    let append_activations = activations
        .iter()
        .filter(|activation| activation.function == append_id)
        .collect::<Vec<_>>();
    assert_eq!(
        append_activations.len(),
        2,
        "root closure should keep the narrow and widened append/2 recursive activations that hang off qsort/1"
    );
    assert!(
        append_activations.iter().all(|activation| activation.input.len() == 2),
        "append/2 should stay keyed on its two inputs"
    );
    assert!(
        append_activations[0].input != append_activations[1].input,
        "the two append/2 recursive activations should remain distinct after canonical keying"
    );
    // Honest argument evidence keys non-recursive runtime helpers
    // per-callsite (the designed behavior); the old any-defaults
    // accidentally merged those keys. The frontier stays small and finite —
    // the runaway grew it without bound.
    assert!(
        activations.len() <= 26,
        "quicksort should settle to a small finite rooted activation frontier, including reached runtime helpers"
    );
    assert!(
        !activations.iter().any(|activation| activation.function == foo_id),
        "quicksort root should not activate the uncalled foo/0"
    );
    assert!(
        closed
            .executables
            .iter()
            .all(|executable| executable.activation.function != foo_id),
        "uncalled foo/0 should not appear in the closed executable frontier"
    );
}

#[test]
fn compiler2_redefining_uncalled_foo_does_not_reopen_quicksort_root() {
    let tel = ConfiguredTelemetry::new();
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo_v1.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(compiler.drive(), "initial quicksort root should settle");
    let closed_before = semantic.last(root_id);
    let count_before = semantic.count(root_id);

    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo_v2.fz".to_string()),
        text: include_str!("../../fixtures2/00027_foo_99.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "redefining uncalled foo/0 should not reopen the quicksort root",
    );

    assert_eq!(
        semantic.count(root_id),
        count_before,
        "uncalled foo/0 redefinition should not republish semantic closure for the rooted quicksort frontier"
    );
    assert_eq!(
        semantic.last(root_id).activations.into_iter().collect::<HashSet<_>>(),
        closed_before.activations.into_iter().collect::<HashSet<_>>(),
        "uncalled foo/0 redefinition should leave the rooted activation frontier unchanged"
    );
}

#[test]
fn compiler2_redefining_main_retracts_the_old_root_frontier_and_activates_foo() {
    let tel = ConfiguredTelemetry::new();
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo_v1.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(compiler.drive(), "initial quicksort root should settle");

    let qsort_id = function_id(&functions, "qsort", 1);
    let partition_id = function_id(&functions, "partition", 4);
    let append_id = function_id(&functions, "append", 2);
    let foo_id = function_id(&functions, "foo", 0);

    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo_v2.fz".to_string()),
        text: include_str!("../../fixtures2/00008_callsite_fact_surface.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "redefining main/0 should retract the old quicksort root frontier",
    );

    let closed_after = semantic.last(root_id);
    let activation_functions = closed_after
        .activations
        .iter()
        .map(|activation| activation.function)
        .collect::<HashSet<_>>();
    let executable_functions = closed_after
        .executables
        .iter()
        .map(|executable| executable.activation.function)
        .collect::<HashSet<_>>();

    assert_eq!(
        activation_functions,
        HashSet::from([function_id(&functions, "main", 0), foo_id]),
        "redefining main/0 should leave only main/0 and foo/0 in the rooted activation frontier"
    );
    assert_eq!(
        executable_functions,
        HashSet::from([function_id(&functions, "main", 0), foo_id]),
        "redefining main/0 should leave only main/0 and foo/0 in the rooted executable frontier"
    );
    assert!(
        !closed_after.activations.iter().any(
            |activation| matches!(activation.function, id if id == qsort_id || id == partition_id || id == append_id)
        ),
        "redefining main/0 should retract the old quicksort recursive frontier"
    );
}

#[test]
fn compiler2_helper_redefinition_leaves_semantic_frontiers_closed_when_reachability_is_unchanged() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/helper_roots_v1.fz".to_string()),
        text: include_str!("../../fixtures2/00028_helper_roots.fz").to_string(),
    });
    let main_root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let other_root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "other_main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(compiler.drive(), "initial rooted helper users should settle");
    let main_closed_before = semantic.last(main_root);
    let other_closed_before = semantic.last(other_root);
    let main_seal_stops_before = outputs
        .stops_matching(|job| matches!(job, Job::SealSemanticClosure(root) if *root == main_root))
        .len();
    let other_seal_stops_before = outputs
        .stops_matching(|job| matches!(job, Job::SealSemanticClosure(root) if *root == other_root))
        .len();

    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/helper_roots_v2.fz".to_string()),
        text: include_str!("../../fixtures2/00029_positive_gte.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "redefining a helper should keep semantic frontiers closed when rooted reachability stays the same",
    );

    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::SealSemanticClosure(root) if *root == main_root))
            .len()
            > main_seal_stops_before,
        "helper guard changes should re-check the dependent root closure",
    );
    assert_eq!(
        outputs
            .stops_matching(|job| matches!(job, Job::SealSemanticClosure(root) if *root == other_root))
            .len(),
        other_seal_stops_before,
        "helper guard changes should not reopen independent root closure sealing"
    );
    assert!(
        outputs
            .stops_matching(|job| matches!(job, Job::SealSemanticClosure(root) if *root == main_root))
            .into_iter()
            .skip(main_seal_stops_before)
            .filter_map(|stop| stop.effects)
            .all(|effects| !output_facts(&effects).contains(&presence(FactKey::SemanticClosed(main_root), true))),
        "helper guard changes should not republish semantic closure when the dependent frontier is unchanged",
    );
    assert_eq!(
        semantic.last(main_root).activations,
        main_closed_before.activations,
        "helper guard changes should leave the dependent rooted activation frontier unchanged"
    );
    assert_eq!(
        semantic.last(main_root).executables,
        main_closed_before.executables,
        "helper guard changes should leave the dependent rooted executable frontier unchanged"
    );
    assert_eq!(
        semantic.last(other_root).activations,
        other_closed_before.activations,
        "helper guard changes should leave the independent rooted activation frontier unchanged"
    );
    assert_eq!(
        semantic.last(other_root).executables,
        other_closed_before.executables,
        "helper guard changes should leave the independent rooted executable frontier unchanged"
    );
}

#[test]
fn compiler2_submit_root_before_code_reports_unresolved_until_entry_is_defined() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let work_graph = WorkGraphCapture::new();
    tel.attach(&["fz", "compiler2", "work_graph", "applied"], work_graph.handler());

    let mut compiler = Compiler2::new(&tel);
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
                    wait.fact == settled_fact(FactKey::FunctionDefined(function_id))
                        && wait.jobs.contains(&Job::SeedRoot(root_id))
                }),
                "unresolved drive should report SeedRoot waiting on the entry definition"
            );
            assert!(
                work_graph.all().into_iter().any(|step| step
                    .blocked
                    .contains(&settled_fact(FactKey::FunctionDefined(function_id)))),
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
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
    let closure_checks_before = outputs
        .stops_matching(|job| matches!(job, Job::SealSemanticClosure(_)))
        .len();
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
    let foo_id = function_id(&functions, "foo", 0);
    assert!(
        scope_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::FunctionSource(foo_id)),
        "late code should note foo/0 source without an explicit ScopeCode demand"
    );
    assert_eq!(
        outputs.stops_matching(|job| matches!(job, Job::SeedRoot(_))).len(),
        seed_stops_before,
        "late unrelated code should not reseed the existing root"
    );
    assert_eq!(
        outputs
            .stops_matching(|job| matches!(job, Job::SealSemanticClosure(_)))
            .len(),
        closure_checks_before,
        "late unrelated code should not reopen semantic closure for the existing root"
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
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

#[test]
fn compiler2_recursive_keying_sees_recursion_through_generated_lambdas() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());

    let mut compiler = Compiler2::new(&tel);
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
            .take(Job::DeriveRecursive(build_id))
            .expect("DeriveRecursive job effects for build/2")
            .contains(&presence(FactKey::Recursive(build_id), true)),
        "the recursive fact should be published for closure-mediated recursion",
    );
    assert!(
        !outputs
            .stops_matching(|job| *job == Job::LowerFunction(generated[0].function_id))
            .is_empty(),
        "deriving recursion should inspect the generated lambda body instead of peeking only at build/2",
    );

    let closed = semantic.last(root_id);
    let build_activations = closed
        .activations
        .iter()
        .filter(|activation| activation.function == build_id)
        .collect::<Vec<_>>();
    assert_eq!(
        build_activations.len(),
        1,
        "recursive non-dispatch inputs should collapse to one build/2 activation key",
    );

    assert!(
        !build_activations[0].input.is_empty(),
        "the collapsed build/2 activation should still carry the recursive accumulator slot",
    );
}

#[test]
fn compiler2_lowered_body_keeps_clause_projections_separate_from_entry_matching() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "non-tail join fixture should settle before native continuation inspection",
    );

    let program = native.last(root_id).program;
    let closure_continuations = program
        .module
        .fns
        .iter()
        .filter(|function| function.name.contains("map_every_list"))
        .flat_map(|function| function.blocks.iter())
        .filter_map(|block| match &block.terminator {
            IrTerm::CallClosure { continuation, .. } => Some(continuation.fn_id),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(
        !closure_continuations.is_empty(),
        "the non-tail join fixture should contain at least one closure-call continuation in native IR",
    );

    for continuation_fn in closure_continuations {
        let body = program
            .bodies
            .iter()
            .find(|body| body.fn_id == continuation_fn)
            .unwrap_or_else(|| panic!("native body for continuation {:?} missing", continuation_fn));
        assert!(
            matches!(body.entry_abi, NativeEntryAbi::Continuation { .. }),
            "closure-call continuation {:?} should publish a continuation entry ABI, got {:?}",
            continuation_fn,
            body.entry_abi,
        );
    }
}

#[test]
fn compiler2_native_program_transports_reusable_cons_caps_through_delivered_continuations() {
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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
        "the helper should resume with one delivered result before its captures, got {:?}",
        continuation.entry_abi,
    );
    assert_eq!(
        function.block(function.entry).params,
        vec![
            crate::fz_ir::Var(0),
            crate::fz_ir::Var(1),
            crate::fz_ir::Var(2),
            crate::fz_ir::Var(3)
        ],
        "the continuation should append one hidden physical source param after its semantic params",
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
        vec![crate::fz_ir::Var(0), crate::fz_ir::Var(1), crate::fz_ir::Var(2)],
        "semantic entry params must ignore the hidden physical capture",
    );
}

#[test]
fn compiler2_lowered_body_records_reusable_cons_capture_requirements_on_delivered_entries() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_native_program_jit_runs_nontail_if_join_flow_through_compiler2_codegen() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&["fz", "runtime", "dbg"], dbg.handler());
    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module"], modules.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let guard_defs = GuardDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "guard_dispatch", "defined"], guard_defs.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let guard_defs = GuardDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "guard_dispatch", "defined"], guard_defs.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let entry_defs = EntryDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "entry_dispatch", "defined"], entry_defs.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let entry_defs = EntryDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "entry_dispatch", "defined"], entry_defs.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let guard_defs = GuardDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "guard_dispatch", "defined"], guard_defs.handler());
    let entry_defs = EntryDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "entry_dispatch", "defined"], entry_defs.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only.fz".to_string()),
        text: include_str!("../../fixtures2/00045_import_only.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-only scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
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
        compiler.demand(Job::DefineModule(module_ids[0])),
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
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
fn compiler2_remote_macro_requires_explicit_require() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only_unknown.fz".to_string()),
        text: include_str!("../../fixtures2/00046_import_only_unknown.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-only unknown scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-only unknown scope"
    );
    assert_resolved(
        compiler.drive(),
        "second drive should scope import-only unknown modules",
    );
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_all.fz".to_string()),
        text: include_str!("../../fixtures2/00047_import_all.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-all scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-all scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-all modules");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should publish the provider interface before retrying User",
    );
    assert!(
        outputs
            .stops_matching(|job| *job == Job::DefineModule(module_ids[0]))
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
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_except.fz".to_string()),
        text: include_str!("../../fixtures2/00048_import_except.fz").to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index import-except scope");
    let module_ids = module_indexed_ids(&outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects"));
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-except scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-except modules");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should publish the provider interface before retrying User",
    );
    assert!(
        outputs
            .stops_matching(|job| *job == Job::DefineModule(module_ids[0]))
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
    spans: SpanJobs,
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
    owner_module_id: Option<ModuleId>,
    arity: u64,
    clauses: u64,
    owner_function_id: Option<FunctionId>,
    function_ref: FunctionRef,
}

#[derive(Debug, Clone)]
struct CallsiteDefinedRecord {
    key: CallSiteKey,
    summary: CallSiteSummary,
}

#[derive(Debug, Clone)]
struct SemanticClosedRecord {
    root_id: crate::compiler2::RootId,
    activations: HashSet<ActivationKey>,
    executables: HashSet<ExecutableKey>,
}

#[derive(Debug, Clone)]
struct MaterializedProgramRecord {
    root_id: crate::compiler2::RootId,
    program: MaterializedProgram,
}

#[derive(Debug, Clone)]
struct AbiReadyProgramRecord {
    root_id: crate::compiler2::RootId,
    program: AbiReadyProgram,
}

#[derive(Debug, Clone)]
struct EmissionReadyProgramRecord {
    root_id: crate::compiler2::RootId,
    changed: bool,
    program: EmissionReadyProgram,
}

#[derive(Debug, Clone)]
struct BackendProgramRecord {
    root_id: crate::compiler2::RootId,
    changed: bool,
    program: BackendProgram,
}

#[derive(Debug, Clone)]
struct NativeProgramRecord {
    root_id: crate::compiler2::RootId,
    changed: bool,
    program: NativeProgram,
}

#[derive(Debug, Clone)]
struct ReturnTypeRecord {
    activation: ActivationKey,
    return_ty: Ty,
}

pub(crate) struct FunctionCapture {
    defs: FunctionDefs,
}

pub(crate) struct ModuleCapture {
    defs: ModuleDefs,
}

struct CallsiteCapture {
    defs: CallsiteDefs,
}

struct SemanticClosedCapture {
    defs: SemanticClosedDefs,
}

struct ReturnTypeCapture {
    defs: ReturnTypeDefs,
}

struct MaterializedProgramCapture {
    defs: MaterializedProgramDefs,
}

struct AbiReadyProgramCapture {
    defs: AbiReadyProgramDefs,
}

struct EmissionReadyProgramCapture {
    defs: EmissionReadyProgramDefs,
}

struct BackendProgramCapture {
    defs: BackendProgramDefs,
}

struct NativeProgramCapture {
    defs: NativeProgramDefs,
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
            spans: Rc::new(RefCell::new(HashMap::new())),
            stops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(OutputCaptureHandler {
            outputs: self.outputs.clone(),
            spans: self.spans.clone(),
            stops: self.stops.clone(),
        })
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

    fn all(&self) -> Vec<(FactKey, bool)> {
        self.outputs
            .borrow()
            .values()
            .flat_map(|outputs| outputs.iter())
            .flat_map(|facts| facts.iter().cloned())
            .collect()
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

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(WorkGraphCaptureHandler {
            steps: self.steps.clone(),
        })
    }

    fn all(&self) -> Vec<AppliedStep<Job, FactKey>> {
        self.steps.borrow().clone()
    }
}

impl FunctionCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(FunctionCaptureHandler {
            defs: self.defs.clone(),
        })
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

impl ModuleCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(ModuleCaptureHandler {
            defs: self.defs.clone(),
        })
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
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(CallsiteCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn all(&self) -> Vec<CallsiteDefinedRecord> {
        self.defs.borrow().clone()
    }
}

impl SemanticClosedCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(SemanticClosedCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last(&self, root_id: crate::compiler2::RootId) -> SemanticClosedRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("semantic_closed.defined for {root_id:?}"))
    }

    fn count(&self, root_id: crate::compiler2::RootId) -> usize {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.root_id == root_id)
            .count()
    }
}

impl ReturnTypeCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(ReturnTypeCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last_for_function(&self, root_id: crate::compiler2::RootId, function_id: FunctionId) -> ReturnTypeRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.activation.root == root_id && record.activation.function == function_id)
            .cloned()
            .unwrap_or_else(|| panic!("return_type.defined for root={root_id:?} function={function_id:?}"))
    }
}

impl MaterializedProgramCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(MaterializedProgramCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last(&self, root_id: crate::compiler2::RootId) -> MaterializedProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("materialized_program.defined for {root_id:?}"))
    }
}

impl AbiReadyProgramCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(AbiReadyProgramCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last(&self, root_id: crate::compiler2::RootId) -> AbiReadyProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("abi_ready_program.defined for {root_id:?}"))
    }
}

impl EmissionReadyProgramCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(EmissionReadyProgramCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last(&self, root_id: crate::compiler2::RootId) -> EmissionReadyProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("emission_ready_program.defined for {root_id:?}"))
    }

    fn records(&self, root_id: crate::compiler2::RootId) -> Vec<EmissionReadyProgramRecord> {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.root_id == root_id)
            .cloned()
            .collect()
    }
}

impl BackendProgramCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(BackendProgramCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last(&self, root_id: crate::compiler2::RootId) -> BackendProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("backend_program.defined for {root_id:?}"))
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

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(NativeProgramCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last(&self, root_id: crate::compiler2::RootId) -> NativeProgramRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("native_program.defined for {root_id:?}"))
    }

    fn records(&self, root_id: crate::compiler2::RootId) -> Vec<NativeProgramRecord> {
        self.defs
            .borrow()
            .iter()
            .filter(|record| record.root_id == root_id)
            .cloned()
            .collect()
    }
}

impl GuardDispatchCapture {
    fn new() -> Self {
        Self {
            dispatches: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(GuardDispatchCaptureHandler {
            dispatches: self.dispatches.clone(),
        })
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

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(EntryDispatchCaptureHandler {
            plans: self.plans.clone(),
        })
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

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(LoweredBodyCaptureHandler {
            bodies: self.bodies.clone(),
        })
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

struct OutputCaptureHandler {
    outputs: JobOutputMap,
    spans: SpanJobs,
    stops: Rc<RefCell<Vec<JobSpanStop>>>,
}

struct WorkGraphCaptureHandler {
    steps: AppliedSteps,
}

struct FunctionCaptureHandler {
    defs: FunctionDefs,
}

struct ModuleCaptureHandler {
    defs: ModuleDefs,
}

struct CallsiteCaptureHandler {
    defs: CallsiteDefs,
}

struct SemanticClosedCaptureHandler {
    defs: SemanticClosedDefs,
}

struct ReturnTypeCaptureHandler {
    defs: ReturnTypeDefs,
}

struct MaterializedProgramCaptureHandler {
    defs: MaterializedProgramDefs,
}

struct AbiReadyProgramCaptureHandler {
    defs: AbiReadyProgramDefs,
}

struct EmissionReadyProgramCaptureHandler {
    defs: EmissionReadyProgramDefs,
}

struct BackendProgramCaptureHandler {
    defs: BackendProgramDefs,
}

struct NativeProgramCaptureHandler {
    defs: NativeProgramDefs,
}

struct EntryDispatchCaptureHandler {
    plans: EntryDispatchMap,
}

struct GuardDispatchCaptureHandler {
    dispatches: GuardDispatchMap,
}

struct LoweredBodyCaptureHandler {
    bodies: LoweredBodyDefs,
}

impl Handler for OutputCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "job"] {
            return;
        }
        match event.kind {
            EventKind::SpanStart => {
                let Some(job) = event.metadata.get("job").and_then(|value| value.downcast_ref::<Job>()) else {
                    return;
                };
                self.spans.borrow_mut().insert(event.span_id, job.clone());
            }
            EventKind::SpanStop => {
                let Some(job) = self.spans.borrow_mut().remove(&event.span_id) else {
                    return;
                };
                self.stops.borrow_mut().push(JobSpanStop {
                    job: job.clone(),
                    effects_present: event.metadata.get("effects").is_some(),
                    effects: event
                        .metadata
                        .get("effects")
                        .and_then(|value| value.downcast_ref::<JobEffects>())
                        .cloned(),
                });
                let Some(effects) = event
                    .metadata
                    .get("effects")
                    .and_then(|value| value.downcast_ref::<JobEffects>())
                else {
                    return;
                };
                self.outputs
                    .borrow_mut()
                    .entry(job)
                    .or_default()
                    .push(output_facts(effects));
            }
            EventKind::Event | EventKind::SpanException => {}
        }
    }
}

impl Handler for WorkGraphCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "work_graph", "applied"] || event.kind != EventKind::Event {
            return;
        }
        let Some(step) = event
            .metadata
            .get("step")
            .and_then(|value| value.downcast_ref::<AppliedStep<Job, FactKey>>())
        else {
            return;
        };
        self.steps.borrow_mut().push(step.clone());
    }
}

impl Handler for FunctionCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.kind != EventKind::Event {
            return;
        }
        let from_source = match event.name {
            ["fz", "compiler2", "function", "defined"] => false,
            ["fz", "compiler2", "function", "source", "noted"] => true,
            _ => return,
        };
        let Some(function_id) = event
            .metadata
            .get("function_id")
            .and_then(|v| v.downcast_ref::<FunctionId>())
            .copied()
        else {
            return;
        };
        let Some(module_id) = event
            .metadata
            .get("module_id")
            .and_then(|v| v.downcast_ref::<ModuleId>())
            .copied()
        else {
            return;
        };
        let owner_module_id = event
            .metadata
            .get("owner_module_id")
            .and_then(|v| v.downcast_ref::<ModuleId>())
            .copied();
        let Some(Value::U64(arity)) = event.measurements.get("arity") else {
            return;
        };
        let Some(Value::U64(clauses)) = event.measurements.get("clauses") else {
            return;
        };
        let Some(function_ref) = event
            .metadata
            .get("function_ref")
            .and_then(|value| value.downcast_ref::<FunctionRef>())
        else {
            return;
        };
        let owner_function_id = if from_source {
            None
        } else {
            event
                .metadata
                .get("owner_function_id")
                .and_then(|v| v.downcast_ref::<FunctionId>())
                .copied()
        };
        self.defs.borrow_mut().insert(
            function_id,
            FunctionDefinedRecord {
                function_id,
                module_id,
                owner_module_id,
                arity: *arity,
                clauses: *clauses,
                owner_function_id,
                function_ref: function_ref.clone(),
            },
        );
    }
}

impl Handler for ModuleCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "module", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(module_id) = event
            .metadata
            .get("module_id")
            .and_then(|v| v.downcast_ref::<ModuleId>())
            .copied()
        else {
            return;
        };
        let Some(module) = event
            .metadata
            .get("module")
            .and_then(|value| value.downcast_ref::<ModuleState>())
        else {
            return;
        };
        self.defs
            .borrow_mut()
            .entry(module_id)
            .or_default()
            .push(module.clone());
    }
}

impl Handler for CallsiteCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "callsite", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(key) = event
            .metadata
            .get("callsite")
            .and_then(|value| value.downcast_ref::<CallSiteKey>())
        else {
            return;
        };
        let Some(summary) = event
            .metadata
            .get("summary")
            .and_then(|value| value.downcast_ref::<CallSiteSummary>())
        else {
            return;
        };
        self.defs.borrow_mut().push(CallsiteDefinedRecord {
            key: key.clone(),
            summary: summary.clone(),
        });
    }
}

impl Handler for SemanticClosedCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "semantic_closed", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(root_id) = event
            .metadata
            .get("root_id")
            .and_then(|v| v.downcast_ref::<crate::compiler2::RootId>())
            .copied()
        else {
            return;
        };
        let Some(closure) = event
            .metadata
            .get("closure")
            .and_then(|value| value.downcast_ref::<SemanticClosure>())
        else {
            return;
        };
        self.defs.borrow_mut().push(SemanticClosedRecord {
            root_id,
            activations: closure.activations.clone(),
            executables: closure.executables.clone(),
        });
    }
}

impl Handler for ReturnTypeCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "return_type", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(activation) = event
            .metadata
            .get("activation")
            .and_then(|value| value.downcast_ref::<ActivationKey>())
        else {
            return;
        };
        // The event carries the activation's return EVIDENCE. Only rounds
        // that hold evidence are recorded; the last record at quiescence is
        // the settled return.
        let Some(Some(return_ty)) = event
            .metadata
            .get("return_ty")
            .and_then(|value| value.downcast_ref::<Option<Ty>>())
            .copied()
        else {
            return;
        };
        self.defs.borrow_mut().push(ReturnTypeRecord {
            activation: activation.clone(),
            return_ty,
        });
    }
}

impl Handler for MaterializedProgramCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "materialized_program", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(root_id) = event
            .metadata
            .get("root_id")
            .and_then(|v| v.downcast_ref::<crate::compiler2::RootId>())
            .copied()
        else {
            return;
        };
        let Some(program) = event
            .metadata
            .get("program")
            .and_then(|value| value.downcast_ref::<MaterializedProgram>())
        else {
            return;
        };
        self.defs.borrow_mut().push(MaterializedProgramRecord {
            root_id,
            program: program.clone(),
        });
    }
}

impl Handler for AbiReadyProgramCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "abi_ready_program", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(root_id) = event
            .metadata
            .get("root_id")
            .and_then(|v| v.downcast_ref::<crate::compiler2::RootId>())
            .copied()
        else {
            return;
        };
        let Some(program) = event
            .metadata
            .get("program")
            .and_then(|value| value.downcast_ref::<AbiReadyProgram>())
        else {
            return;
        };
        self.defs.borrow_mut().push(AbiReadyProgramRecord {
            root_id,
            program: program.clone(),
        });
    }
}

impl Handler for EmissionReadyProgramCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "emission_ready_program", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(root_id) = event
            .metadata
            .get("root_id")
            .and_then(|v| v.downcast_ref::<crate::compiler2::RootId>())
            .copied()
        else {
            return;
        };
        let Some(Value::U64(changed)) = event.measurements.get("changed") else {
            return;
        };
        let Some(program) = event
            .metadata
            .get("program")
            .and_then(|value| value.downcast_ref::<EmissionReadyProgram>())
        else {
            return;
        };
        self.defs.borrow_mut().push(EmissionReadyProgramRecord {
            root_id,
            changed: *changed != 0,
            program: program.clone(),
        });
    }
}

impl Handler for BackendProgramCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "backend_program", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(root_id) = event
            .metadata
            .get("root_id")
            .and_then(|v| v.downcast_ref::<crate::compiler2::RootId>())
            .copied()
        else {
            return;
        };
        let Some(Value::U64(changed)) = event.measurements.get("changed") else {
            return;
        };
        let Some(program) = event
            .metadata
            .get("program")
            .and_then(|value| value.downcast_ref::<BackendProgram>())
        else {
            return;
        };
        self.defs.borrow_mut().push(BackendProgramRecord {
            root_id,
            changed: *changed != 0,
            program: program.clone(),
        });
    }
}

impl Handler for NativeProgramCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "native_program", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(root_id) = event
            .metadata
            .get("root_id")
            .and_then(|v| v.downcast_ref::<crate::compiler2::RootId>())
            .copied()
        else {
            return;
        };
        let Some(Value::U64(changed)) = event.measurements.get("changed") else {
            return;
        };
        let Some(program) = event
            .metadata
            .get("program")
            .and_then(|value| value.downcast_ref::<NativeProgram>())
        else {
            return;
        };
        self.defs.borrow_mut().push(NativeProgramRecord {
            root_id,
            changed: *changed != 0,
            program: program.clone(),
        });
    }
}

impl Handler for GuardDispatchCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "guard_dispatch", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(function_id) = event
            .metadata
            .get("function_id")
            .and_then(|v| v.downcast_ref::<FunctionId>())
            .copied()
        else {
            return;
        };
        let Some(dispatch) = event
            .metadata
            .get("dispatch")
            .and_then(|value| value.downcast_ref::<PatternGuardDispatch<Ty>>())
        else {
            return;
        };
        self.dispatches
            .borrow_mut()
            .entry(function_id)
            .or_default()
            .push(dispatch.clone());
    }
}

impl Handler for EntryDispatchCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "entry_dispatch", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(function_id) = event
            .metadata
            .get("function_id")
            .and_then(|v| v.downcast_ref::<FunctionId>())
            .copied()
        else {
            return;
        };
        let Some(plan) = event
            .metadata
            .get("plan")
            .and_then(|value| value.downcast_ref::<PatternDispatchPlan<Ty>>())
        else {
            return;
        };
        self.plans
            .borrow_mut()
            .entry(function_id)
            .or_default()
            .push(plan.clone());
    }
}

impl Handler for LoweredBodyCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "lowered_body", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(function_id) = event
            .metadata
            .get("function_id")
            .and_then(|v| v.downcast_ref::<FunctionId>())
            .copied()
        else {
            return;
        };
        let Some(body) = event
            .metadata
            .get("body")
            .and_then(|value| value.downcast_ref::<LoweredBody>())
        else {
            return;
        };
        self.bodies
            .borrow_mut()
            .entry(function_id)
            .or_default()
            .push(body.clone());
    }
}

fn measurement_u64(event: &crate::telemetry::capture::OwnedEvent, key: &str) -> u64 {
    match event.measurements.get(key) {
        Some(Value::U64(value)) => *value,
        other => panic!("measurement key `{key}` missing or not u64: {other:?}"),
    }
}

fn metadata_str<'a>(event: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match event.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("metadata key `{key}` missing or not str: {other:?}"),
    }
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

fn materialized_executable(
    program: &MaterializedProgram,
    function: FunctionId,
) -> (&ExecutableKey, &crate::compiler2::MaterializedExecutable) {
    program
        .executables
        .iter()
        .find(|(key, _)| key.activation.function == function)
        .unwrap_or_else(|| panic!("materialized executable for {function:?}"))
}

fn abi_ready_executable(
    program: &AbiReadyProgram,
    function: FunctionId,
) -> (&ExecutableKey, &crate::compiler2::AbiReadyExecutable) {
    program
        .executables
        .iter()
        .find(|(key, _)| key.activation.function == function)
        .unwrap_or_else(|| panic!("ABI-ready executable for {function:?}"))
}

fn abi_ready_callable_entries(program: &AbiReadyProgram, function: FunctionId) -> Vec<&CallableEntry> {
    let entries = program
        .callable_entries
        .iter()
        .filter(|entry| entry.target.activation.function == function)
        .collect::<Vec<_>>();
    assert!(!entries.is_empty(), "ABI-ready callable entries for {function:?}");
    entries
}

fn emission_ready_executable(
    program: &EmissionReadyProgram,
    function: FunctionId,
) -> (usize, &crate::compiler2::EmissionReadyExecutable) {
    program
        .executables
        .iter()
        .enumerate()
        .find(|(_, executable)| executable.key.activation.function == function)
        .unwrap_or_else(|| panic!("emission-ready executable for {function:?}"))
}

fn emission_ready_callable_entries(
    program: &EmissionReadyProgram,
    function: FunctionId,
) -> Vec<(usize, &crate::compiler2::EmissionReadyCallableEntry)> {
    let entries = program
        .callable_entries
        .iter()
        .enumerate()
        .filter(|(_, entry)| program.executables[entry.target].key.activation.function == function)
        .collect::<Vec<_>>();
    assert!(!entries.is_empty(), "emission-ready callable entries for {function:?}");
    entries
}

fn backend_executable(program: &BackendProgram, function: FunctionId) -> (usize, &crate::compiler2::BackendExecutable) {
    program
        .executables
        .iter()
        .enumerate()
        .find(|(_, executable)| executable.key.activation.function == function)
        .unwrap_or_else(|| panic!("backend executable for {function:?}"))
}

fn backend_direct_call<'a>(
    executable: &'a crate::compiler2::BackendExecutable,
    program: &'a BackendProgram,
    callee: FunctionId,
) -> &'a BackendTail {
    match &executable.body {
        crate::compiler2::BackendBody::Extern { .. } => panic!("expected clause body with a direct call"),
        crate::compiler2::BackendBody::Clauses { clauses, entries, .. } => {
            for clause in clauses {
                if let Some(found) = backend_direct_call_in_entry(entries, clause.entry, program, callee) {
                    return found;
                }
            }
            panic!("backend direct call to {callee:?} not found")
        }
    }
}

fn backend_direct_call_in_entry<'a>(
    entries: &'a [BackendEntry],
    entry_id: crate::compiler2::ControlEntryId,
    program: &'a BackendProgram,
    callee: FunctionId,
) -> Option<&'a BackendTail> {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        BackendTail::DirectCall { callee: target, .. }
            if program.executables[*local_call_target(target)].key.activation.function == callee =>
        {
            Some(&entry.tail)
        }
        BackendTail::If {
            then_entry, else_entry, ..
        } => backend_direct_call_in_entry(entries, *then_entry, program, callee)
            .or_else(|| backend_direct_call_in_entry(entries, *else_entry, program, callee)),
        _ => None,
    }
}

fn native_executable_functions(program: &NativeProgram) -> HashSet<FunctionId> {
    program
        .bodies
        .iter()
        .filter_map(|body| match &body.origin {
            NativeBodyOrigin::Executable(key) => Some(key.activation.function),
            NativeBodyOrigin::Clause { .. } | NativeBodyOrigin::Continuation { .. } => None,
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
            | NativeBodyOrigin::Continuation { .. } => None,
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

fn native_closure_call_targets(program: &NativeProgram) -> Vec<Option<FnId>> {
    let mut out = Vec::new();
    for function in &program.module.fns {
        for block in &function.blocks {
            match &block.terminator {
                IrTerm::CallClosure { direct_target, .. } | IrTerm::TailCallClosure { direct_target, .. } => {
                    out.push(*direct_target);
                }
                _ => {}
            }
        }
    }
    out
}

fn native_callable_boundary_uses(program: &NativeProgram) -> HashSet<NativeCallableBoundaryId> {
    let mut out = HashSet::new();
    for body in &program.bodies {
        out.extend(body.callable_value_boundaries.values().copied());
    }
    out
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

fn native_programs_match(left: &NativeProgram, right: &NativeProgram) -> bool {
    left.backend_revision == right.backend_revision
        && left.entry == right.entry
        && left.bodies == right.bodies
        && left.callable_boundaries == right.callable_boundaries
        && native_modules_match(&left.module, &right.module)
}

fn native_modules_match(left: &IrModule, right: &IrModule) -> bool {
    left.module_path == right.module_path
        && left.fns.len() == right.fns.len()
        && left
            .fns
            .iter()
            .zip(right.fns.iter())
            .all(|(left, right)| native_fns_match(left, right))
        && left.fn_idx == right.fn_idx
        && left.atom_names == right.atom_names
        && left.externs == right.externs
        && left.extern_idx == right.extern_idx
        && left.external_call_edges().len() == right.external_call_edges().len()
        && left
            .external_call_edges()
            .iter()
            .zip(right.external_call_edges().iter())
            .all(|(left, right)| native_external_call_edges_match(left, right))
        && left.protocol_call_targets == right.protocol_call_targets
}

fn native_fns_match(left: &IrFn, right: &IrFn) -> bool {
    left.id == right.id
        && left.name == right.name
        && left.frame_schema_id == right.frame_schema_id
        && left.entry == right.entry
        && left.category == right.category
        && left.owner_module == right.owner_module
        && left.ignored_entry_params == right.ignored_entry_params
        && left.physical_entry_params == right.physical_entry_params
        && left.physical_capabilities == right.physical_capabilities
        && left.blocks.len() == right.blocks.len()
        && left
            .blocks
            .iter()
            .zip(right.blocks.iter())
            .all(|(left, right)| native_blocks_match(left, right))
}

fn native_blocks_match(left: &IrBlock, right: &IrBlock) -> bool {
    left.id == right.id
        && left.params == right.params
        && left.stmts.len() == right.stmts.len()
        && left
            .stmts
            .iter()
            .zip(right.stmts.iter())
            .all(|(left, right)| native_stmts_match(left, right))
        && native_terms_match(&left.terminator, &right.terminator)
}

fn native_stmts_match(left: &IrStmt, right: &IrStmt) -> bool {
    match (left, right) {
        (IrStmt::Let(left_var, left_prim), IrStmt::Let(right_var, right_prim)) => {
            left_var == right_var && native_prims_match(left_prim, right_prim)
        }
    }
}

fn native_prims_match(left: &IrPrim, right: &IrPrim) -> bool {
    match (left, right) {
        (IrPrim::Extern(left_ident, left_extern, left_args), IrPrim::Extern(right_ident, right_extern, right_args)) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_extern == right_extern
                && left_args == right_args
        }
        (IrPrim::MakeFnRef(left_ident, left_fn), IrPrim::MakeFnRef(right_ident, right_fn)) => {
            native_callsite_idents_match(left_ident, right_ident) && left_fn == right_fn
        }
        (
            IrPrim::MakeClosure(left_ident, left_fn, left_captured),
            IrPrim::MakeClosure(right_ident, right_fn, right_captured),
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_fn == right_fn
                && left_captured == right_captured
        }
        _ => left == right,
    }
}

fn native_terms_match(left: &IrTerm, right: &IrTerm) -> bool {
    match (left, right) {
        (IrTerm::Goto(left_block, left_args), IrTerm::Goto(right_block, right_args)) => {
            left_block == right_block && left_args == right_args
        }
        (
            IrTerm::If {
                cond: left_cond,
                then_b: left_then,
                else_b: left_else,
                origin: left_origin,
            },
            IrTerm::If {
                cond: right_cond,
                then_b: right_then,
                else_b: right_else,
                origin: right_origin,
            },
        ) => {
            left_cond == right_cond && left_then == right_then && left_else == right_else && left_origin == right_origin
        }
        (
            IrTerm::Call {
                ident: left_ident,
                callee: left_callee,
                args: left_args,
                continuation: left_cont,
            },
            IrTerm::Call {
                ident: right_ident,
                callee: right_callee,
                args: right_args,
                continuation: right_cont,
            },
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_callee == right_callee
                && left_args == right_args
                && native_conts_match(left_cont, right_cont)
        }
        (
            IrTerm::TailCall {
                ident: left_ident,
                callee: left_callee,
                args: left_args,
                is_back_edge: left_back_edge,
            },
            IrTerm::TailCall {
                ident: right_ident,
                callee: right_callee,
                args: right_args,
                is_back_edge: right_back_edge,
            },
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_callee == right_callee
                && left_args == right_args
                && left_back_edge == right_back_edge
        }
        (
            IrTerm::CallClosure {
                ident: left_ident,
                closure: left_closure,
                args: left_args,
                continuation: left_cont,
                direct_target: left_direct_target,
            },
            IrTerm::CallClosure {
                ident: right_ident,
                closure: right_closure,
                args: right_args,
                continuation: right_cont,
                direct_target: right_direct_target,
            },
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_closure == right_closure
                && left_args == right_args
                && native_conts_match(left_cont, right_cont)
                && left_direct_target == right_direct_target
        }
        (
            IrTerm::TailCallClosure {
                ident: left_ident,
                closure: left_closure,
                args: left_args,
                direct_target: left_direct_target,
            },
            IrTerm::TailCallClosure {
                ident: right_ident,
                closure: right_closure,
                args: right_args,
                direct_target: right_direct_target,
            },
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_closure == right_closure
                && left_args == right_args
                && left_direct_target == right_direct_target
        }
        (IrTerm::Return(left_var), IrTerm::Return(right_var)) | (IrTerm::Halt(left_var), IrTerm::Halt(right_var)) => {
            left_var == right_var
        }
        (
            IrTerm::ReceiveMatched {
                ident: left_ident,
                clauses: left_clauses,
                dispatch: left_dispatch,
                after: left_after,
                pinned: left_pinned,
                captures: left_captures,
            },
            IrTerm::ReceiveMatched {
                ident: right_ident,
                clauses: right_clauses,
                dispatch: right_dispatch,
                after: right_after,
                pinned: right_pinned,
                captures: right_captures,
            },
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_clauses.len() == right_clauses.len()
                && left_clauses
                    .iter()
                    .zip(right_clauses.iter())
                    .all(|(left, right)| native_receive_clauses_match(left, right))
                && left_dispatch == right_dispatch
                && native_receive_after_match(left_after.as_ref(), right_after.as_ref())
                && left_pinned == right_pinned
                && left_captures == right_captures
        }
        _ => false,
    }
}

fn native_conts_match(left: &IrCont, right: &IrCont) -> bool {
    left.fn_id == right.fn_id && left.captured == right.captured
}

fn native_receive_clauses_match(left: &ReceiveClause, right: &ReceiveClause) -> bool {
    native_callsite_idents_match(&left.ident, &right.ident)
        && left.bound_names == right.bound_names
        && left.guard == right.guard
        && left.body == right.body
        && left.span == right.span
}

fn native_receive_after_match(left: Option<&ReceiveAfter>, right: Option<&ReceiveAfter>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            native_callsite_idents_match(&left.ident, &right.ident)
                && left.timeout == right.timeout
                && left.body == right.body
                && left.span == right.span
        }
        _ => false,
    }
}

fn native_external_call_edges_match(left: &ExternalCallEdge, right: &ExternalCallEdge) -> bool {
    native_callsite_ids_match(&left.callsite, &right.callsite) && left.target == right.target
}

fn native_callsite_ids_match(left: &IrCallsiteId, right: &IrCallsiteId) -> bool {
    left.caller == right.caller && left.slot == right.slot && native_callsite_idents_match(&left.ident, &right.ident)
}

fn native_callsite_idents_match(left: &CallsiteIdent, right: &CallsiteIdent) -> bool {
    left.span() == right.span()
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

pub(crate) fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

pub(crate) fn function_id(capture: &FunctionCapture, name: &str, arity: u64) -> FunctionId {
    capture.id(name, arity)
}

fn generated_functions_owned_by(capture: &FunctionCapture, owner: FunctionId) -> Vec<FunctionDefinedRecord> {
    capture
        .all()
        .into_iter()
        .filter(|record| record.owner_function_id == Some(owner))
        .collect()
}

fn function_id_in_module(
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
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());

    let mut world = crate::compiler2::World::new(&tel);
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
    assert_resolved(world.drive(), "the recursive count program should converge");

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
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());

    let mut world = crate::compiler2::World::new(&tel);
    world.submit_code(
        Some("forever.fz".to_string()),
        concat!("fn forever(), do: forever()\n", "fn main(), do: forever()\n").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(world.drive(), "a never-returning program still quiesces");

    let closure = semantic.last(root);
    assert!(!closure.activations.is_empty());
    for activation in &closure.activations {
        assert_eq!(
            world.activation_return(activation),
            None,
            "settled evidence for a never-returning activation stays empty",
        );
    }
}

#[test]
fn compiler2_unproductive_deepening_settles_at_bottom_without_widening() {
    // fn deep(x), do: [deep(x)] — the inner call must produce a value before
    // the list ever exists, so this function NEVER returns: its least
    // fixpoint is bottom. Under the old absent-reads-as-none lie this very
    // program manufactured a divergent ascent (list(none), list(list(none)),
    // …); honest paths never start the chain.
    let tel = ConfiguredTelemetry::new();
    let widened = Capture::new();
    tel.attach(&["fz", "compiler2", "return_type", "widened"], widened.handler());
    let mut world = crate::compiler2::World::new(&tel);
    world.submit_code(
        Some("deep_unproductive.fz".to_string()),
        concat!("fn deep(x), do: [deep(x)]\n", "fn main(), do: deep(1)\n").to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(world.drive(), "an unproductive deepening program quiesces at bottom");
    assert!(
        widened.is_empty(),
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
    let widened = Capture::new();
    tel.attach(&["fz", "compiler2", "return_type", "widened"], widened.handler());
    let mut world = crate::compiler2::World::new(&tel);
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
    assert_resolved(world.drive(), "the productive deepening program must converge");
    assert!(
        !widened.is_empty(),
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
        max_ascents: u64,
    }
    let defines: Rc<RefCell<HashMap<(u64, u64), ReturnStats>>> = Rc::new(RefCell::new(HashMap::new()));
    let sink = Rc::clone(&defines);
    tel.attach(
        &["fz", "compiler2", "return_type", "defined"],
        Box::new(move |event: &Event<'_, '_, '_>| {
            let (Some(Value::U64(root)), Some(Value::U64(function)), Some(Value::U64(ascents))) = (
                event.measurements.get("root_id"),
                event.measurements.get("function_id"),
                event.measurements.get("ascents"),
            ) else {
                return;
            };
            let mut defines = sink.borrow_mut();
            let entry = defines.entry((*root, *function)).or_default();
            entry.define_calls += 1;
            entry.max_ascents = entry.max_ascents.max(*ascents);
        }),
    );

    let mut world = crate::compiler2::World::new(&tel);
    world.submit_code(
        Some("quicksort.fz".to_string()),
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(world.drive(), "quicksort converges by theorem, on every schedule");

    for ((root, function), stats) in defines.borrow().iter() {
        assert!(
            stats.max_ascents <= 8,
            "fn {function} (root {root}) ascended {} times — corpus programs converge well under the widening delay",
            stats.max_ascents,
        );
        assert!(
            stats.define_calls <= 64,
            "fn {function} (root {root}) was re-analyzed {} times — the runaway re-ran one activation 32,366 times",
            stats.define_calls,
        );
    }
}

/// The widening operator is a terminator of last resort, not a feature any
/// honest program meets: across the whole fixture corpus the return join
/// must converge precisely, with zero widening engagements. The measured
/// maximum ascent pinned here is what justifies the headroom documented on
/// RETURN_WIDENING_BUDGET — if this pin moves, that doc comment moves with
/// it. The sweep is sharded into four `#[test]`s purely so it parallelizes
/// across the harness's threads; together the shards cover every fixture.
fn sweep_corpus_for_return_widening(shard: usize, shards: usize) {
    let mut swept = 0u32;
    let mut corpus_max_ascents = 0u64;
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
        let widened = Capture::new();
        tel.attach(&["fz", "compiler2", "return_type", "widened"], widened.handler());
        let max_ascents: Rc<RefCell<u64>> = Rc::new(RefCell::new(0));
        let sink = Rc::clone(&max_ascents);
        tel.attach(
            &["fz", "compiler2", "return_type", "defined"],
            Box::new(move |event: &Event<'_, '_, '_>| {
                if let Some(Value::U64(ascents)) = event.measurements.get("ascents") {
                    let mut max = sink.borrow_mut();
                    *max = (*max).max(*ascents);
                }
            }),
        );

        let mut world = crate::compiler2::World::new(&tel);
        world.submit_code(Some(path.display().to_string()), text);
        world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
        // Diagnostics are fixture-specific; the corpus invariants are that
        // the drive terminates (it returned) and never widened a return.
        let _ = world.drive();
        assert!(
            widened.is_empty(),
            "return widening engaged on corpus fixture {}",
            path.display(),
        );
        corpus_max_ascents = corpus_max_ascents.max(*max_ascents.borrow());
    }
    assert!(
        swept >= 25,
        "corpus shard {shard}/{shards} swept only {swept} fixtures — wrong path?"
    );
    assert!(
        corpus_max_ascents <= 4,
        "corpus max return ascents grew to {corpus_max_ascents} — \
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
    // schedule irrelevant: twenty fresh drives must do identical work and
    // settle identical frontiers. If this test ever flakes, the design has
    // a hole and the flake has found it — do not loosen it.
    let mut shapes = Vec::new();
    for _ in 0..20 {
        let tel = ConfiguredTelemetry::new();
        let semantic = SemanticClosedCapture::new();
        tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());
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

        let mut world = crate::compiler2::World::new(&tel);
        world.submit_code(
            Some("quicksort.fz".to_string()),
            include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
        );
        let root = world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
        assert_resolved(world.drive(), "every schedule converges");
        let closed = semantic.last(root);
        shapes.push((*jobs_ran.borrow(), closed.activations.len(), closed.executables.len()));
    }
    // The fixpoint is unique: every schedule settles the exact same
    // frontier. The WORK to reach it may vary slightly (a different
    // interleaving costs a few extra quiet joins), but stays in a tight
    // band — the runaway did 54,000+ jobs where these do ~300.
    let frontier = (shapes[0].1, shapes[0].2);
    assert!(
        shapes.iter().all(|shape| (shape.1, shape.2) == frontier),
        "all schedules must settle identical frontiers: {shapes:?}",
    );
    let min_jobs = shapes.iter().map(|shape| shape.0).min().expect("runs");
    let max_jobs = shapes.iter().map(|shape| shape.0).max().expect("runs");
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
    let mut world = crate::compiler2::World::new(&tel);
    world.submit_code(
        Some("quicksort.fz".to_string()),
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    assert_resolved(world.drive(), "first drive settles");

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
    assert_resolved(world.drive(), "a settled world re-drives to Resolved");
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
    // String literals have no singleton types (Literal::Binary types as
    // str_t), so no subtype check can ever witness "the scrutinee always
    // equals this string". The old miss-side proof !is_subtype(str, str)
    // evaluated false and silently pruned the live wildcard clause — the
    // value test happens at RUNTIME, so the statically pruned body was
    // simply gone. Both clauses must stay reachable.
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    type ReachableByFunction = Vec<(u64, Vec<u32>)>;
    let analyses: Rc<RefCell<ReachableByFunction>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&analyses);
    tel.attach(
        &["fz", "compiler2", "activation_analysis", "defined"],
        Box::new(move |event: &Event<'_, '_, '_>| {
            let Some(Value::U64(function)) = event.measurements.get("function_id") else {
                return;
            };
            let Some(analysis) = event
                .metadata
                .get("analysis")
                .and_then(|value| value.downcast_ref::<crate::compiler2::ActivationAnalysis>())
            else {
                return;
            };
            sink.borrow_mut().push((*function, analysis.reachable_clauses.clone()));
        }),
    );

    let mut world = crate::compiler2::World::new(&tel);
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
    assert_resolved(world.drive(), "string-constant dispatch should settle");

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

#[test]
fn compiler2_int_keyed_map_index_types_through_the_carried_literal() {
    // Map keys are VALUES: the lowering carries the written constant
    // alongside the runtime key (LoweredMapKey), so %{1 => 10}[1] keeps its
    // precise int field type without numeric singleton types in the lattice.
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let returns = ReturnTypeCapture::new();
    tel.attach(&["fz", "compiler2", "return_type", "defined"], returns.handler());

    let mut world = crate::compiler2::World::new(&tel);
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
    assert_resolved(world.drive(), "int-keyed map program settles");

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
    tel.attach(&["fz", "diag"], diags.handler());
    let rendered = rendered_type_defs(&tel);

    let mut world = crate::compiler2::World::new(&tel);
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
    assert_resolved(world.drive(), "the literal-typed program settles");

    assert!(
        diags.find(&["fz", "diag", "warning"]).iter().any(|event| {
            matches!(
                event.metadata.get("code"),
                Some(Value::Str(code)) if code == "type/numeric-literal-widened"
            )
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
    tel.attach(&[], dbg.handler());
    let native = NativeProgramCapture::new();
    tel.attach(&["fz", "compiler2", "native_program", "defined"], native.handler());

    let mut compiler = Compiler2::new(&tel);
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

    assert_resolved(
        compiler.drive(),
        "native lowering should preserve callable return seams for closure predicates and reducers",
    );

    let program = native.last(root_id).program;
    let compiled = jit_compile_native_program(&mut compiler, &program);
    assert_eq!(
        compiled.run(&tel, program.entry),
        2,
        "the fixture should still return the final count after native callable-entry adaptation",
    );
    assert_eq!(
        dbg.lines().as_slice(),
        ["false", "false", "true", ":no", "2", "2", "2"],
        "callable-entry adapters should box raw predicate/reducer returns back onto the ValueRef callable seam",
    );
}
