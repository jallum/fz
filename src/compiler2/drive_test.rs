use super::{AppliedStep, CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, Job, RootSubmission};
use crate::compiler2::artifact::{BackendEntry, BackendTail};
use crate::compiler2::artifact::{NativeBodyOrigin, NativeEntryAbi, NativeProgram};
use crate::compiler2::drive::JobEffects;
use crate::compiler2::{
    AbiReadyProgram, AbiValueRepr, ActivationKey, BackendProgram, CallSiteId, CallSiteKey, CallSiteSummary,
    CallableEntry, ControlEntryOrigin, EmissionReadyProgram, ExecutableKey, FactKey, FunctionId, FunctionRef,
    LoweredBody, LoweredStep, LoweredTail, MaterializedProgram, ModuleId, ModuleState, ReturnAbi, SelectedCallee,
    QuotedSourceHeap, SemanticClosure, Ty, TypeName, TypeVarId, Types, ValueId,
};
use crate::diag::codes;
use crate::dispatch_matrix::Region;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::exec::runtime::DbgCapture;
use crate::fz_ir::{
    Block as IrBlock, CallsiteId as IrCallsiteId, CallsiteIdent, Cont as IrCont, ExternTy, ExternalCallEdge,
    FnIr as IrFn, Module as IrModule, Prim as IrPrim, ReceiveAfter, ReceiveClause, Stmt as IrStmt, Term as IrTerm,
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

    let consumers_of = |ref_name: &str| {
        let mut consumers = capture
            .find(&["fz", "compiler2", "type", "referenced"])
            .into_iter()
            .filter(|event| metadata_str(event, "ref_name") == ref_name)
            .map(|event| metadata_str(&event, "consumer").to_string())
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
    assert_eq!(metadata_str(&box_refs[0], "consumer"), "type:tkf_wrapper");
    assert_eq!(
        consumers_of("tkf_box"),
        vec!["type:tkf_wrapper".to_string()],
        "the parametric type is a dep of the wrapper that applies it",
    );
}

#[test]
fn compiler2_derive_type_def_pulls_a_referenced_type_and_its_wait_set_leaving_others_cold() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

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
        capture
            .find(&["fz", "compiler2", "type", "defined"])
            .into_iter()
            .filter(|event| metadata_str(event, "name") == name)
            .map(|event| metadata_str(&event, "ty").to_string())
            .last()
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
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

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

    let resolved = capture
        .find(&["fz", "compiler2", "type", "defined"])
        .into_iter()
        .filter(|event| metadata_str(event, "name") == "tkf_pos")
        .map(|event| metadata_str(&event, "ty").to_string())
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
fn compiler2_protocol_domain_and_dispatch_facts_revise_when_impls_land() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
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
        protocol_defined.contains(&presence(FactKey::TypeDefined(t0.clone()), true))
            && protocol_defined.contains(&presence(FactKey::TypeDefined(t1.clone()), true))
            && protocol_defined.contains(&presence(FactKey::ProtocolDispatch(protocol), true)),
        "defining the protocol should publish both protocol-domain type facts and an initial dispatch fact",
    );

    let initial = capture
        .find(&["fz", "compiler2", "type", "defined"])
        .into_iter()
        .filter(|event| metadata_str(event, "name") == "t")
        .map(|event| {
            (
                measurement_u64(&event, "arity"),
                measurement_u64(&event, "changed"),
                metadata_str(&event, "ty").to_string(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        initial.len(),
        2,
        "the initial protocol surface should publish both t arities once"
    );

    let mut expect = Types::new();
    let marker = expect.opaque_of(&crate::frontend::protocols::protocol_domain_tag(
        &crate::modules::identity::ModuleName::parse_dotted("Proof").expect("protocol name should parse"),
    ));
    let rendered = expect.display(&marker).to_string();
    assert_eq!(
        initial,
        vec![(0, 1, rendered.clone()), (1, 1, rendered.clone())],
        "before any impl lands, both protocol-domain facts should resolve to the protocol marker",
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
        owner_defined.contains(&presence(FactKey::TypeDefined(t0.clone()), true))
            && owner_defined.contains(&presence(FactKey::TypeDefined(t1.clone()), true))
            && owner_defined.contains(&presence(FactKey::ProtocolDispatch(protocol), true)),
        "adding an impl should revise both protocol-domain type facts and the dispatch fact",
    );

    let any = world.types_mut().any();
    let list_any = world.types_mut().list(any);
    let widened_t0 = world
        .type_def(&t0)
        .expect("the monomorphic protocol-domain fact should stay stored after widening")
        .ty;
    let marker_t0 = world
        .types_mut()
        .opaque_of(&crate::frontend::protocols::protocol_domain_tag(
            &crate::modules::identity::ModuleName::parse_dotted("Proof").expect("protocol name should parse"),
        ));
    assert_eq!(
        widened_t0,
        world.types_mut().union(marker_t0, list_any),
        "t/0 should widen from the marker to the marker-or-list(any) domain when List implements the protocol",
    );

    let elem = world
        .types_mut()
        .type_var(crate::frontend::protocols::PROTOCOL_ELEM_VAR);
    let list_elem = world.types_mut().list(elem);
    let widened_t1 = world
        .type_def(&t1)
        .expect("the parametric protocol-domain fact should stay stored after widening")
        .ty;
    let marker_t1 = world
        .types_mut()
        .opaque_of(&crate::frontend::protocols::protocol_domain_tag(
            &crate::modules::identity::ModuleName::parse_dotted("Proof").expect("protocol name should parse"),
        ));
    assert_eq!(
        widened_t1,
        world.types_mut().union(marker_t1, list_elem),
        "t(a) should widen from the marker to the marker-or-list(a) domain when List implements the protocol",
    );

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
        dispatch.arms[0].callbacks.contains_key(&("pick".to_string(), 2)),
        "the dispatch arm should route the declared callback name and arity",
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
        "scoping should note the expected top-level function surfaces"
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        0,
        "indexing should not eagerly materialize function definitions"
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "source", "noted"]),
        5,
        "scoping should note one function-source fact per top-level function"
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
    assert_eq!(
        outputs.stops_matching(|job| matches!(job, Job::LowerFunction(_))).len(),
        0,
        "indexing should not lower any function bodies"
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
        text: "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n\ndefmacro quoted_var() do\n  quote do: x\nend\n"
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
        macro_outputs.contains(&presence(FactKey::MacroExecutable(inc), 1)),
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
            .stops_matching(|job| matches!(job, Job::LowerBackendProgram(_) | Job::LowerNativeProgram(_)))
            .is_empty(),
        "rejected macro runtime roots must not reach backend or native lowering"
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
    let outputs = outputs
        .take(Job::AnalyzeActivation(ActivationKey {
            root: root_id,
            function: main_id,
            input: Vec::new(),
        }))
        .expect("AnalyzeActivation job effects for main/0");
    let callsite_facts = outputs
        .iter()
        .filter(|(fact, _)| matches!(fact, FactKey::CallSiteSummary(_)))
        .count();

    assert_eq!(
        callsite_facts, 1,
        "an activation with one reached direct call should publish one whole callsite-summary fact",
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
                && record.summary.callee == SelectedCallee::Function(list_impl_reduce_id)
        }),
        "Enum.reduce/3 should devirtualize Enumerable.reduce/3 to the List-backed protocol callback",
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == bridge_reducer_id
                && record.summary.callee == SelectedCallee::Function(user_reducer_id)
        }),
        "the bridge reducer should activate the user reducer closure directly",
    );

    let activation_ids = semantic
        .last(root_id)
        .activations
        .into_iter()
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
    let user_reducer_return = returns.last_for_function(root_id, user_reducer_id).return_ty;
    let list_impl_return = returns.last_for_function(root_id, list_impl_reduce_id).return_ty;
    assert!(
        main_return == enum_reduce_return && main_return == user_reducer_return,
        "the selected reduce path should settle main/0, Enum.reduce/3, and the user reducer to one shared return type",
    );
    assert!(
        list_impl_return != main_return,
        "the selected List-backed protocol callback should keep a distinct wrapper return from the reduced accumulator value",
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
                && record.summary.callee == SelectedCallee::Function(list_impl_reduce_id)
        }),
        "Enum.reduce/3 should still devirtualize through the List-backed protocol callback for operator refs",
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id && record.summary.callee == SelectedCallee::Function(kernel_plus_id)
        }),
        "function-ref reducers should surface Kernel.+/2 as an ordinary callable edge",
    );

    let activation_ids = semantic
        .last(root_id)
        .activations
        .into_iter()
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
        main_return != kernel_plus_return,
        "main/0 should keep a distinct tuple-shaped return from the reducer callback's scalar return",
    );
    assert!(
        enum_reduce_return == kernel_plus_return,
        "Enum.reduce/3 should settle to the same scalar return as the reached Kernel.+/2 reducer callback",
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
    assert_eq!(
        qsort_edge.callee.activation.function, qsort_id,
        "materialization should freeze main/0's qsort/1 call to an exact executable key",
    );
    assert!(
        program.executables.contains_key(&qsort_edge.callee),
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
        1,
        "only the semantically reachable dbg/1 call should survive materialization",
    );
    assert_eq!(
        direct_calls, 1,
        "the specialized materialized body should keep only one live direct-call tail",
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
            .any(|edge| edge.callee.activation.function == list_impl_reduce_id),
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
            .any(|edge| edge.callee.activation.function == user_reducer_id),
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
        .find(|edge| edge.callee.activation.function == partition_id)
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
        .find(|edge| edge.callee.activation.function == open_id)
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
fn compiler2_abi_ready_fails_for_unresolved_named_function_refs_at_callable_boundaries() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/unresolved_callable_boundary.fz".to_string()),
        text: include_str!("../../fixtures2/00014_unresolved_callable_boundary.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let job = match compiler.drive() {
        DriveOutcome::Fatal { job } => job,
        other => panic!("unresolved callable-boundary fn refs should fail during ABI-ready derivation: {other:?}"),
    };
    assert_eq!(
        job,
        Job::DeriveAbiReady(root_id),
        "the fatal should surface when ABI-ready tries to name a callable entry from the closed facts",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("callable-boundary diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN.0,
        "unresolved callable-boundary failures should surface as incomplete closed-artifact facts",
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("missing/1"),
        "the fatal should identify the unresolved named callable boundary",
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
        .find(|edge| program.executables[edge.callee].key.activation.function == qsort_id)
        .expect("emission-ready main/0 -> qsort/1 call edge");
    assert_eq!(
        program.executables[qsort_edge.callee].key.activation.function, qsort_id,
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
        vec![FactKey::SemanticClosed(root_id)],
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
            .all(|(fact, _)| *fact == FactKey::MaterializedProgram(root_id)),
        "materialization should publish only the materialized artifact fact",
    );

    let abi_ready = outputs.effects(Job::DeriveAbiReady(root_id));
    assert_eq!(
        abi_ready.reads,
        vec![FactKey::MaterializedProgram(root_id)],
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
            .all(|(fact, _)| *fact == FactKey::AbiReadyProgram(root_id)),
        "ABI-ready derivation should publish only the ABI-ready artifact fact",
    );

    let emission_ready = outputs.effects(Job::DeriveEmissionReady(root_id));
    assert_eq!(
        emission_ready.reads,
        vec![FactKey::AbiReadyProgram(root_id)],
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
            .all(|(fact, _)| *fact == FactKey::EmissionReadyProgram(root_id)),
        "emission-ready derivation should publish only the emission-ready artifact fact",
    );

    let backend = outputs.effects(Job::LowerBackendProgram(root_id));
    assert_eq!(
        backend.reads,
        vec![FactKey::EmissionReadyProgram(root_id)],
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
            .all(|(fact, _)| *fact == FactKey::BackendProgram(root_id)),
        "backend lowering should publish only the backend handoff fact",
    );

    let native = outputs.effects(Job::LowerNativeProgram(root_id));
    assert_eq!(
        native.reads,
        vec![FactKey::BackendProgram(root_id)],
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
            .all(|(fact, _)| *fact == FactKey::NativeProgram(root_id)),
        "native lowering should publish only the native handoff fact",
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
                program.executables[*callee].key.activation.function, qsort_id,
                "backend direct-call steps should point at settled executable inventory indices",
            );
            assert!(
                args.iter().all(|arg| arg.callable_entries.is_empty()),
                "the main/0 quicksort call should not carry callable-boundary obligations",
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

    let used_entries = backend_callable_entry_uses(&program);
    let expected_entries = program
        .callable_entries
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| {
            let function = program.executables[entry.target].key.activation.function;
            matches!(function, id if id == user_reducer_id || id == bridge_reducer_id).then_some(index)
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        used_entries, expected_entries,
        "backend call arguments should carry exactly the callable-entry obligations that survive the closed Enum.reduce path",
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
                program.executables[*callee].key.activation.function, open_id,
                "backend extern calls should still target the settled extern executable inventory slot",
            );
            assert_eq!(
                extern_marshals.as_deref(),
                Some(&[ExternTy::CString, ExternTy::I64, ExternTy::I64][..]),
                "backend direct-call steps should carry the exact settled C wire classes for a variadic extern site",
            );
            assert!(
                args.iter().all(|arg| arg.callable_entries.is_empty()),
                "plain variadic extern arguments should not carry callable-entry obligations",
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
        program.callable_entries.is_empty(),
        "quicksort should not manufacture callable-entry inventory in the native handoff",
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
        .callable_entries
        .iter()
        .map(|entry| entry.target.activation.function)
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_functions,
        HashSet::from([user_reducer_id, bridge_reducer_id]),
        "the native callable-entry inventory should keep exactly the user reducer and bridge reducer entries",
    );

    let used_entries = native_callable_constructor_uses(&program);
    let expected_entries = program
        .callable_entries
        .iter()
        .filter_map(|entry| {
            matches!(
                entry.target.activation.function,
                id if id == user_reducer_id || id == bridge_reducer_id
            )
            .then_some(entry.target_fn.0 as usize)
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        used_entries, expected_entries,
        "native callable constructors should point at exactly the callable-entry obligations that survive the closed Enum.reduce path",
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
    let callable_targets = native_callable_constructor_uses(&program)
        .into_iter()
        .map(|target_fn| {
            program
                .callable_entries
                .iter()
                .find(|entry| entry.target_fn.0 as usize == target_fn)
                .unwrap_or_else(|| {
                    panic!("native callable constructor target fn {target_fn} missing from callable entries")
                })
                .target
                .activation
                .function
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        callable_targets,
        HashSet::from([child_id]),
        "native callable constructors should resolve to the one closed callable-entry target for child/0",
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
        name: Some("fixtures/map_three_path_parity/input.fz".to_string()),
        text: include_str!("../../fixtures/map_three_path_parity/input.fz").to_string(),
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
        name: Some("fixtures/tail_recursion/input.fz".to_string()),
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
        name: Some("fixtures/receive_selective_refs/input.fz".to_string()),
        text: include_str!("../../fixtures/receive_selective_refs/input.fz").to_string(),
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
fn compiler2_native_program_resource_fixture_shapes_callable_entries_explicitly() {
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
    let callable_entries = program
        .callable_entries
        .iter()
        .filter(|entry| entry.target.activation.function == lambda_id)
        .map(|entry| (entry.capture_count, entry.param_reprs.clone(), entry.return_abi.clone()))
        .collect::<Vec<_>>();
    assert_eq!(
        callable_entries,
        vec![(0, vec![AbiValueRepr::RawInt], ReturnAbi::Value(AbiValueRepr::ValueRef))],
        "resource destructor lambdas should surface one zero-capture callable entry that takes the raw payload lane and returns through the boxed nil seam",
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

    let native_callable_entry = program
        .callable_entries
        .iter()
        .find(|entry| entry.target.activation.function == lambda_id)
        .expect("native program should publish the dtor lambda callable entry");
    let compiled = jit_compile_native_program(&mut compiler, &program);
    let static_target = compiled
        .static_closure_targets()
        .iter()
        .find(|(_, fn_id, _, _)| *fn_id == native_callable_entry.target_fn.0)
        .expect("compiled JIT module should publish one static closure target for the dtor entry target");
    let body_ptr = compiled
        .fn_ptr(native_callable_entry.target_fn)
        .expect("compiled JIT module should publish the dtor entry target body address");
    assert_ne!(
        static_target.2, body_ptr,
        "static closure singletons should point at callable-entry wrappers, not straight at the lambda body",
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
        .find(|edge| edge.callee.activation.function == open_id)
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
        .find(|edge| program.executables[edge.callee].key.activation.function == open_id)
        .expect("emission-ready call edge for libc::open");
    assert_eq!(
        open_edge.extern_marshals.as_deref(),
        Some(&[ExternTy::CString, ExternTy::I64, ExternTy::I64][..]),
        "emission-ready call edges should preserve the frozen C marshal classes for a variadic extern callsite",
    );
    assert_eq!(
        program.executables[open_edge.callee].return_abi,
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
        .find(|edge| edge.callee.activation.function == printf_id)
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
                && record.summary.callee == SelectedCallee::Function(qsort_id)
        }),
        "semantic analysis should publish the rooted main/0 -> qsort/1 direct edge"
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == qsort_id
                && record.summary.callee == SelectedCallee::Function(partition_id)
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
                && record.summary.callee == SelectedCallee::Function(append_id)
        }),
        "semantic analysis should publish qsort/1's reachable append/2 direct edge"
    );
    assert!(
        callsites
            .iter()
            .all(|record| record.summary.callee != SelectedCallee::Function(foo_id)),
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
    assert_eq!(
        partition_activations.len(),
        2,
        "root closure should keep the narrow and widened partition/4 recursive activations because pivot/rest participate in dispatch"
    );
    assert!(
        partition_activations
            .iter()
            .all(|activation| activation.input.len() == 4),
        "partition/4 should stay keyed on its four inputs"
    );
    assert!(
        partition_activations[0].input[..2] != partition_activations[1].input[..2],
        "partition/4 should preserve distinct dispatch-driven pivot/rest keys"
    );
    assert_eq!(
        partition_activations[0].input[2..],
        partition_activations[1].input[2..],
        "partition/4 should collapse only the recursive accumulator slots after canonical keying"
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
    assert!(
        activations.len() <= 13,
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
fn compiler2_helper_redefinition_republishes_only_the_dependent_root_frontier() {
    let tel = ConfiguredTelemetry::new();
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
    let main_count_before = semantic.count(main_root);
    let other_count_before = semantic.count(other_root);

    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/helper_roots_v2.fz".to_string()),
        text: include_str!("../../fixtures2/00029_positive_gte.fz").to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "redefining a helper should republish only the dependent rooted semantic frontier",
    );

    assert!(
        semantic.count(main_root) > main_count_before,
        "redefining the helper should republish the dependent root frontier"
    );
    assert_eq!(
        semantic.count(other_root),
        other_count_before,
        "redefining the helper should not republish the independent root frontier"
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
                    wait.fact == FactKey::FunctionDefined(function_id) && wait.jobs.contains(&Job::SeedRoot(root_id))
                }),
                "unresolved drive should report SeedRoot waiting on the entry definition"
            );
            assert!(
                work_graph
                    .all()
                    .into_iter()
                    .any(|step| step.blocked.contains(&FactKey::FunctionDefined(function_id))),
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
    assert_eq!(
        lowered_functions,
        HashSet::from([main_id, generated[0]]),
        "rooting a local lambda should lower only the reachable owner and generated lambda bodies",
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
        clauses[0]
            .projections
            .iter()
            .all(|step| matches!(step, LoweredStep::TupleField { .. } | LoweredStep::SplitList { .. })),
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
    let _ = entry_dispatch(&entry_defs, wanted_id);
    let _ = entry_dispatch(&entry_defs, other_id);

    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_blast_radius_v2.fz".to_string()),
        text: include_str!("../../fixtures2/00029_positive_gte.fz").to_string(),
    });
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "redefinition code still needs to be scoped explicitly without a root",
    );
    assert_resolved(
        compiler.drive(),
        "helper redefinition should rerun only the helper and dependent entry-dispatch plan",
    );

    let helper_outputs = outputs
        .take(Job::ReifyGuardDispatch(positive_id))
        .expect("helper reification should rerun after helper redefinition");
    assert!(
        helper_outputs.contains(&presence(FactKey::GuardDispatch(positive_id), true)),
        "helper reification should publish a revised guard-dispatch fact",
    );
    let wanted_outputs = outputs
        .take(Job::PlanEntryDispatch(wanted_id))
        .expect("dependent wanted/1 entry dispatch should rerun");
    assert!(
        wanted_outputs.contains(&presence(FactKey::EntryDispatch(wanted_id), true)),
        "dependent wanted/1 entry dispatch should republish with a new revision",
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
fn compiler2_index_code_recurses_through_nested_modules() {
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

    assert_resolved(compiler.drive(), "first drive should index nested module scopes");
    let indexed_outputs = outputs.take(Job::IndexCode(code_id)).expect("IndexCode job effects");
    let module_ids = module_indexed_ids(&indexed_outputs);
    assert_eq!(module_ids.len(), 3, "nested indexing should discover X, X.Y, and X.Y.Z");

    let indexed_stop = outputs.stop(Job::IndexCode(code_id));
    assert!(indexed_stop.effects_present, "indexing job should finish with effects");

    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for nested modules"
    );
    assert_resolved(
        compiler.drive(),
        "second drive should scope the root module declarations",
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "module", "defined"]),
        0,
        "root definition should not eagerly define nested modules"
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        0,
        "root definition should not eagerly define nested functions"
    );

    assert!(
        compiler.demand(Job::DefineModule(*module_ids.last().expect("deepest module id"))),
        "explicit demand should enqueue the nested module definition"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should define the demanded nested module and its parents",
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
        .find(|record| record.function_ref.name != "__info__")
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
        indexed_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleIndexed(_)))
            .count(),
        3,
        "nested indexing should surface one module-indexed fact per nested module"
    );
    assert_eq!(
        indexed_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::FunctionDefined(_)))
            .count(),
        0,
        "nested indexing should not define functions directly"
    );
    assert_eq!(
        indexed_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleDefined(_)))
            .count(),
        0,
        "nested indexing should not define modules directly"
    );
    assert!(
        indexed_outputs.contains(&presence(FactKey::CodeIndexed(code_id), true)),
        "nested indexing should include the final code-indexed fact"
    );
}

#[test]
fn compiler2_import_only_classifies_exact_refs_when_body_uses_them() {
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
        capture.count(&["fz", "compiler2", "function", "defined"]),
        0,
        "root definition should not eagerly define import-only modules"
    );
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(
        compiler.drive(),
        "third drive should classify the exact imported call before saving User.run",
    );
    let mut names = functions
        .all()
        .into_iter()
        .filter(|record| record.function_ref.name != "__info__")
        .map(|record| (function_fq_name(&record, &modules), record.arity))
        .collect::<Vec<_>>();
    names.sort();
    assert!(
        names.contains(&("Math.add".to_string(), 1))
            && names.contains(&("Math.add".to_string(), 2))
            && names.contains(&("User.run".to_string(), 0)),
        "source publication should define the provider surface before saving a body that calls an exact import: {names:?}"
    );

    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "rooting User.run should pull Math because the imported add/2 is actually used",
    );
    let mut names = functions
        .all()
        .into_iter()
        .filter(|record| record.function_ref.name != "__info__")
        .map(|record| (function_fq_name(&record, &modules), record.arity))
        .collect::<Vec<_>>();
    names.sort();
    assert!(
        names.contains(&("Math.add".to_string(), 1))
            && names.contains(&("Math.add".to_string(), 2))
            && names.contains(&("User.run".to_string(), 0)),
        "root demand should keep the classified exact import callable without reverting to a guessed target: {names:?}"
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

    match compiler.drive() {
        DriveOutcome::Fatal {
            job: Job::LowerFunction(_),
        } => {}
        other => panic!("unrequired remote macro call should reach macro-free lowering as a fatal error: {other:?}"),
    }
    assert_eq!(
        capture.count(&["fz", "compiler2", "macro", "expanded"]),
        0,
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
fn compiler2_import_only_missing_target_is_unresolved_when_used() {
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
    match compiler.drive() {
        DriveOutcome::Fatal { job } if job == Job::DefineModule(module_ids[0]) => {}
        other => panic!("missing exact import should fail while publishing the importing body: {other:?}"),
    }
    assert!(
        capture.contains(&["fz", "diag", "error"]),
        "using a missing exact import should emit the deferred missing-export diagnostic"
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("missing exact import diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::RESOLVE_UNKNOWN_IMPORT.0,
        "missing exact imports should reuse the module-export diagnostic shape"
    );
    assert_eq!(
        metadata_str(&diagnostic, "message"),
        "module `Math` does not export `missing/1`",
        "missing exact imports should name the unresolved export"
    );
}

#[test]
fn compiler2_import_all_waits_for_defined_module_surface() {
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
    assert_resolved(compiler.drive(), "third drive should define Math before retrying User");
    let mut names = functions
        .all()
        .into_iter()
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
fn compiler2_import_except_waits_for_defined_module_surface() {
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
    assert_resolved(compiler.drive(), "third drive should define Math before retrying User");
    let mut names = functions
        .all()
        .into_iter()
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

    fn all(&self) -> Vec<(FactKey, u64)> {
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
            | crate::compiler2::ModuleState::Indexed(source) => {
                if source.parent == ModuleId::GLOBAL {
                    source.local_name.clone()
                } else {
                    format!("{}.{}", modules.qualified_name(source.parent), source.local_name)
                }
            }
            crate::compiler2::ModuleState::Placeholder => {
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
                    .push(effects.outputs.clone());
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
        let Some(return_ty) = event
            .metadata
            .get("return_ty")
            .and_then(|value| value.downcast_ref::<Ty>())
        else {
            return;
        };
        self.defs.borrow_mut().push(ReturnTypeRecord {
            activation: activation.clone(),
            return_ty: *return_ty,
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

fn lowered_body(capture: &LoweredBodyCapture, function: FunctionId) -> LoweredBody {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("lowered_body.defined for {function:?}"))
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
            if program.executables[*target].key.activation.function == callee =>
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

fn backend_callable_entry_uses(program: &BackendProgram) -> HashSet<usize> {
    let mut out = HashSet::new();
    for executable in &program.executables {
        match &executable.body {
            crate::compiler2::BackendBody::Extern { .. } => {}
            crate::compiler2::BackendBody::Clauses { clauses, entries, .. } => {
                for clause in clauses {
                    collect_backend_callable_entry_uses(entries, clause.entry, &mut out);
                }
            }
        }
    }
    out
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

fn native_callable_constructor_uses(program: &NativeProgram) -> HashSet<usize> {
    let mut out = HashSet::new();
    for body in &program.bodies {
        for entries in body.callable_constructors.values() {
            out.extend(entries.iter().copied());
        }
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
        && left.callable_entries == right.callable_entries
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
        && left.external_call_edges.len() == right.external_call_edges.len()
        && left
            .external_call_edges
            .iter()
            .zip(right.external_call_edges.iter())
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
            },
            IrTerm::CallClosure {
                ident: right_ident,
                closure: right_closure,
                args: right_args,
                continuation: right_cont,
            },
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_closure == right_closure
                && left_args == right_args
                && native_conts_match(left_cont, right_cont)
        }
        (
            IrTerm::TailCallClosure {
                ident: left_ident,
                closure: left_closure,
                args: left_args,
            },
            IrTerm::TailCallClosure {
                ident: right_ident,
                closure: right_closure,
                args: right_args,
            },
        ) => {
            native_callsite_idents_match(left_ident, right_ident)
                && left_closure == right_closure
                && left_args == right_args
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

fn collect_backend_callable_entry_uses(
    entries: &[BackendEntry],
    entry_id: crate::compiler2::ControlEntryId,
    out: &mut HashSet<usize>,
) {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        BackendTail::DirectCall { args, .. } | BackendTail::ClosureCall { args, .. } => {
            for arg in args {
                out.extend(arg.callable_entries.iter().copied());
            }
        }
        BackendTail::If {
            then_entry, else_entry, ..
        } => {
            collect_backend_callable_entry_uses(entries, *then_entry, out);
            collect_backend_callable_entry_uses(entries, *else_entry, out);
        }
        BackendTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_backend_callable_entry_uses(entries, *arm_entry, out);
            }
            collect_backend_callable_entry_uses(entries, dispatch.miss_entry, out);
        }
        BackendTail::Receive(receive) => {
            for clause in &receive.clauses {
                collect_backend_callable_entry_uses(entries, clause.entry, out);
            }
            if let Some(after) = &receive.after {
                collect_backend_callable_entry_uses(entries, after.entry, out);
            }
        }
        BackendTail::Value { .. } | BackendTail::Halt { .. } => {}
    }
}

fn direct_call_in_body(body: LoweredBody, callee: FunctionId) -> (CallSiteId, ValueId) {
    match body {
        LoweredBody::Extern { .. } => panic!("expected clause body with a direct call"),
        LoweredBody::Clauses { clauses, entries, .. } => {
            for clause in clauses {
                if let Some(found) = direct_call_in_entry(&entries, clause.entry, callee) {
                    return found;
                }
            }
            panic!("direct call to {callee:?} not found in lowered body")
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
            callee: crate::compiler2::DirectCallee::Function(function),
            ..
        } if *function == callee => Some((*callsite, *value)),
        crate::compiler2::LoweredTail::If {
            then_entry, else_entry, ..
        } => direct_call_in_entry(entries, *then_entry, callee)
            .or_else(|| direct_call_in_entry(entries, *else_entry, callee)),
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
