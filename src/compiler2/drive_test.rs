use super::{AppliedStep, CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, Job, RootSubmission};
use crate::compiler2::drive::JobEffects;
use crate::compiler2::{
    ActivationKey, CallSiteKey, CallSiteSummary, ExecutableKey, FactKey, FactValue, FunctionId, FunctionRef,
    LoweredBody, LoweredStep, MaterializedProgram, Module, ModuleId, SelectedCallee, SemanticClosure,
};
use crate::diag::codes;
use crate::dispatch_matrix::Region;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::telemetry::handler::{Event, EventKind, Handler};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use crate::types::{Ty, Types};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

type OutputFacts = Vec<(FactKey, FactValue)>;
type JobOutputMap = Rc<RefCell<HashMap<Job, Vec<OutputFacts>>>>;
type AppliedSteps = Rc<RefCell<Vec<AppliedStep<Job, FactKey>>>>;
type EntryDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<PatternDispatchPlan>>>>;
type GuardDispatchMap = Rc<RefCell<HashMap<FunctionId, Vec<PatternGuardDispatch>>>>;
type LoweredBodyDefs = Rc<RefCell<HashMap<FunctionId, Vec<LoweredBody>>>>;
type SpanJobs = Rc<RefCell<HashMap<u64, Job>>>;
type FunctionDefs = Rc<RefCell<Vec<FunctionDefinedRecord>>>;
type ModuleDefs = Rc<RefCell<HashMap<ModuleId, Vec<Module>>>>;
type CallsiteDefs = Rc<RefCell<Vec<CallsiteDefinedRecord>>>;
type SemanticClosedDefs = Rc<RefCell<Vec<SemanticClosedRecord>>>;
type MaterializedProgramDefs = Rc<RefCell<Vec<MaterializedProgramRecord>>>;
type ReturnTypeDefs = Rc<RefCell<Vec<ReturnTypeRecord>>>;

fn presence(fact: FactKey, revision: u64) -> (FactKey, FactValue) {
    (fact, FactValue::presence(revision))
}

#[test]
fn compiler2_runtime_prelude_does_not_run_frontend_before_drive() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
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
fn compiler2_index_code_defines_owned_functions_without_lowering_or_activating_bodies() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let source = format!(
        "{}\nfn foo(), do: 42\n",
        include_str!("../../fixtures/quicksort/input.fz")
    );

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
        "function.defined should publish the expected top-level definitions"
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        5,
        "indexing should emit one function.defined event per function"
    );
    assert!(
        capture
            .find(&["fz", "compiler2", "function", "defined"])
            .into_iter()
            .all(|event| event.metadata.len() == 0),
        "generic capture should not durable-copy synthesized function definition metadata"
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
        outputs.contains(&presence(FactKey::CodeIndexed(code_id), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    let _code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
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
            .any(|step| step.coalesced.contains(&Job::CheckSemanticClosure(root_id))),
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
        lower_outputs.contains(&presence(FactKey::LoweredBody(main_id), 1)),
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
        seed_outputs.contains(&presence(FactKey::RootEntry(root_id), 1)),
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
        seed_outputs.contains(&presence(
            FactKey::Executable(ExecutableKey {
                activation: ActivationKey {
                    root: root_id,
                    function: main_id,
                    input: Vec::new(),
                },
                need: ExecutableNeed::Value,
            }),
            1,
        )),
        "SeedRoot should publish the entry executable request"
    );

    let closure_outputs = outputs
        .take(Job::CheckSemanticClosure(root_id))
        .expect("CheckSemanticClosure job effects");
    assert!(
        !closure_outputs
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::Activation(_))),
        "semantic closure should read activation facts rather than publish them"
    );
    assert!(
        !closure_outputs
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::Executable(_))),
        "semantic closure should read executable facts rather than publish them"
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
            .stops_matching(|job| matches!(job, Job::CheckSemanticClosure(_)))
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
fn compiler2_runtime_refs_pull_only_the_reached_runtime_modules() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("runtime_refs.fz".to_string()),
        text: "fn main(), do: dbg(Process.heap_alloc_stats())\n".to_string(),
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
fn compiler2_unused_runtime_library_stays_cold() {
    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("no_runtime.fz".to_string()),
        text: "fn main(), do: 42\n".to_string(),
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
    use crate::types::Types;

    let tel = ConfiguredTelemetry::new();
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
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
        text: r#"
fn main(), do: Enum.reduce([1, 2, 3, 4, 5], 0, fn (x, acc) -> x + acc end)
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
        "Enum.reduce should settle runtime protocol dispatch and closure calls in one semantic closure",
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

    let main_lowered = outputs
        .take(Job::LowerFunction(main_id))
        .expect("LowerFunction job effects for main/0");
    assert!(
        main_lowered.contains(&presence(FactKey::FunctionDefined(user_reducer_id), 1)),
        "lowering main/0 should surface its generated reducer function through job effects",
    );
    let enum_lowered = outputs
        .take(Job::LowerFunction(enum_reduce_id))
        .expect("LowerFunction job effects for Enum.reduce/3");
    assert!(
        enum_lowered.contains(&presence(FactKey::FunctionDefined(bridge_reducer_id), 1)),
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

    let mut t = crate::types::new();
    let int = t.int();
    let done = t.atom_lit("done");
    let done_int = t.tuple(&[done, int.clone()]);
    assert!(
        t.is_equivalent(&returns.last_for_function(root_id, main_id).return_ty, &int),
        "main/0 should settle to int for the reduced accumulator",
    );
    assert!(
        t.is_equivalent(&returns.last_for_function(root_id, enum_reduce_id).return_ty, &int),
        "Enum.reduce/3 should settle to int for the rooted list reducer fixture",
    );
    assert!(
        t.is_equivalent(&returns.last_for_function(root_id, user_reducer_id).return_ty, &int),
        "the user reducer lambda should settle to int under the selected list reduction path",
    );
    assert!(
        t.is_equivalent(
            &returns.last_for_function(root_id, list_impl_reduce_id).return_ty,
            &done_int,
        ),
        "the selected List-backed protocol callback should settle to {{:done, int}}",
    );
}

#[test]
fn compiler2_enum_reduce_operator_ref_activates_kernel_plus() {
    use crate::types::Types;

    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
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

    let mut t = crate::types::new();
    let int = t.int();
    let tuple_int = t.tuple(&[int.clone(), int.clone()]);
    assert!(
        t.is_equivalent(&returns.last_for_function(root_id, main_id).return_ty, &tuple_int),
        "main/0 should settle to {{int, int}} for the operator-ref reducer fixture",
    );
    assert!(
        t.is_equivalent(&returns.last_for_function(root_id, kernel_plus_id).return_ty, &int),
        "Kernel.+/2 should retain a concrete int activation under the operator-ref reducer fixture",
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let materialized = MaterializedProgramCapture::new();
    tel.attach(
        &["fz", "compiler2", "materialized_program", "defined"],
        materialized.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
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
fn compiler2_materialization_freezes_only_the_selected_enum_reduce_path() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
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
        text: r#"
fn main(), do: Enum.reduce([1, 2, 3, 4, 5], 0, fn (x, acc) -> x + acc end)
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
            .any(|edge| edge.callee == SelectedCallee::Function(list_impl_reduce_id)),
        "materialization should freeze Enum.reduce/3's protocol call to the selected List-backed callback",
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
            .any(|edge| edge.callee == SelectedCallee::Function(user_reducer_id)),
        "materialization should freeze the bridge reducer call to the user reducer executable",
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
fn compiler2_semantic_analysis_derives_reachable_call_edges_and_tuple_return_need() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
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
                && record.summary.callee == SelectedCallee::Function(qsort_id)
        }),
        "semantic analysis should publish the rooted main/0 -> qsort/1 direct edge"
    );
    assert!(
        callsites.iter().any(|record| {
            record.key.activation.root == root_id
                && record.key.activation.function == qsort_id
                && record.summary.callee == SelectedCallee::Function(partition_id)
                && record.summary.need == ExecutableNeed::TupleFields(2)
        }),
        "semantic analysis should mark qsort/1's partition/4 call as needing tuple fields"
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
    use crate::types::Types;

    let tel = ConfiguredTelemetry::new();
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
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

    let mut t = crate::types::new();
    let int = t.int();
    let any = t.any();
    let list_int = t.list(int.clone());
    let nonempty_int = t.non_empty_list(int.clone());
    let list_any = t.list(any);

    assert!(
        activations.contains(&ActivationKey {
            root: root_id,
            function: main_id,
            input: Vec::new(),
        }),
        "root closure should keep the entry activation in the settled frontier"
    );
    assert!(
        activations.contains(&ActivationKey {
            root: root_id,
            function: qsort_id,
            input: vec![nonempty_int],
        }),
        "root closure should keep qsort/1's non-empty recursive activation"
    );
    assert!(
        activations.contains(&ActivationKey {
            root: root_id,
            function: qsort_id,
            input: vec![list_int.clone()],
        }),
        "root closure should keep qsort/1's widened list activation"
    );
    assert!(
        activations.contains(&ActivationKey {
            root: root_id,
            function: partition_id,
            input: vec![int.clone(), list_int.clone(), list_any.clone(), list_any.clone()],
        }),
        "root closure should keep partition/4's recursive activation"
    );
    assert!(
        activations.contains(&ActivationKey {
            root: root_id,
            function: append_id,
            input: vec![list_int, list_any],
        }),
        "root closure should keep append/2's recursive activation"
    );
    assert!(
        activations.len() <= 12,
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
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
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
        text: "fn foo(), do: 99\n".to_string(),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo_v1.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
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
        text: "fn foo(), do: 42\nfn main(), do: foo()\n".to_string(),
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
        text: r#"
fn positive(n), do: n > 0
fn wanted(n) when positive(n), do: :yes
fn wanted(_), do: :no
fn other(n) when n > 0, do: :yes
fn other(_), do: :no
fn main(), do: wanted(1)
fn other_main(), do: other(1)
"#
        .to_string(),
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
        text: "fn positive(n), do: n >= 0\n".to_string(),
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

    let submitted = capture
        .last(&["fz", "compiler2", "root", "submitted"])
        .expect("root submitted event");
    let function_id = match submitted.measurements.get("function_id") {
        Some(Value::U64(id)) => FunctionId::from_u32(*id as u32),
        other => panic!("root submission missing function_id measurement: {other:?}"),
    };

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
        text: "fn main(), do: 42\n".to_string(),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_only.fz".to_string()),
        text: "fn main(), do: 42\n".to_string(),
    });
    let _root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "first drive should seed the initial root");
    let closure_checks_before = outputs
        .stops_matching(|job| matches!(job, Job::CheckSemanticClosure(_)))
        .len();
    let lowered_before = outputs.stops_matching(|job| matches!(job, Job::LowerFunction(_))).len();
    let seed_stops_before = outputs.stops_matching(|job| matches!(job, Job::SeedRoot(_))).len();
    assert!(
        seed_stops_before >= 2,
        "entry seeding should settle before later code arrives"
    );

    let late_code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/late_foo.fz".to_string()),
        text: "fn foo(), do: 42\n".to_string(),
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
            .any(|(fact, _)| *fact == FactKey::FunctionDefined(foo_id)),
        "late code should define foo/0 without an explicit ScopeCode demand"
    );
    assert_eq!(
        outputs.stops_matching(|job| matches!(job, Job::SeedRoot(_))).len(),
        seed_stops_before,
        "late unrelated code should not reseed the existing root"
    );
    assert_eq!(
        outputs
            .stops_matching(|job| matches!(job, Job::CheckSemanticClosure(_)))
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/local_lambda.fz".to_string()),
        text: "fn main(), do: (fn (x) -> x + 1 end).(41)\n".to_string(),
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
        lower_outputs.contains(&presence(FactKey::LoweredBody(main_id), 1)),
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
        generated_outputs.contains(&presence(FactKey::LoweredBody(generated[0]), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let semantic = SemanticClosedCapture::new();
    tel.attach(&["fz", "compiler2", "semantic_closed", "defined"], semantic.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_lambda_recursion_keying.fz".to_string()),
        text: r#"
fn build(acc, n) do
  if n == 0 do
    acc
  else
    step = fn () -> build([n | acc], n - 1) end
    step.()
  end
end

fn main(), do: dbg(build([], 5))
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
            .contains(&presence(FactKey::Recursive(build_id), 1)),
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

    let mut types = crate::types::new();
    let empty = types.empty_list();
    let expected_acc = types.convergence_class(&empty);
    assert!(
        types.is_equivalent(&build_activations[0].input[0], &expected_acc),
        "build/2 accumulator should use the recursive convergence class",
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/lowered_clause_projections.fz".to_string()),
        text: r#"
fn positive(n), do: n > 0
fn wanted({:ok, {n, _}}) when positive(n), do: n
fn wanted(_), do: 0
"#
        .to_string(),
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
        lowered_outputs.contains(&presence(FactKey::LoweredBody(wanted_id), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/lambda_capture_inputs.fz".to_string()),
        text: "fn main(k), do: fn (x) -> x + k end\n".to_string(),
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
        lowered_outputs.contains(&presence(FactKey::LoweredBody(lambda_id), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let bodies = LoweredBodyCapture::new();
    tel.attach(&["fz", "compiler2", "lowered_body", "defined"], bodies.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/lowered_local_match.fz".to_string()),
        text: r#"
fn main() do
  {:ok, n} = {:ok, 42}
  n
end
"#
        .to_string(),
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
        lowered_outputs.contains(&presence(FactKey::LoweredBody(main_id), 1)),
        "lowering main/0 should publish its lowered body fact",
    );

    let body = lowered_body(&bodies, main_id);
    let LoweredBody::Clauses { clauses, .. } = body else {
        panic!("main/0 should lower as clauses");
    };
    assert_eq!(
        clauses[0].projections.len(),
        0,
        "main/0 has no head params to project after entry dispatch",
    );
    assert!(
        clauses[0].body.steps.iter().any(|step| {
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let guard_defs = GuardDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "guard_dispatch", "defined"], guard_defs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_helpers.fz".to_string()),
        text: r#"
fn positive(n), do: n > 0
fn wanted(n), do: positive(n)
"#
        .to_string(),
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
        positive_outputs.contains(&presence(FactKey::GuardDispatch(positive_id), 1)),
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
        wanted_outputs.contains(&presence(FactKey::GuardDispatch(wanted_id), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let guard_defs = GuardDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "guard_dispatch", "defined"], guard_defs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_destructure.fz".to_string()),
        text: r#"
fn positive(n), do: n > 0
fn within(limit, n), do: positive(n + limit)
fn wanted({:ok, {n, _}}), do: within(1, n)
fn wanted(_), do: false
"#
        .to_string(),
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
        wanted_outputs.contains(&presence(FactKey::GuardDispatch(wanted_id), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_cycle.fz".to_string()),
        text: r#"
fn a(n), do: b(n)
fn b(n), do: a(n)
"#
        .to_string(),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_impure.fz".to_string()),
        text: r#"
fn bad(n) do
  if n > 0 do
    true
  else
    false
  end
end
"#
        .to_string(),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let entry_defs = EntryDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "entry_dispatch", "defined"], entry_defs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_aliases.fz".to_string()),
        text: r#"
defmodule Sample do
  @type count :: integer

  fn positive(n), do: n > 0

  fn wanted(n :: count) when positive(n), do: {:pos, n}
  fn wanted(0), do: :zero
  fn wanted(_), do: :fallback
end
"#
        .to_string(),
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
        helper_outputs.contains(&presence(FactKey::GuardDispatch(positive_id), 1)),
        "helper planning should automatically publish the nested guard-dispatch fact",
    );
    let wanted_outputs = outputs
        .take(Job::PlanEntryDispatch(wanted_id))
        .expect("PlanEntryDispatch job effects for wanted/1");
    assert!(
        wanted_outputs.contains(&presence(FactKey::EntryDispatch(wanted_id), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let entry_defs = EntryDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "entry_dispatch", "defined"], entry_defs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_single_clause.fz".to_string()),
        text: "fn wanted(n), do: n\n".to_string(),
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
        wanted_outputs.contains(&presence(FactKey::EntryDispatch(wanted_id), 1)),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let entry_defs = EntryDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "entry_dispatch", "defined"], entry_defs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_blast_radius_v1.fz".to_string()),
        text: r#"
fn positive(n), do: n > 0
fn wanted(n) when positive(n), do: true
fn wanted(_), do: false
fn other(n) when n > 0, do: true
fn other(_), do: false
"#
        .to_string(),
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
    let _ = entry_dispatch(&entry_defs, wanted_id);
    let _ = entry_dispatch(&entry_defs, other_id);

    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_dispatch_blast_radius_v2.fz".to_string()),
        text: "fn positive(n), do: n >= 0\n".to_string(),
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
        helper_outputs.contains(&presence(FactKey::GuardDispatch(positive_id), 2)),
        "helper reification should publish a revised guard-dispatch fact",
    );
    let wanted_outputs = outputs
        .take(Job::PlanEntryDispatch(wanted_id))
        .expect("dependent wanted/1 entry dispatch should rerun");
    assert!(
        wanted_outputs.contains(&presence(FactKey::EntryDispatch(wanted_id), 2)),
        "dependent wanted/1 entry dispatch should republish with a new revision",
    );
    assert!(
        outputs.take(Job::PlanEntryDispatch(other_id)).is_none(),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/nested_modules.fz".to_string()),
        text: r#"
defmodule X do
  defmodule Y do
    defmodule Z do
      fn func(), do: 20
    end
  end
end
"#
        .to_string(),
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
        .next()
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
        indexed_outputs.contains(&presence(FactKey::CodeIndexed(code_id), 1)),
        "nested indexing should include the final code-indexed fact"
    );
}

#[test]
fn compiler2_import_only_binds_exact_refs_and_pulls_provider_when_used() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only.fz".to_string()),
        text: r#"
defmodule User do
  import Math, only: [add: 1, add: 2]
  fn run(), do: add(20, 22)
end

defmodule Math do
  fn add(a), do: a
  fn add(a, b), do: a + b
end
"#
        .to_string(),
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
        "third drive should define User without warming exact-import providers",
    );
    let mut names = functions
        .all()
        .into_iter()
        .map(|record| (function_fq_name(&record, &modules), record.arity))
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        vec![("User.run".to_string(), 0)],
        "defining the importing module should not define exact-import providers"
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
        "demand should pull the provider surface when an exact import is reached"
    );
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
        text: r#"
defmodule User do
  import Math, only: [missing: 1]
  fn run(), do: missing(20)
end

defmodule Math do
  fn add(a), do: a
end
"#
        .to_string(),
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
        "third drive should define User without validating cold exact imports",
    );

    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    match compiler.drive() {
        DriveOutcome::Unresolved { waits } => {
            assert!(
                waits
                    .iter()
                    .any(|wait| matches!(wait.fact, FactKey::FunctionDefined(_))),
                "using a missing exact import should leave precise function-definition demand unresolved"
            );
        }
        other => panic!("missing exact import should become unresolved demand: {other:?}"),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_all.fz".to_string()),
        text: r#"
defmodule User do
  import Math
  fn run(), do: add(20, 22)
end

defmodule Math do
  fn add(a), do: a
  fn add(a, b), do: a + b
end
"#
        .to_string(),
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
    tel.attach(&["fz", "compiler2", "function", "defined"], functions.handler());
    let modules = ModuleCapture::new();
    tel.attach(&["fz", "compiler2", "module", "defined"], modules.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_except.fz".to_string()),
        text: r#"
defmodule User do
  import Math, except: [add: 1]
  fn run(), do: add(20, 22)
end

defmodule Math do
  fn add(a), do: a
  fn add(a, b), do: a + b
  fn sub(a, b), do: a - b
end
"#
        .to_string(),
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
struct ReturnTypeRecord {
    activation: ActivationKey,
    return_ty: Ty,
}

struct FunctionCapture {
    defs: FunctionDefs,
}

struct ModuleCapture {
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

    fn stop(&self, job: Job) -> JobSpanStop {
        self.stops
            .borrow()
            .iter()
            .find(|stop| stop.job == job)
            .cloned()
            .unwrap_or_else(|| panic!("job stop event for {job:?}"))
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
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(FunctionCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn all(&self) -> Vec<FunctionDefinedRecord> {
        self.defs.borrow().clone()
    }

    fn id(&self, name: &str, arity: u64) -> FunctionId {
        self.defs
            .borrow()
            .iter()
            .find(|record| record.function_ref.name == name && record.arity == arity)
            .map(|record| record.function_id)
            .unwrap_or_else(|| panic!("function.defined for {name}/{arity}"))
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
        match &module.state {
            crate::compiler2::ModuleState::Defined { source, .. }
            | crate::compiler2::ModuleState::Scoped { source, .. }
            | crate::compiler2::ModuleState::Indexed(source) => {
                if source.parent == ModuleId::GLOBAL {
                    source.local_name.clone()
                } else {
                    format!("{}.{}", self.qualified_name(source.parent), source.local_name)
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

    fn take(&self, function: FunctionId) -> Option<PatternGuardDispatch> {
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

    fn take(&self, function: FunctionId) -> Option<PatternDispatchPlan> {
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
        if event.name != ["fz", "compiler2", "function", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(Value::U64(function_id)) = event.measurements.get("function_id") else {
            return;
        };
        let Some(Value::U64(module_id)) = event.measurements.get("module_id") else {
            return;
        };
        let owner_module_id = match event.measurements.get("owner_module_id") {
            Some(Value::U64(owner_module_id)) => Some(ModuleId::from_u32(*owner_module_id as u32)),
            _ => None,
        };
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
        let owner_function_id = match event.measurements.get("owner_function_id") {
            Some(Value::U64(owner)) => Some(FunctionId::from_u32(*owner as u32)),
            _ => None,
        };
        self.defs.borrow_mut().push(FunctionDefinedRecord {
            function_id: FunctionId::from_u32(*function_id as u32),
            module_id: ModuleId::from_u32(*module_id as u32),
            owner_module_id,
            arity: *arity,
            clauses: *clauses,
            owner_function_id,
            function_ref: function_ref.clone(),
        });
    }
}

impl Handler for ModuleCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "module", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(Value::U64(module_id)) = event.measurements.get("module_id") else {
            return;
        };
        let Some(module) = event
            .metadata
            .get("module")
            .and_then(|value| value.downcast_ref::<Module>())
        else {
            return;
        };
        self.defs
            .borrow_mut()
            .entry(ModuleId::from_u32(*module_id as u32))
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
        let Some(Value::U64(root_id)) = event.measurements.get("root_id") else {
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
            root_id: crate::compiler2::RootId::from_u32(*root_id as u32),
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
            return_ty: return_ty.clone(),
        });
    }
}

impl Handler for MaterializedProgramCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "materialized_program", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(Value::U64(root_id)) = event.measurements.get("root_id") else {
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
            root_id: crate::compiler2::RootId::from_u32(*root_id as u32),
            program: program.clone(),
        });
    }
}

impl Handler for GuardDispatchCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "guard_dispatch", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(Value::U64(function_id)) = event.measurements.get("function_id") else {
            return;
        };
        let Some(dispatch) = event
            .metadata
            .get("dispatch")
            .and_then(|value| value.downcast_ref::<PatternGuardDispatch>())
        else {
            return;
        };
        self.dispatches
            .borrow_mut()
            .entry(FunctionId::from_u32(*function_id as u32))
            .or_default()
            .push(dispatch.clone());
    }
}

impl Handler for EntryDispatchCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "entry_dispatch", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(Value::U64(function_id)) = event.measurements.get("function_id") else {
            return;
        };
        let Some(plan) = event
            .metadata
            .get("plan")
            .and_then(|value| value.downcast_ref::<PatternDispatchPlan>())
        else {
            return;
        };
        self.plans
            .borrow_mut()
            .entry(FunctionId::from_u32(*function_id as u32))
            .or_default()
            .push(plan.clone());
    }
}

impl Handler for LoweredBodyCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "lowered_body", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(Value::U64(function_id)) = event.measurements.get("function_id") else {
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
            .entry(FunctionId::from_u32(*function_id as u32))
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

fn guard_dispatch(capture: &GuardDispatchCapture, function: FunctionId) -> PatternGuardDispatch {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("guard_dispatch.defined for {function:?}"))
}

fn entry_dispatch(capture: &EntryDispatchCapture, function: FunctionId) -> PatternDispatchPlan {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("entry_dispatch.defined for {function:?}"))
}

fn lowered_body(capture: &LoweredBodyCapture, function: FunctionId) -> LoweredBody {
    capture
        .take(function)
        .unwrap_or_else(|| panic!("lowered_body.defined for {function:?}"))
}

fn plan_has_nested_guard_dispatch(plan: &PatternDispatchPlan) -> bool {
    plan.guards.iter().any(expr_has_nested_dispatch)
}

fn plan_body_has_type_question(plan: &PatternDispatchPlan, body_id: u32) -> bool {
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

fn guard_dispatch_has_nested_dispatch(dispatch: &PatternGuardDispatch) -> bool {
    dispatch.plan.guards.iter().any(expr_has_nested_dispatch) || dispatch.bodies.iter().any(expr_has_nested_dispatch)
}

fn expr_has_nested_dispatch(expr: &PatternGuardExpr) -> bool {
    match expr {
        PatternGuardExpr::Dispatch { .. } => true,
        PatternGuardExpr::Unary { expr, .. } => expr_has_nested_dispatch(expr),
        PatternGuardExpr::Binary { lhs, rhs, .. } => expr_has_nested_dispatch(lhs) || expr_has_nested_dispatch(rhs),
        PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => false,
    }
}

fn guard_dispatch_has_binary_nested_input(dispatch: &PatternGuardDispatch) -> bool {
    dispatch.bodies.iter().any(expr_has_binary_nested_input)
}

fn expr_has_binary_nested_input(expr: &PatternGuardExpr) -> bool {
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

fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

fn function_id(capture: &FunctionCapture, name: &str, arity: u64) -> FunctionId {
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
                && function_module_name(record, modules) == module_name
        })
        .map(|record| record.function_id)
        .unwrap_or_else(|| panic!("function.defined for {module_name}.{name}/{arity}"))
}

fn module_id(capture: &ModuleCapture, name: &str) -> ModuleId {
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
    modules.qualified_name(function.module_id)
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
