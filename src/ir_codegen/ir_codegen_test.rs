use super::*;
use crate::compiler::source::Span;
use crate::diag::Diagnostics;
use crate::exec::runtime::{DbgCapture, ExitRecord, ProcessExitCapture, Runtime};
use crate::frontend::compile_source_with_interface_table;
use crate::frontend::compile_source_with_types;
use crate::frontend::resolve::{InterfaceTable, flatten_modules};
use crate::fz_ir::{CallsiteIdent, DirectCallTarget, FnBuilder, FnId, Module, Prim, SpecId, Stmt, Term, Var};
use crate::ir_interp::run_main_with_plan;
use crate::ir_lower::lower_program;
use crate::ir_planner::fn_types::{CallEdgeTarget, ReturnDemand, SpecKey};
use crate::ir_planner::{ModulePlan, SpecPlan, materialize_program, plan_module_with_role};
use crate::modules::identity::{Mfa, ModuleName};
use crate::modules::interface::{InterfaceFn, ModuleInterface};
use crate::modules::pipeline::{CompileMode, PreparedExecutionGraph, checked_module_for_mode, prepare_execution_graph};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Telemetry, Value};
use crate::test_support::{
    assert_authoritative_planner_consistent, module_reachable_materialized_body_signals,
    runtime_graph_codegen_materialized_body_signals,
};
use crate::types::{DefaultTypes, KeySlot, Types, key_slots_from_tys};
use cranelift_codegen::ir::types;
use fz_runtime::any_value::debug::render_value;
use fz_runtime::any_value::{
    AnyValue, AnyValueRefPacking, FALSE_ATOM_ID, NIL_ATOM_ID, TRUE_ATOM_ID, ValueKind, bitstring_addr_from_tagged,
    bitstring_bytes_ptr,
};
use fz_runtime::heap::Schema;
use fz_runtime::ir_runtime::{frame_alloc_count_reset, frame_alloc_count_take};
use std::collections::{BTreeMap, BTreeSet, HashMap};

// `false` halts as its reserved atom ID; name the constant so test
// assertions stay readable.
const FALSE_HALT: i64 = FALSE_ATOM_ID as i64;

fn clif_hex_u64(word: u64) -> String {
    let raw = format!("{word:016x}");
    let mut formatted = String::from("0x");
    for (idx, chunk) in raw.as_bytes().chunks(4).enumerate() {
        if idx > 0 {
            formatted.push('_');
        }
        formatted.push_str(std::str::from_utf8(chunk).expect("hex chunk is utf8"));
    }
    formatted
}

fn packed_ref_tag_mask(kind: ValueKind) -> String {
    clif_hex_u64((kind.tag() as u64) << AnyValueRefPacking::current().tag_shift())
}

fn lower_src(src: &str) -> Module {
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower")
}

fn lower_resolved_src(src: &str) -> Module {
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let mut t = crate::types::new();
    let prog = flatten_modules(&mut t, prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("resolve");
    lower_program(&mut t, &prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("lower")
}

fn planner_roles(cap: &Capture) -> Vec<String> {
    cap.find(&["fz", "planner", "planned"])
        .into_iter()
        .map(|ev| match ev.metadata.get("role") {
            Some(Value::Str(role)) => role.to_string(),
            other => panic!("planner.planned event missing role metadata: {:?}", other),
        })
        .collect()
}

// DROP: old-world CompiledUnit/IR module container, no compiler2 analogue
#[test]
fn compiled_unit_carries_interface_contract_and_ir_code() {
    let m = lower_resolved_src(
        r#"
defmodule Math do
  fn add(x, y), do: x + y
end
"#,
    );
    let interface = ModuleInterface {
        name: ModuleName::from_segments(vec!["Math".to_string()]),
        imports: Vec::new(),
        exports: vec![InterfaceFn {
            name: "add".to_string(),
            arity: 2,
            specs: Vec::new(),
            name_span: Span::DUMMY,
        }],
        types: Vec::new(),
        protocols: Vec::new(),
        protocol_impls: Vec::new(),
        docs: None,
        fingerprint_inputs: vec!["export:Math.add/2".to_string()],
    };
    let unit = CompiledUnit::from_ir_module(m.clone(), Some(interface), Diagnostics::new());
    assert_eq!(unit.name.as_ref().unwrap().dotted(), "Math");
    assert_eq!(unit.code.fns.len(), m.fns.len());
    assert_eq!(unit.exports[0].name, "add");
    assert_eq!(
        unit.interface.as_ref().map(|interface| interface.name.dotted()),
        Some("Math".to_string())
    );
}

#[test]
fn runtime_metadata_link_merges_overlapping_atoms_and_schemas_deterministically() {
    let module_a = ModuleName::from_segments(vec!["A".to_string()]);
    let module_b = ModuleName::from_segments(vec!["B".to_string()]);
    let mut a_exports = BTreeMap::new();
    a_exports.insert("A.f/0".to_string(), 0);
    let unit_a = RuntimeUnitMetadata {
        module: Some(module_a.clone()),
        atoms: vec!["ok".to_string(), "shared".to_string()],
        schemas: vec![Schema::tuple_of_arity(2)],
        frame_sizes: vec![16],
        exported_symbols: a_exports,
        imported_refs: Vec::new(),
        static_closures: Vec::new(),
        halt_kinds: [(0, 1)].into_iter().collect(),
        entrypoints: RuntimeEntrypoints {
            resume: true,
            main: true,
            spawn: true,
            drain_dtor: true,
        },
    };
    let mut b_exports = BTreeMap::new();
    b_exports.insert("B.g/1".to_string(), 1);
    let unit_b = RuntimeUnitMetadata {
        module: Some(module_b),
        atoms: vec!["shared".to_string(), "error".to_string()],
        schemas: vec![Schema::tuple_of_arity(2), Schema::tuple_of_arity(3)],
        frame_sizes: vec![16, 24],
        exported_symbols: b_exports,
        imported_refs: vec![Mfa::new(module_a, "f", 0)],
        static_closures: vec![RuntimeStaticClosure {
            closure_schema_id: 2,
            fn_id: 1,
            halt_kind: 0,
        }],
        halt_kinds: [(1, 0)].into_iter().collect(),
        entrypoints: RuntimeEntrypoints {
            resume: true,
            main: false,
            spawn: true,
            drain_dtor: true,
        },
    };

    let image_ab = RuntimeImageMetadata::link_units(&[unit_a.clone(), unit_b.clone()]).expect("link");
    let image_ba = RuntimeImageMetadata::link_units(&[unit_b, unit_a]).expect("link");
    assert_eq!(image_ab.render_stable(), image_ba.render_stable());
    assert_eq!(
        image_ab.render_stable(),
        "atoms=error,ok,shared\n\
schemas=Tuple2:16:[0:AnyValue|8:AnyValue],Tuple3:24:[0:AnyValue|8:AnyValue|16:AnyValue]\n\
frames=16,16,24\n\
exports=A.f/0:0,B.g/1:2\n\
imports=A.f/0"
    );
    assert_eq!(image_ab.relocations[0].atom_ids, vec![1, 2]);
    assert_eq!(image_ab.relocations[1].atom_ids, vec![2, 0]);
    assert_eq!(image_ab.halt_kinds.get(&0), Some(&1));
    assert_eq!(image_ab.halt_kinds.get(&2), Some(&0));
}

#[test]
fn runtime_metadata_link_rejects_duplicate_exports() {
    let mut exports = BTreeMap::new();
    exports.insert("A.f/0".to_string(), 0);
    let unit = RuntimeUnitMetadata {
        module: None,
        atoms: Vec::new(),
        schemas: Vec::new(),
        frame_sizes: vec![8],
        exported_symbols: exports,
        imported_refs: Vec::new(),
        static_closures: Vec::new(),
        halt_kinds: BTreeMap::new(),
        entrypoints: RuntimeEntrypoints::default(),
    };
    let err = RuntimeImageMetadata::link_units(&[unit.clone(), unit]).unwrap_err();
    assert_eq!(err, RuntimeMetadataLinkError::DuplicateExport("A.f/0".to_string()));
}

#[test]
fn runtime_unit_metadata_carries_external_import_refs() {
    let mut module = Module::new();
    let export = Mfa::new(ModuleName::from_segments(vec!["Dep".to_string()]), "run", 1);
    let mut builder = FnBuilder::new(FnId(0), "User.run");
    let arg = builder.fresh_var();
    let entry = builder.block(vec![arg]);
    builder.set_terminator(
        entry,
        Term::TailCall {
            ident: CallsiteIdent::synthetic(),
            callee: DirectCallTarget::ProviderBoundary(export.clone()),
            args: vec![arg],
            is_back_edge: false,
        },
    );
    module.fn_idx.insert(FnId(0), module.fns.len());
    module.fns.push(builder.build());
    let meta = RuntimeUnitMetadata::from_ir_module(None, &module);
    assert_eq!(meta.imported_refs, vec![export]);
}

// DROP: old-world unresolved external call validation, no compiler2 analogue
#[test]
fn codegen_rejects_unresolved_external_module_calls() {
    let mut m = lower_src("fn main(), do: 0");
    let export = Mfa::new(ModuleName::from_segments(vec!["Dep".to_string()]), "run", 0);
    let main_id = m.fn_by_name("main").unwrap().id;
    let main_idx = m.fn_idx[&main_id];
    let entry = m.fns[main_idx].entry;
    m.fns[main_idx].blocks[entry.0 as usize].terminator = Term::TailCall {
        ident: CallsiteIdent::synthetic(),
        callee: DirectCallTarget::ProviderBoundary(export),
        args: Vec::new(),
        is_back_edge: false,
    };
    let mut t = crate::types::new();
    let plan = plan_module_with_role(&mut t, &m, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    let err = match compile_planned(&mut t, &m, &plan, &crate::telemetry::ConfiguredTelemetry::new()) {
        Ok(_) => panic!("expected unresolved external call error"),
        Err(err) => err,
    };
    assert_eq!(err.message, "unresolved provider-boundary call `Dep.run/0`");
}

fn link_test_unit(module: &str, exports: &[(&str, usize)], imports: Vec<Mfa>) -> (CompiledUnit, RuntimeUnitMetadata) {
    let module_name = ModuleName::from_segments(vec![module.to_string()]);
    let interface = ModuleInterface {
        name: module_name.clone(),
        imports: Vec::new(),
        exports: exports
            .iter()
            .map(|(name, arity)| InterfaceFn {
                name: (*name).to_string(),
                arity: *arity,
                specs: Vec::new(),
                name_span: Span::DUMMY,
            })
            .collect(),
        types: Vec::new(),
        protocols: Vec::new(),
        protocol_impls: Vec::new(),
        docs: None,
        fingerprint_inputs: exports
            .iter()
            .map(|(name, arity)| format!("export:{module}.{name}/{arity}"))
            .collect(),
    };
    let mut code = Module::new();
    for (idx, (name, arity)) in exports.iter().enumerate() {
        let fn_id = FnId(idx as u32);
        let mut builder = FnBuilder::new(fn_id, format!("{module}.{name}")).with_owner_module(module);
        let params = (0..*arity).map(|_| builder.fresh_var()).collect::<Vec<_>>();
        let entry = builder.block(params);
        builder.set_terminator(entry, Term::Halt(Var(0)));
        code.fn_idx.insert(fn_id, code.fns.len());
        code.fns.push(builder.build());
    }
    for import in &imports {
        let fn_id = FnId(code.fns.len() as u32);
        let mut builder = FnBuilder::new(fn_id, format!("__import_probe__.{}", import));
        let params = (0..import.arity).map(|_| builder.fresh_var()).collect::<Vec<_>>();
        let entry = builder.block(params.clone());
        builder.set_terminator(
            entry,
            Term::TailCall {
                ident: CallsiteIdent::synthetic(),
                callee: DirectCallTarget::ProviderBoundary(import.clone()),
                args: params,
                is_back_edge: false,
            },
        );
        code.fn_idx.insert(fn_id, code.fns.len());
        code.fns.push(builder.build());
    }
    let unit = CompiledUnit::from_ir_module(code, Some(interface), Diagnostics::new());
    let runtime = RuntimeUnitMetadata {
        module: Some(module_name),
        atoms: Vec::new(),
        schemas: Vec::new(),
        frame_sizes: vec![16],
        exported_symbols: exports
            .iter()
            .enumerate()
            .map(|(idx, (name, arity))| (format!("{module}.{name}/{arity}"), idx as u32))
            .collect(),
        imported_refs: imports,
        static_closures: Vec::new(),
        halt_kinds: BTreeMap::new(),
        entrypoints: RuntimeEntrypoints::default(),
    };
    (unit, runtime)
}

// PICKED: multi-module import and cross-module call resolves and runs
#[test]
fn linked_image_validates_two_module_program_and_runs() {
    let src = r#"
defmodule Math do
  fn add(x, y), do: x + y
end
defmodule User do
  import Math, only: [add: 2]
  fn run(), do: add(20, 22)
end
fn main(), do: User.run()
"#;
    let m = lower_resolved_src(src);
    let entry = m.fn_by_name("main").unwrap().id;
    let mut t = crate::types::new();
    let plan = plan_module_with_role(&mut t, &m, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    let compiled =
        compile_planned(&mut t, &m, &plan, &crate::telemetry::ConfiguredTelemetry::new()).expect("compile planned");
    let (math, _) = link_test_unit("Math", &[("add", 2)], Vec::new());
    let (user, _) = link_test_unit(
        "User",
        &[("run", 0)],
        vec![Mfa::new(ModuleName::from_segments(vec!["Math".to_string()]), "add", 2)],
    );

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "link"], capture.handler());
    let _ = (math, user);
    let image = CompiledImage::from_linked(&tel, 2, compiled);
    assert!(image.metadata().is_none());
    assert!(capture.contains(&["fz", "link", "succeeded"]));
    assert_eq!(image.run(&tel, entry), 42);
}

// PICKED: cross-module function call resolves and executes provider body
#[test]
fn linked_ir_units_rewrite_provider_boundary_calls_and_run_provider_body() {
    let mut t = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let math = compile_source_with_types(
        &mut t,
        "defmodule Math do\n  fn add(x, y), do: x + y\nend\n".to_string(),
        "math.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|err| panic!("math frontend: {:?}", err.diagnostics));
    let math_name = ModuleName::from_segments(vec!["Math".to_string()]);
    let math_interface = math
        ._prog
        .module_interfaces
        .get(&math_name)
        .cloned()
        .expect("math interface");

    let mut interfaces = InterfaceTable::new();
    interfaces.insert(math_name, math_interface.clone());
    let user = compile_source_with_interface_table(
        &mut t,
        "defmodule User do\n  import Math, only: [add: 2]\n  fn run(), do: add(20, 22)\nend\nfn main(), do: User.run()\n".to_string(),
        "user.fz".to_string(),
        interfaces,
        &tel,
    )
    .unwrap_or_else(|err| panic!("user frontend: {:?}", err.diagnostics));
    assert_eq!(user.module.external_call_edges().len(), 1);

    let math_unit = CompiledUnit::from_ir_module_with_plan(
        math.module,
        Some(math.module_plan),
        Some(math_interface),
        Diagnostics::new(),
    );
    let user_unit =
        CompiledUnit::from_ir_module_with_plan(user.module, Some(user.module_plan), None, Diagnostics::new());
    let linked = link_ir_units(&[math_unit, user_unit]).expect("link ir units");
    // Re-plan the linked module: after the linker rewrites provider-boundary
    // callsites to their resolved targets, a fresh plan must show no
    // provider-boundary call edges and no protocol-stub targets.
    let linked_plan = plan_module_with_role(&mut t, &linked, &tel, "test");
    assert!(
        !linked_plan.specs.values().any(|spec| {
            spec.call_edges
                .values()
                .any(|edge| matches!(edge.target, CallEdgeTarget::ProviderBoundary { .. }))
        }),
        "linked protocol edge should resolve to a local impl"
    );
    assert!(
        !linked_plan.specs.values().any(|spec| {
            spec.call_edges.values().any(|edge| {
                edge.local_target()
                    .map(|target| linked.fn_by_id(target.fn_id).name.starts_with("__protocol__"))
                    .unwrap_or(false)
            })
        }),
        "linked protocol edge must not target the protocol stub"
    );
    assert!(linked.external_call_edges().is_empty());
    let entry = linked.fn_by_name("main").expect("main").id;

    let compiled = compile_planned(&mut t, &linked, &linked_plan, &tel).expect("compile planned linked");
    let image = CompiledImage::from_linked(&tel, 2, compiled);

    assert_eq!(image.run(&tel, entry), 42);
}

// PICKED: cross-module protocol impl dispatch resolves to correct implementation
#[test]
fn linked_ir_units_preserve_provider_protocol_dispatch_plan() {
    let mut t = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let provider = compile_source_with_types(
        &mut t,
        r#"
defmodule Contracts do
  defprotocol Collectable do
    fn id(value)
  end

  defimpl Collectable, for: List do
    fn id(value), do: 42
  end
end
"#
        .to_string(),
        "contracts.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|err| panic!("provider frontend: {:?}", err.diagnostics));
    let contracts = ModuleName::from_segments(vec!["Contracts".to_string()]);
    let contracts_interface = provider._prog.module_interfaces[&contracts].clone();

    let mut interfaces = InterfaceTable::new();
    interfaces.insert(contracts, contracts_interface.clone());
    let user = compile_source_with_interface_table(
        &mut t,
        r#"
defmodule User do
  fn run(), do: Contracts.Collectable.id([1])
end
fn main(), do: User.run()
"#
        .to_string(),
        "user.fz".to_string(),
        interfaces,
        &tel,
    )
    .unwrap_or_else(|err| panic!("user frontend: {:?}", err.diagnostics));
    assert!(
        user.module
            .protocol_call_targets
            .values()
            .any(|target| target.callback == "id")
    );
    assert!(
        user.module_plan.specs.values().any(|spec| {
            spec.call_edges
                .values()
                .any(|edge| matches!(edge.target, CallEdgeTarget::ProviderBoundary { .. }))
        }),
        "user protocol call should be a provider-boundary call edge"
    );

    let provider_unit = CompiledUnit::from_ir_module_with_plan(
        provider.module,
        Some(provider.module_plan),
        Some(contracts_interface),
        Diagnostics::new(),
    );
    let user_unit =
        CompiledUnit::from_ir_module_with_plan(user.module, Some(user.module_plan), None, Diagnostics::new());
    let linked = link_ir_units(&[provider_unit, user_unit]).expect("link ir units");
    let entry = linked.fn_by_name("main").expect("main").id;
    let linked_plan = plan_module_with_role(&mut t, &linked, &tel, "test");
    let compiled = compile_planned(&mut t, &linked, &linked_plan, &tel).expect("compile planned linked");
    let image = CompiledImage::from_linked(&tel, 2, compiled);

    assert_eq!(image.run(&tel, entry), 42);
}

// PICKED: protocol dispatch over integer type calls correct impl
#[test]
fn native_static_protocol_dispatch_preserves_integer_abi() {
    let mut t = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let frontend = compile_source_with_types(
        &mut t,
        r#"
defprotocol Integerish do
  fn id(value)
end

defimpl Integerish, for: Integer do
  fn id(value), do: value + 1
end

fn main(), do: Integerish.id(41)
"#
        .to_string(),
        "integerish.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|err| panic!("frontend: {:?}", err.diagnostics));
    let entry = frontend.module.fn_by_name("main").expect("main").id;
    let compiled = compile_planned(&mut t, &frontend.module, &frontend.module_plan, &tel).expect("compile planned");
    let image = CompiledImage::from_linked(&tel, 1, compiled);

    assert_eq!(image.run(&tel, entry), 42);
}

/// fz-t1m.1.5 — a closed-union protocol receiver dispatches to the correct
/// impl per runtime value, identically in the interpreter and native codegen.
///
/// `describe`'s argument is the element type of `[7, [1, 2, 3]]`, i.e.
/// `integer | list(int)` — a closed union over the `Integer` and `List`
/// impls. The frontend rewrites the single stub call into a TypeTest/If
/// cascade. The impls return distinguishing values (the integer itself vs the
/// constant 100), so a swapped or missing arm would change the result:
/// `describe(7) + describe([1,2,3])` = `7 + 100` = `107`.
// PICKED: closed-union protocol dispatch selects correct impl per value type
#[test]
fn closed_union_protocol_dispatch_runs_in_interp_and_native() {
    const SRC: &str = r#"
defprotocol Sizer do
  fn size(value)
end

defimpl Sizer, for: Integer do
  fn size(value), do: value
end

defimpl Sizer, for: List do
  fn size(value), do: 100
end

fn describe(value), do: Sizer.size(value)

fn main() do
  case [7, [1, 2, 3]] do
    [a, b] -> describe(a) + describe(b)
    _ -> 0
  end
end
"#;
    let mut t = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let frontend = compile_source_with_types(&mut t, SRC.to_string(), "sizer.fz".to_string(), &tel)
        .unwrap_or_else(|err| panic!("frontend: {:?}", err.diagnostics));
    let entry = frontend.module.fn_by_name("main").expect("main").id;

    // Interpreter path — runs the frontend module directly.
    let interp = crate::ir_interp::run_main(&tel, &frontend.module).expect("interp run");
    assert_eq!(interp, 107, "interpreter protocol dispatch");

    // Native path — same module through codegen.
    let compiled = compile_planned(&mut t, &frontend.module, &frontend.module_plan, &tel).expect("compile planned");
    let image = CompiledImage::from_linked(&tel, 1, compiled);
    assert_eq!(image.run(&tel, entry), 107, "native protocol dispatch");
}

// PICKED: Enum.count, member?, reduce, and Enumerable.reduce over lists
#[test]
fn runtime_enumerable_list_count_member_and_reduce() {
    let got = capture_main_with_runtime_graph(
        r#"
fn main() do
  dbg({
    Enum.count([1, 2, 3]),
    Enum.member?([1, 2, 3], 2),
    Enum.reduce([1, 2, 3], 0, fn (x, acc) -> acc + x end),
    Enumerable.reduce([1, 2, 3], {:cont, 0}, fn (x, acc) -> {:cont, acc + x} end)
  })
end
"#,
    );

    assert_eq!(got, vec!["{3, true, 6, {:done, 6}}"]);
}

// PICKED: Enum.to_list and Enum.map preserve list structure and elements
#[test]
fn runtime_enum_to_list_and_map_preserve_recursive_list_shape_native() {
    let got = capture_main_with_runtime_graph(
        r#"
fn main() do
  dbg(Enum.to_list([1, 2, 3]))
  dbg(Enum.map([1, 2, 3, 4], fn x -> x * 2 end))
end
"#,
    );

    assert_eq!(got, vec!["[1, 2, 3]", "[2, 4, 6, 8]"]);
}

// PICKED: Enum tier-0 fixture exercises basic Enum operations end-to-end
#[test]
fn runtime_enum_tier0_fixture_runs_native() {
    let got = capture_main_with_runtime_graph(include_str!("../../fixtures/enum_tier0/input.fz"));
    let expected = include_str!("../../fixtures/enum_tier0/expected.txt")
        .lines()
        .map(str::to_string)
        .collect::<Vec<_>>();

    assert_eq!(got, expected);
}

// PICKED: Enum.count with predicate closure filters list correctly
#[test]
fn enum_count_predicate_branch_helpers_keep_value_ref_return_lane() {
    let src = r#"
fn main() do
  dbg(Enum.count([1, 2, 3, 4], fn (x) -> x > 2 end))
end
"#;
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());
    let mut t = crate::types::new();
    let graph = runtime_graph_observed(&mut t, src, &tel);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let compiled = compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    let got = observe(&compiled, entry).output;
    assert_eq!(got, vec!["2"]);
    assert_authoritative_planner_consistent(&cap);

    let branch_helper_contracts = cap
        .find(&["fz", "codegen", "abi_contract"])
        .into_iter()
        .filter_map(|event| {
            let fn_name = match event.metadata.get("fn_name") {
                Some(Value::Str(name)) if *name == "if_then" || *name == "if_else" => name.to_string(),
                _ => return None,
            };
            let param_reprs = match event.metadata.get("param_reprs") {
                Some(Value::StrSeq(reprs)) => reprs,
                other => panic!("abi_contract missing branch helper param_reprs: {other:?}"),
            };
            if param_reprs.len() != 1 || param_reprs[0] != "RawInt" {
                return None;
            }
            let return_repr = match event.metadata.get("return_repr") {
                Some(Value::Str(repr)) => repr.to_string(),
                other => panic!("abi_contract missing branch helper return_repr: {other:?}"),
            };
            Some((fn_name, return_repr))
        })
        .collect::<Vec<_>>();
    assert!(
        !branch_helper_contracts.is_empty(),
        "test premise: Enum.count predicate wrapper should lower RawInt branch helpers"
    );
    assert!(
        branch_helper_contracts
            .iter()
            .all(|(_, return_repr)| return_repr == "ValueRef"),
        "branch helpers tail-called by a ValueRef closure wrapper must keep tagged returns: {branch_helper_contracts:?}"
    );
}

// DROP: old-world callable-entry selection telemetry, planner internals
#[test]
fn enum_find_closure_allocation_selects_site_specific_callable_entry() {
    let src = include_str!("../../fixtures/enum_predicate_search/input.fz");
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "callable_entry_selected"], cap.handler());

    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    #[derive(Debug)]
    struct CallableEntrySelection {
        body_name: String,
        closure_fn_name: String,
        selection_kind: String,
        capture_count: u64,
        callable_entry_spec_id: u64,
        callable_entry_spec_key: String,
    }

    let selections = cap
        .find(&["fz", "codegen", "callable_entry_selected"])
        .into_iter()
        .map(|event| {
            let body_name = match event.metadata.get("body_name") {
                Some(Value::Str(name)) => name.to_string(),
                other => panic!("callable_entry_selected missing body_name: {other:?}"),
            };
            let closure_fn_name = match event.metadata.get("closure_fn_name") {
                Some(Value::Str(name)) => name.to_string(),
                other => panic!("callable_entry_selected missing closure_fn_name: {other:?}"),
            };
            let selection_kind = match event.metadata.get("selection_kind") {
                Some(Value::Str(kind)) => kind.to_string(),
                other => panic!("callable_entry_selected missing selection_kind: {other:?}"),
            };
            let capture_count = match event.measurements.get("capture_count") {
                Some(Value::U64(count)) => *count,
                other => panic!("callable_entry_selected missing capture_count: {other:?}"),
            };
            let callable_entry_spec_id = match event.measurements.get("callable_entry_spec_id") {
                Some(Value::U64(spec_id)) => *spec_id,
                other => panic!("callable_entry_selected missing callable_entry_spec_id: {other:?}"),
            };
            let callable_entry_spec_key = match event.metadata.get("callable_entry_spec_key") {
                Some(Value::Str(key)) => key.to_string(),
                other => panic!("callable_entry_selected missing callable_entry_spec_key: {other:?}"),
            };
            CallableEntrySelection {
                body_name,
                closure_fn_name,
                selection_kind,
                capture_count,
                callable_entry_spec_id,
                callable_entry_spec_key,
            }
        })
        .collect::<Vec<_>>();

    let enum_find_wrappers = selections
        .iter()
        .filter(|selection| {
            selection.body_name.starts_with("Enum.find_s")
                && selection.closure_fn_name.starts_with("lambda_")
                && selection.selection_kind == "make_closure"
                && selection.capture_count == 2
        })
        .collect::<Vec<_>>();

    assert!(
        enum_find_wrappers
            .iter()
            .any(|selection| selection.callable_entry_spec_key.contains("nil")),
        "Enum.find/2 should allocate the nil-default wrapper against the nil-specialized callable body: {enum_find_wrappers:?}"
    );
    assert!(
        enum_find_wrappers
            .iter()
            .any(|selection| selection.callable_entry_spec_key.contains(":none")),
        "Enum.find/3 should keep the :none wrapper on its own callable body: {enum_find_wrappers:?}"
    );

    let wrapper_spec_ids = enum_find_wrappers
        .iter()
        .map(|selection| selection.callable_entry_spec_id)
        .collect::<BTreeSet<_>>();
    assert!(
        wrapper_spec_ids.len() >= 2,
        "default-specific Enum.find wrappers must not collapse to one callable entry: {enum_find_wrappers:?}"
    );
}

// PICKED: Enum.find and Enum.find_value with closures return correct results
#[test]
fn enum_find_then_find_value_preserves_reduce_continuation_protocol_native() {
    let src = r#"
fn main() do
  xs = [1, 2, 3, 4]
  dbg(Enum.find(xs, fn (x) -> x > 2 end))
  dbg(Enum.find_value(xs, fn (x) -> if (x % 2) == 0, do: {:even, x}, else: false end))
end
"#;
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "abi_contract"], cap.handler());
    let compiled = compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    let got = observe(&compiled, entry).output;
    assert_eq!(got, vec!["3", "{:even, 2}"]);

    let reduce_step_specs = cap
        .find(&["fz", "codegen", "abi_contract"])
        .into_iter()
        .filter_map(|event| {
            let fn_name = match event.metadata.get("fn_name") {
                Some(Value::Str(name)) => name,
                _ => return None,
            };
            if fn_name != "List.reduce_step" {
                return None;
            }
            match event.metadata.get("spec_key") {
                Some(Value::Str(key)) => Some(key.to_string()),
                other => panic!("abi_contract missing List.reduce_step spec_key: {other:?}"),
            }
        })
        .collect::<Vec<_>>();
    assert!(
        !reduce_step_specs.is_empty(),
        "test premise: Enum.find/Enum.find_value should compile List.reduce_step contracts"
    );
    assert!(
        reduce_step_specs.iter().all(|spec| spec.contains(":cont | :halt")),
        "List.reduce_step must keep the reducer protocol wrapper in its selected continuation ABI: {reduce_step_specs:?}"
    );
}

// PICKED: Enum.find_index with predicate closure returns correct index or nil
#[test]
fn enum_find_index_tail_clause_boxes_int_for_value_return_lane() {
    let src = r#"
fn main() do
  xs = [1, 2, 3, 4]
  dbg(Enum.find_index(xs, fn (x) -> (x % 2) == 0 end))
  dbg(Enum.find_index(xs, fn (x) -> x > 9 end))
end
"#;
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "abi_contract"], cap.handler());
    let compiled = compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    let got = observe(&compiled, entry).output;
    assert_eq!(got, vec!["1", "nil"]);

    let int_clause_contracts = cap
        .find(&["fz", "codegen", "abi_contract"])
        .into_iter()
        .filter_map(|event| {
            let fn_name = match event.metadata.get("fn_name") {
                Some(Value::Str(name)) => name,
                _ => return None,
            };
            if fn_name != "fn_clause_0" {
                return None;
            }
            let param_reprs = match event.metadata.get("param_reprs") {
                Some(Value::StrSeq(reprs)) => reprs,
                other => panic!("abi_contract missing fn_clause_0 param_reprs: {other:?}"),
            };
            if param_reprs.len() != 1 || param_reprs[0] != "RawInt" {
                return None;
            }
            match event.metadata.get("return_repr") {
                Some(Value::Str(repr)) => Some(repr.to_string()),
                other => panic!("abi_contract missing fn_clause_0 return_repr: {other:?}"),
            }
        })
        .collect::<Vec<_>>();
    assert!(
        int_clause_contracts.iter().all(|repr| repr == "ValueRef"),
        "reachable int matcher clauses tail-called by a ValueRef-returning finish function must box their return lane: {int_clause_contracts:?}"
    );
}

// PICKED: opaque reducer closure call chains with indirect continuation
#[test]
fn opaque_reducer_join_uses_lazy_continuation_for_indirect_closure_call() {
    let src = include_str!("../../fixtures/opaque_fn_value_join/input.fz");
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "closure_call_lowered"], cap.handler());
    let compiled = compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    let got = observe(&compiled, entry).output;
    assert_eq!(got, vec!["6"]);

    let closure_calls = cap
        .find(&["fz", "codegen", "closure_call_lowered"])
        .into_iter()
        .map(|event| {
            let body_name = match event.metadata.get("body_name") {
                Some(Value::Str(name)) => name,
                other => panic!("closure_call_lowered missing body_name: {other:?}"),
            };
            let dispatch_kind = match event.metadata.get("dispatch_kind") {
                Some(Value::Str(kind)) => kind.to_string(),
                other => panic!("closure_call_lowered missing dispatch_kind: {other:?}"),
            };
            let continuation_storage = match event.metadata.get("continuation_storage") {
                Some(Value::Str(storage)) => storage.to_string(),
                other => panic!("closure_call_lowered missing continuation_storage: {other:?}"),
            };
            (body_name.to_string(), dispatch_kind, continuation_storage)
        })
        .collect::<Vec<_>>();
    assert!(
        closure_calls.iter().any(|(_, dispatch_kind, continuation_storage)| {
            dispatch_kind == "indirect" && continuation_storage == "lazy_descriptor"
        }),
        "opaque reducer join should keep an indirect reducer continuation as a lazy descriptor: {closure_calls:?}"
    );
}

// PICKED: Enumerable.reduce returns :done and :halted protocol results correctly
#[test]
fn runtime_enumerable_list_reduce_reports_low_level_done_and_halt() {
    let src = r#"
fn main() do
  dbg({
    Enumerable.reduce([1, 2], {:cont, 0}, fn (x, acc) -> {:cont, acc + x} end),
    Enumerable.reduce([1, 2], {:halt, 7}, fn (x, acc) -> {:cont, acc + x} end)
  })
end
"#;
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let module = graph.module;
    let plan = graph.module_plan;
    let planned_program = materialize_program(&mut t, &module, &plan, &crate::telemetry::ConfiguredTelemetry::new());
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "closure_call_lowered"], cap.handler());
    tel.attach(&["fz", "codegen", "callable_entry_lowered"], cap.handler());
    let compiled = compile_planned(&mut t, &module, &plan, &tel).expect("compile planned");
    let expected_callable_targets = planned_program
        .callable_entries()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let actual_targets = compiled
        .static_closure_targets()
        .iter()
        .map(|(sid, _, _, _)| *sid)
        .collect::<BTreeSet<_>>();
    assert!(
        expected_callable_targets.is_subset(&actual_targets),
        "compiled static-closure singleton ids must include materialized zero-cap callable entries; expected={expected_callable_targets:?} actual={actual_targets:?}"
    );
    let reducer_callable_entry = *expected_callable_targets
        .iter()
        .next()
        .expect("Enumerable.reduce fixture should materialize one reducer callable entry");

    let closure_calls = cap
        .find(&["fz", "codegen", "closure_call_lowered"])
        .into_iter()
        .map(|ev| {
            let body_name = match ev.metadata.get("body_name") {
                Some(Value::Str(name)) => name.clone(),
                other => panic!("closure_call_lowered missing body_name: {other:?}"),
            };
            let call_kind = match ev.metadata.get("call_kind") {
                Some(Value::Str(kind)) => kind.clone(),
                other => panic!("closure_call_lowered missing call_kind: {other:?}"),
            };
            let dispatch_kind = match ev.metadata.get("dispatch_kind") {
                Some(Value::Str(kind)) => kind.clone(),
                other => panic!("closure_call_lowered missing dispatch_kind: {other:?}"),
            };
            let closure_binding_repr = match ev.metadata.get("closure_binding_repr") {
                Some(Value::Str(repr)) => repr.clone(),
                other => panic!("closure_call_lowered missing closure_binding_repr: {other:?}"),
            };
            (body_name, call_kind, dispatch_kind, closure_binding_repr)
        })
        .collect::<Vec<_>>();
    assert!(
        closure_calls
            .iter()
            .any(|(_, call_kind, dispatch_kind, closure_binding_repr)| {
                call_kind == "call_closure" && dispatch_kind == "direct" && closure_binding_repr == "ValueRef"
            }),
        "known Enumerable.reduce reducer should lower as a direct closure call while retaining tagged closure binding: {closure_calls:?}"
    );
    let callable_entries = cap
        .find(&["fz", "codegen", "callable_entry_lowered"])
        .into_iter()
        .map(|ev| {
            let spec_id = match ev.measurements.get("spec_id") {
                Some(Value::U64(id)) => *id as u32,
                other => panic!("callable_entry_lowered missing spec_id: {other:?}"),
            };
            let arg_count = match ev.measurements.get("arg_count") {
                Some(Value::U64(count)) => *count as u32,
                other => panic!("callable_entry_lowered missing arg_count: {other:?}"),
            };
            let capture_count = match ev.measurements.get("capture_count") {
                Some(Value::U64(count)) => *count as u32,
                other => panic!("callable_entry_lowered missing capture_count: {other:?}"),
            };
            (spec_id, arg_count, capture_count)
        })
        .collect::<Vec<_>>();
    assert!(
        callable_entries.iter().any(|(spec_id, arg_count, capture_count)| {
            *spec_id == reducer_callable_entry && *arg_count == 2 && *capture_count == 0
        }),
        "compile should materialize a zero-cap callable entry for the reducer body: {callable_entries:?}"
    );

    let got = capture_main_module_planned(&mut t, module, plan);
    assert_eq!(got, vec!["{{:done, 3}, {:halted, 7}}"]);
}

// PICKED: Enum.reduce_while with shape-changing accumulator halts at correct element
#[test]
fn runtime_enum_reduce_while_shape_changing_accumulator_runs_native() {
    let src = r#"
fn finish({:found, index}), do: index
fn finish({:not_found, _index}), do: -1

fn collapsed() do
  Enum.reduce_while([1, 2, 3], {:not_found, 0}, fn (entry, {:not_found, index}) ->
    if entry == 2 do
      {:halt, {:found, index}}
    else
      {:cont, {:not_found, index + 1}}
    end
  end)
end

fn main() do
  dbg(finish(collapsed()))
end
"#;
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let module = graph.module;

    let collapsed = module.fn_by_name("collapsed").expect("collapsed");
    let plan = graph.module_plan;
    let ret = plan
        .effective_returns
        .get(&SpecKey::value(collapsed.id, Vec::new()).body_key())
        .unwrap_or_else(|| panic!("missing collapsed return"));
    let found = t.atom_lit("found");
    let int = t.int();
    let found_int = t.tuple(&[found, int]);
    assert!(
        t.is_subtype(&found_int, ret),
        "reduce_while declared return must include halt payload, got {}",
        t.display(ret)
    );

    assert_eq!(
        capture_main_module_planned(&mut t, module, plan),
        vec!["1"],
        "native result"
    );
}

// PICKED: Enum.find early halt with default value returns first matching element
#[test]
fn runtime_enum_find_early_halt_keeps_value_delivery_boxed() {
    let got = capture_main_with_runtime_graph(
        r#"
fn main() do
  dbg(Enum.find([1, 2], :none, fn (x) -> if x == 1, do: true, else: panic("late find") end))
end
"#,
    );

    assert_eq!(got, vec!["1"]);
}

// PICKED: Enum.sort with default and custom comparator preserves stable order
#[test]
fn runtime_enum_sort_uses_stable_merge_sort_for_lists() {
    let got = capture_main_with_runtime_graph(
        r#"
fn descending(left, right), do: left >= right
fn by_key(left, right) do
  {left_key, _left_tag} = left
  {right_key, _right_tag} = right
  left_key <= right_key
end

fn main() do
  dbg(Enum.sort([3, 1, 2, 1, 5, 4]))
  dbg(Enum.sort([3, 1, 2, 1, 5, 4], descending))
  dbg(Enum.sort([{2, :a}, {1, :a}, {2, :b}, {1, :b}], by_key))
end
"#,
    );

    assert_eq!(
        got,
        vec![
            "[1, 1, 2, 3, 4, 5]",
            "[5, 4, 3, 2, 1, 1]",
            "[{1, :a}, {1, :b}, {2, :a}, {2, :b}]"
        ]
    );
}

#[test]
#[ignore = "broken in the old pipeline since before fz-rh2.18.5; the old world dies with fz-rh2.16.6 — do not fix"]
fn image_linker_rejects_missing_and_duplicate_providers() {
    let missing = Mfa::new(ModuleName::from_segments(vec!["Missing".to_string()]), "f", 0);
    let (user, _) = link_test_unit("User", &[("run", 0)], vec![missing.clone()]);
    let err = match link_ir_units(&[user]) {
        Ok(_) => panic!("expected missing import"),
        Err(err) => err,
    };
    assert_eq!(
        err,
        ImageLinkError::MissingImport {
            requester: Some(ModuleName::from_segments(vec!["User".to_string()])),
            import: missing,
        }
    );

    let (a, _) = link_test_unit("A", &[("f", 0)], Vec::new());
    let (dup, _) = link_test_unit("A", &[("f", 0)], Vec::new());
    let err = match link_ir_units(&[a, dup]) {
        Ok(_) => panic!("expected duplicate provider"),
        Err(err) => err,
    };
    assert!(matches!(err, ImageLinkError::DuplicateProvider { .. }));
}

#[test]
fn image_linker_rejects_unresolved_external_imports_without_provider() {
    let target = Mfa::new(ModuleName::from_segments(vec!["Provider".to_string()]), "run", 0);
    let mut unit_code = Module::new();
    let mut builder = FnBuilder::new(FnId(0), "User.run").with_owner_module("User");
    let entry = builder.block(Vec::new());
    builder.set_terminator(
        entry,
        Term::TailCall {
            ident: CallsiteIdent::synthetic(),
            callee: DirectCallTarget::ProviderBoundary(target),
            args: Vec::new(),
            is_back_edge: false,
        },
    );
    unit_code.fn_idx.insert(FnId(0), unit_code.fns.len());
    unit_code.fns.push(builder.build());
    let interface = ModuleInterface {
        name: ModuleName::from_segments(vec!["User".to_string()]),
        imports: Vec::new(),
        exports: Vec::new(),
        types: Vec::new(),
        protocols: Vec::new(),
        protocol_impls: Vec::new(),
        docs: None,
        fingerprint_inputs: Vec::new(),
    };
    let unit = CompiledUnit::from_ir_module(unit_code.clone(), Some(interface), Diagnostics::new());
    let err = match link_ir_units(&[unit]) {
        Ok(_) => panic!("expected unresolved external calls"),
        Err(err) => err,
    };
    assert_eq!(
        err,
        ImageLinkError::MissingImport {
            requester: Some(ModuleName::from_segments(vec!["User".to_string()])),
            import: Mfa::new(ModuleName::from_segments(vec!["Provider".to_string()]), "run", 0,),
        }
    );
}

// DROP: AOT object-file compilation, no compiler2 AOT path yet
#[test]
fn aot_compile_produces_object_with_main_symbol() {
    let src = "fn add1(n) do n + 1 end\nfn main() do dbg(add1(41)) end";
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let artifact = compile_aot_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        "add1_smoke",
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile_aot planned");
    assert!(!artifact.object.is_empty(), "AOT object should be non-empty");
    // compile_aot emits a C-callable `main` symbol that wraps
    // fz_aot_run_main; the artifact surfaces it for the linker.
    let main_sym = artifact.main_symbol.expect("main_symbol set");
    assert_eq!(main_sym, "main", "expected C-callable main symbol");
    // Host-target object-file magic: ELF starts 0x7f 'E' 'L' 'F';
    // Mach-O starts 0xfeedface/0xfeedfacf (or byte-swapped 64-bit).
    let magic_ok = matches!(
        &artifact.object[..4],
        [0x7f, b'E', b'L', b'F']
            | [0xce, 0xfa, 0xed, 0xfe]
            | [0xcf, 0xfa, 0xed, 0xfe]
            | [0xfe, 0xed, 0xfa, 0xce]
            | [0xfe, 0xed, 0xfa, 0xcf]
    );
    assert!(magic_ok, "unexpected object magic: {:02x?}", &artifact.object[..4]);
}

/// A run observed entirely through telemetry: the process_exited `ExitRecord`
/// plus the `dbg` output line stream. The one seam the result/output/heap test
/// helpers are built on — no helper reads `task.halt_value` or `TEST_CAPTURE`.
struct Observation {
    exit: ExitRecord,
    output: Vec<String>,
}

fn observe(compiled: &CompiledModule, entry: FnId) -> Observation {
    let tel = ConfiguredTelemetry::new();
    let exits = ProcessExitCapture::new();
    let out = DbgCapture::new();
    tel.attach(&[], exits.handler());
    tel.attach(&[], out.handler());
    let mut rt = Runtime::new(compiled, 1, &tel);
    let root_pid = rt.spawn(entry);
    rt.run_until_idle();

    Observation {
        exit: exits.by_pid(root_pid).expect("root process_exited captured"),
        output: out.lines(),
    }
}

fn run_main(src: &str) -> i64 {
    run_runtime_graph_main_planned(src)
}

fn run_main_returning_module(src: &str) -> (i64, Module) {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    let r = compiled.run(&ConfiguredTelemetry::new(), entry);
    (r, graph.module)
}

fn capture_main(src: &str) -> Vec<String> {
    capture_main_with_runtime_graph(src)
}

fn capture_main_with_runtime_graph(src: &str) -> Vec<String> {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    assert_direct_call_arities(&graph.module);
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    observe(&compiled, entry).output
}

fn runtime_graph(t: &mut DefaultTypes, src: &str) -> PreparedExecutionGraph {
    runtime_graph_observed(t, src, &crate::telemetry::ConfiguredTelemetry::new())
}

fn runtime_graph_observed(t: &mut DefaultTypes, src: &str, tel: &dyn Telemetry) -> PreparedExecutionGraph {
    let frontend = compile_source_with_types(t, src.to_string(), "test.fz".to_string(), tel);
    let checked = checked_module_for_mode(t, frontend, tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    prepare_execution_graph(t, checked, tel, CompileMode::Normal).unwrap_or_else(|err| panic!("execution graph: {err}"))
}

fn capture_main_module_planned(t: &mut DefaultTypes, m: Module, plan: ModulePlan) -> Vec<String> {
    let entry = m.fn_by_name("main").unwrap().id;
    assert_direct_call_arities(&m);
    let compiled =
        compile_planned(t, &m, &plan, &crate::telemetry::ConfiguredTelemetry::new()).expect("compile planned");
    observe(&compiled, entry).output
}

fn run_runtime_graph_main_planned(src: &str) -> i64 {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    observe(&compiled, entry).exit.halt_value
}

fn assert_direct_call_arities(m: &Module) {
    for f in &m.fns {
        for block in &f.blocks {
            match &block.terminator {
                Term::Call { callee, args, .. } | Term::TailCall { callee, args, .. } => {
                    let (target_name, target_id, params) = match callee {
                        DirectCallTarget::Local(callee) => {
                            let target = m.fn_by_id(*callee);
                            (
                                target.name.clone(),
                                format!("{:?}", target.id),
                                target.block(target.entry).params.len(),
                            )
                        }
                        DirectCallTarget::ProviderBoundary(target) => {
                            (target.name.clone(), target.module.to_string(), target.arity)
                        }
                    };
                    assert_eq!(
                        params,
                        args.len(),
                        "{} calls {}#{:?} with {} args but target has {} params\ncaller:\n{}",
                        f.name,
                        target_name,
                        target_id,
                        args.len(),
                        params,
                        f
                    );
                }
                _ => {}
            }
        }
    }
}

/// (halt value, live heap-object count) observed via `observe`. The seam tests
/// use to check a run's result and heap without poking a Process.
fn run_capturing(compiled: &CompiledModule, entry: FnId) -> (i64, usize) {
    let o = observe(compiled, entry);
    (o.exit.halt_value, o.exit.live_count)
}

fn count_live_objects(src: &str) -> usize {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    run_capturing(&compiled, entry).1
}

/// Live heap objects the program *body* allocates. Every spawned main carries
/// fixed launch scaffolding (the entry thunk + synthetic main inner closure
/// the scheduler resumes through `fz_resume`); a no-allocation main isolates
/// that baseline so callers can assert on the objects their source builds.
fn run_main_and_count_live(src: &str) -> usize {
    let scaffolding = count_live_objects("fn main(), do: 0");
    count_live_objects(src) - scaffolding
}

/// Two Processes built from the same CompiledModule observe equal atom
/// ids for the same atom literal: atoms are u32s baked into compiled
/// code, identical regardless of which Process runs it.
// PICKED: atom identity is stable across multiple executions of same program
#[test]
fn atom_identity_preserved_across_processes_from_same_module() {
    // `:ok` halts as the atom's raw u32 id; both Processes must agree
    // because the id was assigned once at compile time.
    let src = "fn main(), do: :ok";
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    let entry = graph.module.fn_by_name("main").unwrap().id;

    let (ra, _) = run_capturing(&compiled, entry);
    let (rb, _) = run_capturing(&compiled, entry);
    assert_eq!(ra, rb, "atom id stable across processes from the same module");
}

/// `nil`, `true`, and `false` are reserved at atom IDs 0/1/2 in every
/// module so downstream codegen / runtime can rely on them. Pin halt
/// values to the named constants to catch any re-shuffling of intern order.
// PICKED: nil, true, false reserved atom IDs are stable and correct
#[test]
fn reserved_atom_ids_are_stable() {
    assert_eq!(NIL_ATOM_ID, 0);
    assert_eq!(TRUE_ATOM_ID, 1);
    assert_eq!(FALSE_ATOM_ID, 2);
    assert_eq!(run_main("fn main(), do: nil"), NIL_ATOM_ID as i64);
    assert_eq!(run_main("fn main(), do: true"), TRUE_ATOM_ID as i64);
    assert_eq!(run_main("fn main(), do: false"), FALSE_ATOM_ID as i64);
}

// PICKED: spawn with captured variables executes and completes correctly
#[test]
fn runtime_graph_spawn_with_captures_runs_via_planned_codegen_path() {
    assert_eq!(
        run_runtime_graph_main_planned(include_str!("../../fixtures/spawn_with_captures/input.fz")),
        NIL_ATOM_ID as i64
    );
}

// PICKED: plain spawn of zero-arity function executes child process
#[test]
fn runtime_graph_plain_spawn_runs_via_planned_codegen_path() {
    assert_eq!(
        run_runtime_graph_main_planned("fn child(), do: nil\nfn main() do spawn(child) end"),
        2
    );
}

// PICKED: spawn + send + selective receive delivers message to waiting process
#[test]
fn planned_codegen_runs_runtime_graph_selective_receive() {
    let src = "fn child(), do: send(1, 42)\n\
               fn main() do\n\
                 spawn(child)\n\
                 dbg(receive do x -> x end)\n\
               end";
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").expect("main fn").id;
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    assert_eq!(observe(&compiled, entry).exit.halt_value, 42);
}

// DROP: old-world materialization reachability for receive bodies, planner internals
#[test]
#[ignore = "broken in the old pipeline since before fz-rh2.18.5; the old world dies with fz-rh2.16.6 — do not fix"]
fn materialization_keeps_selective_receive_outcome_bodies_reachable() {
    let src = "fn child(), do: send(1, 42)\n\
               fn main() do\n\
                 spawn(child)\n\
                 dbg(receive do x -> x end)\n\
               end";
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let reachable = module_reachable_materialized_body_signals(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &ConfiguredTelemetry::new(),
    );

    assert!(
        reachable.iter().any(|body| body.fn_name == "rx_clause_0_body"),
        "authoritative materialization must keep selective-receive outcome bodies reachable: {reachable:?}"
    );
    assert!(
        reachable.iter().any(|body| body.fn_name == "k_185"),
        "authoritative materialization must keep the receive continuation reachable: {reachable:?}"
    );
}

// PICKED: plain spawn executes child process via interpreter path
#[test]
fn runtime_graph_plain_spawn_runs_via_planned_interp_path() {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, "fn child(), do: nil\nfn main() do spawn(child) end");
    let (halt, _) = run_main_with_plan(
        &mut t,
        &crate::telemetry::ConfiguredTelemetry::new(),
        &graph.module,
        graph.module_plan,
    )
    .expect("interp run");
    assert_eq!(halt, 2);
}

// DROP: old-world materialized body signals telemetry, planner internals
#[test]
fn codegen_materializes_plain_spawn_child_callable_boundary_target() {
    let signals = runtime_graph_codegen_materialized_body_signals(
        include_str!("../type_infer/fixtures/spawn_plain.fz"),
        &ConfiguredTelemetry::new(),
    );

    let child = signals
        .iter()
        .find(|signal| signal.fn_name == "child")
        .unwrap_or_else(|| panic!("expected child materialized body event: {signals:?}"));

    assert_eq!(child.role, "authoritative");
    assert!(
        child.spec_key.contains("FnId"),
        "materialized body event should carry the child spec key: {child:?}"
    );
}

// PICKED: spawn child, send message, receive in main returns sent value
#[test]
fn runtime_graph_spawn_then_receive_runs_via_planned_codegen_path() {
    assert_eq!(
        run_runtime_graph_main_planned(
            "fn child(), do: send(1, 42)\nfn main() do spawn(child)\nreceive do x -> x end\nend"
        ),
        42
    );
}

// DROP: old-world MakeFnRef IR node and planner zero-cap callable registration
#[test]
fn runtime_graph_plain_spawn_make_fn_ref_registers_zero_cap_target() {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, "fn child(), do: nil\nfn main() do spawn(child) end");
    let module = graph.module;
    let child = module.fn_by_name("child").expect("child fn");
    let child_fn_refs = module
        .fns
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|block| block.stmts.iter())
        .filter(|stmt| {
            matches!(
                stmt,
                Stmt::Let(_, Prim::MakeFnRef(_, fn_id)) if *fn_id == child.id
            )
        })
        .count();
    let child_make_closures = module
        .fns
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|block| block.stmts.iter())
        .filter(|stmt| {
            matches!(
                stmt,
                Stmt::Let(_, Prim::MakeClosure(_, fn_id, captured))
                    if *fn_id == child.id && captured.is_empty()
            )
        })
        .count();
    assert!(
        child_fn_refs > 0,
        "runtime graph plain spawn should carry child/0 as a thin fn ref; child_fn_refs={child_fn_refs}"
    );
    assert_eq!(
        child_make_closures, 0,
        "runtime graph plain spawn should not recover child/0 as MakeClosure([], ...)"
    );
    let plan = graph.module_plan;
    let child_specs: Vec<_> = plan.specs.keys().filter(|key| key.fn_id == child.id).cloned().collect();

    let child_target = plan
        .specs
        .keys()
        .find(|key| key.fn_id == child.id && key.input.is_empty() && key.demand.is_value())
        .cloned()
        .unwrap_or_else(|| {
            panic!(
                "planned runtime graph should register a value spec for child/0; child_make_closures={child_make_closures}; child_specs={child_specs:?}"
            )
        });

    let planned_program = materialize_program(&mut t, &module, &plan, &crate::telemetry::ConfiguredTelemetry::new());
    let child_sid = planned_program
        .spec_registry()
        .resolve_spec_key(&t, &child_target)
        .expect("callable-boundary target spec must be registered")
        .0;

    assert_eq!(
        planned_program
            .callable_entries()
            .get(&child_sid)
            .map(|entry| entry.capture_count),
        Some(0),
        "authoritative planned program must register child/0 as a zero-cap callable target when the prepared runtime graph carries MakeFnRef(child); child_fn_refs={child_fn_refs}; child_make_closures={child_make_closures}"
    );
}

// DROP: old-world resume_addr/static_closure_targets JIT finalization internals
#[test]
fn runtime_graph_plain_spawn_finalizes_resume_addr() {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, "fn child(), do: nil\nfn main() do spawn(child) end");
    let module = graph.module;
    let child_id = module.fn_by_name("child").expect("child fn").id.0;
    let plan = graph.module_plan;
    let compiled = compile_planned(&mut t, &module, &plan, &crate::telemetry::ConfiguredTelemetry::new())
        .expect("compile planned");
    assert!(
        !compiled.resume_addr.is_null(),
        "runtime graph plain spawn should finalize fz_resume"
    );
    assert!(
        compiled
            .static_closure_targets()
            .iter()
            .any(|(_, fn_id, _, _)| *fn_id == child_id),
        "runtime graph plain spawn should register child/0 as a static closure target: {:?}",
        compiled.static_closure_targets()
    );
    assert!(
        compiled
            .static_closure_targets()
            .iter()
            .all(|(_, _, ptr, _)| !ptr.is_null()),
        "runtime graph plain spawn should finalize non-null static closure targets: {:?}",
        compiled.static_closure_targets()
    );
}

// DROP: old-world materialized IR var type check for closure operands, planner internals
#[test]
fn materialized_enum_take_closure_operands_stay_value_ref_typed() {
    let mut t = crate::types::new();
    let src = "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n";
    let graph = runtime_graph(&mut t, src);
    let module = graph.module;
    let plan = graph.module_plan;
    let planned_program = materialize_program(&mut t, &module, &plan, &crate::telemetry::ConfiguredTelemetry::new());

    let mut checked = 0usize;
    for sid in planned_program.reachable_specs() {
        let body = &planned_program.executable_body(SpecId(*sid)).body;
        let spec_key = &planned_program.spec_keys()[*sid as usize];
        let spec_plan = plan
            .specs
            .get(spec_key)
            .unwrap_or_else(|| panic!("missing spec plan for reachable spec_key={spec_key:?}"));
        for block in &body.blocks {
            let closure = match &block.terminator {
                Term::CallClosure { closure, .. } | Term::TailCallClosure { closure, .. } => *closure,
                _ => continue,
            };
            let closure_ty = spec_plan.vars.get(&closure).unwrap_or_else(|| {
                panic!(
                    "missing closure var type for sid={sid} closure={closure:?} body={}",
                    body.name
                )
            });
            checked += 1;
            assert_eq!(
                ArgRepr::from_ty(&mut t, closure_ty),
                ArgRepr::ValueRef,
                "closure operand must stay ValueRef-typed for codegen; sid={sid}; spec_key={spec_key:?}; fn_name={}; closure={closure:?}; closure_ty={}",
                body.name,
                t.display(closure_ty)
            );
        }
    }

    assert!(
        checked > 0,
        "expected minimal Enum.take runtime graph to retain at least one indirect closure call"
    );
}

// DROP: old-world codegen telemetry for closure binding repr, no compiler2 analogue
#[test]
fn codegen_lowering_keeps_enum_take_closure_bindings_on_value_ref_lane() {
    let src = "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n";
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "closure_call_lowered"], cap.handler());

    let mut t = crate::types::new();
    let graph = runtime_graph_observed(&mut t, src, &tel);
    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    let events = cap.find(&["fz", "codegen", "closure_call_lowered"]);
    assert!(
        !events.is_empty(),
        "expected minimal Enum.take codegen to lower at least one closure call"
    );
    for event in events {
        let repr = match event.metadata.get("closure_binding_repr") {
            Some(Value::Str(repr)) => repr,
            other => panic!("closure_binding_repr missing or wrong type: {other:?}"),
        };
        assert_eq!(
            repr, "ValueRef",
            "closure-call lowering must keep closure bindings on the ValueRef lane: {:?}",
            event.metadata
        );
    }
}

// DROP: old-world SpecKey arity invariant on planned body, planner internals
#[test]
fn planned_enum_take_indirect_closure_body_preserves_spec_key_arity() {
    let mut t = crate::types::new();
    let src = "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n";
    let graph = runtime_graph(&mut t, src);
    let planned_program = materialize_program(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    );

    let mut checked = 0usize;
    for sid in planned_program.reachable_specs() {
        let planned = planned_program.executable_body(SpecId(*sid));
        let has_indirect_closure = planned.body.blocks.iter().any(|block| {
            matches!(
                block.terminator,
                Term::CallClosure { .. } | Term::TailCallClosure { .. }
            )
        });
        if !has_indirect_closure {
            continue;
        }
        checked += 1;
        assert_eq!(
            planned.body.block(planned.body.entry).params.len(),
            planned.spec_key.input.len(),
            "indirect-closure planned body must preserve spec-key arity; sid={sid}; fn_name={}; spec_key={:?}",
            planned.body.name,
            planned.spec_key
        );
    }

    assert!(
        checked > 0,
        "expected at least one indirect closure body in minimal Enum.take"
    );
}

/// Two Processes built from the same CompiledModule run independent
/// programs that each construct a map; each Process owns its own
/// builder fields so the runs cannot leak state into each other.
// PICKED: map construction is isolated between independent process runs
#[test]
fn two_processes_run_independent_map_builds() {
    // Distinct keys + values so any state leak surfaces as a wrong halt.
    let src_a = "fn main(), do: %{1 => 10, 2 => 20}[1]";
    let src_b = "fn main(), do: %{3 => 30, 4 => 40}[3]";

    let mut ta = crate::types::new();
    let graph_a = runtime_graph(&mut ta, src_a);
    let ca = compile_planned(
        &mut ta,
        &graph_a.module,
        &graph_a.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    let entry_a = graph_a.module.fn_by_name("main").unwrap().id;
    let mut tb = crate::types::new();
    let graph_b = runtime_graph(&mut tb, src_b);
    let cb = compile_planned(
        &mut tb,
        &graph_b.module,
        &graph_b.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    let entry_b = graph_b.module.fn_by_name("main").unwrap().id;

    // Independent runs: each spawns its own task with its own heap, so any
    // cross-talk would surface as a wrong halt. Running program A twice
    // proves a second run is unaffected by the first.
    let (ra, la) = run_capturing(&ca, entry_a);
    let (rb, lb) = run_capturing(&cb, entry_b);
    let (ra2, _) = run_capturing(&ca, entry_a);

    assert_eq!(ra, 10, "program a's first run returns map[1] = 10");
    assert_eq!(rb, 30, "program b's run returns map[3] = 30");
    assert_eq!(ra2, 10, "program a's second run returns 10 (independent)");

    assert!(la > 0, "program a leaves live heap allocs");
    assert!(lb > 0, "program b leaves live heap allocs");
}

// PICKED: integer literal evaluates and returns correct value
#[test]
fn const_int_runs_and_halts_with_value() {
    assert_eq!(run_main("fn main() do 42 end"), 42);
}

// PICKED: integer addition computes correct result
#[test]
fn binop_int_addition_runs() {
    assert_eq!(run_main("fn main(), do: 40 + 2"), 42);
}

// PICKED: chained arithmetic operators evaluate in correct order
#[test]
fn binop_chain_runs() {
    assert_eq!(run_main("fn main(), do: (1 + 2) * 7"), 21);
}

// PICKED: if/else conditional takes true branch on satisfied condition
#[test]
fn if_then_else_runs() {
    assert_eq!(run_main("fn main(), do: if 1 < 2, do: 100, else: 200"), 100);
}

// PICKED: dbg/1 prints expression value to output
#[test]
fn print_builtin_routes_through_runtime() {
    assert_eq!(capture_main("fn main(), do: dbg(40 + 2)"), vec!["42"]);
}

// PICKED: Process.heap_alloc_stats intrinsic returns map with allocation counts
#[test]
fn process_heap_alloc_stats_is_callable_from_fz() {
    let lines = capture_main_with_runtime_graph(
        "fn main() do\n  xs = [1, 2]\n  dbg(xs)\n  stats = Process.heap_alloc_stats()\n  dbg(stats[:list_cons_allocs])\n  dbg(stats[:map_allocs])\nend",
    );
    assert_eq!(lines, vec!["[1, 2]", "2", "0"]);
}

// PICKED: assert and refute builtins distinguish integer payload from bool kind
#[test]
fn assert_builtin_keeps_scalar_kind_separate_from_raw_payload() {
    assert_eq!(run_main("fn main(), do: assert(2)"), NIL_ATOM_ID as i64);
    assert_eq!(run_main("fn main(), do: refute(true == 1)"), NIL_ATOM_ID as i64);
}

// PICKED: unary negation of integer literal returns negative value
#[test]
fn unop_neg_runs() {
    assert_eq!(run_main("fn main(), do: -7"), -7);
}

// PICKED: atom literal returns its interned atom id
#[test]
fn atom_const_returns_atom_id() {
    let (atom_id, module) = run_main_returning_module("fn main(), do: :ok");
    assert_eq!(module.atom_names[atom_id as usize], "ok");
}

// PICKED: function call passes argument and returns computed result
#[test]
fn add1_via_call_returns_42() {
    assert_eq!(run_main("fn add1(n), do: n + 1\nfn main(), do: add1(41)"), 42);
}

// PICKED: non-tail call result used in enclosing arithmetic expression
#[test]
fn binop_with_inner_nontail_call() {
    assert_eq!(run_main("fn add1(n), do: n + 1\nfn main(), do: add1(40) + 2"), 43);
}

// PICKED: recursive function with base case and pattern matching computes factorial
#[test]
fn fact_5_smaller_repro() {
    assert_eq!(
        run_main(
            r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(5)
"#
        ),
        120
    );
}

// PICKED: deep recursive factorial executes without stack overflow
#[test]
fn fact_10_runs_via_recursion_and_continuation_chain() {
    assert_eq!(
        run_main(
            r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(10)
"#
        ),
        3628800
    );
}

// PICKED: tail-recursive loop over 100k iterations does not overflow stack
#[test]
fn count_100k_stays_bounded_via_tail_call_frame_reuse() {
    assert_eq!(
        run_main(
            r#"
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)
fn main(), do: count(100000, 0)
"#
        ),
        100_000
    );
}

#[test]
fn render_any_value_dispatches_per_tag() {
    assert_eq!(render_value(std::ptr::null_mut(), AnyValue::int(42)), "42");
    assert_eq!(render_value(std::ptr::null_mut(), AnyValue::int(0)), "0");
    assert_eq!(render_value(std::ptr::null_mut(), AnyValue::int(-7)), "-7");
    assert_eq!(render_value(std::ptr::null_mut(), AnyValue::nil_atom()), "nil");
    assert_eq!(render_value(std::ptr::null_mut(), AnyValue::bool_atom(true)), "true");
    assert_eq!(render_value(std::ptr::null_mut(), AnyValue::bool_atom(false)), "false");
    // Empty Process.atom_names: render falls back to `:atom_N`. The
    // source-name path is verified end-to-end by the fixture matrix.
    assert_eq!(render_value(std::ptr::null_mut(), AnyValue::atom(3)), ":atom_3");
}

// PICKED: atom, true, false literals render correctly via dbg
#[test]
fn print_captures_atom_and_specials() {
    assert_eq!(
        capture_main("fn main() do\n  dbg(:ok)\n  dbg(true)\n  dbg(false)\nend"),
        vec![":ok", "true", "false"]
    );
}

// PICKED: atom-keyed map literal renders with canonical key-value syntax
#[test]
fn print_atom_keyed_map_renders_canonically() {
    assert_eq!(
        capture_main("fn main(), do: dbg(%{a: 1, b: 2})"),
        vec!["%{:a => 1, :b => 2}"]
    );
}

// PICKED: map key access returns value for present keys
#[test]
fn map_get_returns_value_or_nil() {
    assert_eq!(run_main("fn main(), do: %{a: 10, b: 20}[:a] + %{a: 10, b: 20}[:b]"), 30);
}

// PICKED: map update syntax creates new map leaving original immutable
#[test]
fn map_update_returns_new_map_originals_unchanged() {
    assert_eq!(
        capture_main(
            r#"
fn main() do
  m = %{a: 1, b: 2}
  m2 = %{m | a: 99}
  dbg(m)
  dbg(m2)
end
"#
        ),
        vec!["%{:a => 1, :b => 2}", "%{:a => 99, :b => 2}",]
    );
}

// PICKED: bitstring literal renders correctly as byte sequence
#[test]
fn print_bitstring_literal_via_jit() {
    assert_eq!(capture_main("fn main(), do: dbg(<<0xff, 0xab>>)"), vec!["<<255, 171>>"]);
}

// PICKED: binary pattern match splits header byte from rest of bitstring
#[test]
fn match_simple_header_and_rest() {
    assert_eq!(
        capture_main(
            r#"
fn parse(<<n, rest::binary>>), do: {n, rest}
fn main(), do: dbg(parse(<<0xa5, 0x01, 0x02>>))
"#
        ),
        vec!["{165, <<1, 2>>}"]
    );
}

// PICKED: binary pattern with size variable extracts variable-length segment
#[test]
fn match_variable_size_payload_via_size_var() {
    assert_eq!(
        capture_main(
            r#"
fn parse(<<len, payload::binary-size(len), rest::binary>>) do
  {len, payload, rest}
end
fn main(), do: dbg(parse(<<3, 0x01, 0x02, 0x03, 0xff>>))
"#
        ),
        vec!["{3, <<1, 2, 3>>, <<255>>}"]
    );
}

// PICKED: two-element tuple literal renders correctly
#[test]
fn print_tuple_pair_renders() {
    assert_eq!(capture_main("fn main(), do: dbg({1, 2})"), vec!["{1, 2}"]);
}

// PICKED: tuple pattern match destructures elements by position
#[test]
fn fst_snd_destructure_tuple() {
    assert_eq!(
        run_main(
            r#"
fn fst({a, _}), do: a
fn snd({_, b}), do: b
fn main(), do: fst({10, 20}) + snd({30, 40})
"#
        ),
        50
    );
}

// PICKED: mixed-type tuple with int, atom, bool renders correctly
#[test]
fn print_mixed_type_tuple() {
    assert_eq!(
        capture_main("fn main(), do: dbg({1, :ok, true})"),
        vec!["{1, :ok, true}"]
    );
}

// DROP: old-world CLIF IR shape for static tuple lowering, no compiler2 analogue
#[test]
fn static_tuple_literal_uses_read_only_storage_without_boxing() {
    let ir = compile_and_grab_ir("fn main(), do: dbg({1, 2.5, :ok})", "main");
    let struct_ref_tag_mask = packed_ref_tag_mask(ValueKind::STRUCT);
    assert!(
        ir.contains("symbol_value") && ir.contains(&struct_ref_tag_mask),
        "fully static tuple literal should lower to a static struct ref:\n{}",
        ir
    );
    assert!(
        !ir.contains("@fz_alloc_struct") && !ir.contains("@fz_struct_set_field_"),
        "fully static tuple literal should not allocate or initialize heap storage:\n{}",
        ir
    );
    assert!(
        !ir.contains("@fz_box_int_for_any") && !ir.contains("@fz_box_float_for_any"),
        "static numeric tuple fields should not allocate boxes before initialization:\n{}",
        ir
    );
}

// DROP: old-world CLIF IR field setter names for tuple construction, no compiler2 analogue
#[test]
fn dynamic_tuple_literal_initializes_scalar_fields_without_boxing() {
    let ir = compiled_ir_body_containing(
        "fn id(x) do\n  dbg(x)\n  x\nend\nfn main(), do: dbg({1, id(2.5), :ok})",
        "@fz_struct_set_field_float",
    );
    assert!(
        ir.contains("@fz_struct_set_field_int"),
        "dynamic integer tuple field should use typed destination setter:\n{}",
        ir
    );
    assert!(
        ir.contains("@fz_struct_set_field_float"),
        "dynamic float tuple field should use typed destination setter:\n{}",
        ir
    );
    assert!(
        ir.contains("@fz_struct_set_field_atom"),
        "dynamic atom tuple field should use typed destination setter:\n{}",
        ir
    );
    assert!(
        !ir.contains("@fz_box_int_for_any") && !ir.contains("@fz_box_float_for_any"),
        "dynamic numeric tuple fields should not allocate boxes before initialization:\n{}",
        ir
    );
}

// DROP: old-world CLIF IR alias-mark instruction for ref field publication
#[test]
fn tuple_literal_marks_ref_fields_as_published() {
    let ir = compile_and_grab_ir("fn main(), do: {[1, 2]}", "main");
    assert!(
        ir.contains("@fz_mark_published_ref_aliased") && ir.contains("@fz_struct_set_field_ref"),
        "tuple ref fields should be alias-marked before publication:\n{}",
        ir
    );
}

// PICKED: list literal renders correctly as bracketed comma-separated values
#[test]
fn print_list_literal_renders_via_jit() {
    assert_eq!(capture_main("fn main(), do: dbg([1, 2, 3])"), vec!["[1, 2, 3]"]);
}

// PICKED: recursive list head/tail pattern match accumulates sum correctly
#[test]
fn sum_list_via_head_tail_recursion() {
    assert_eq!(
        run_main(
            r#"
fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)
fn main(), do: sum([1, 2, 3, 4, 5])
"#
        ),
        15
    );
}

// PICKED: double negation round-trips integer value correctly
#[test]
fn box_unbox_int_roundtrip_via_neg_neg() {
    for n in &[0i64, 1, -1, 42, -42, 1_000_000_000] {
        let src = format!("fn main(), do: -(-({}))", n);
        assert_eq!(run_main(&src), *n, "round-trip failed for {}", n);
    }
}

// PICKED: mutually recursive functions dispatch correctly across call boundaries
#[test]
fn mutual_recursion_even_odd_small_n() {
    assert_eq!(
        run_main(
            r#"
fn even(0), do: true
fn even(n), do: odd(n - 1)
fn odd(0), do: false
fn odd(n), do: even(n - 1)
fn main(), do: even(10)
"#
        ),
        1
    );
}

// PICKED: function reference passed as value and called via closure application
#[test]
fn apply_simple_closure_no_captures() {
    assert_eq!(
        run_main(
            r#"
fn double(x), do: x * 2
fn apply_f(f, n), do: f.(n)
fn main(), do: apply_f(double, 21)
"#
        ),
        42
    );
}

// DROP: old-world CLIF IR static callable singleton path, no compiler2 analogue
#[test]
fn thin_fn_refs_lower_through_static_callable_singletons_without_closure_alloc() {
    let ir = compile_and_grab_all_ir(
        r#"
fn double(x), do: x * 2
fn apply_f(f, n), do: f.(n)
fn main(), do: apply_f(double, 21)
"#,
    );
    assert!(
        ir.iter().any(|(_, body)| body.contains("fz_get_static_closure")),
        "thin callable values should lower through the static callable singleton path: {:?}",
        ir.iter().map(|(name, _)| name).collect::<Vec<_>>()
    );
    assert!(
        ir.iter().all(|(_, body)| !body.contains("fz_alloc_closure")),
        "thin callable values should not allocate closure environments in codegen:\n{}",
        ir.iter()
            .map(|(name, body)| format!("-- {name} --\n{body}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// PICKED: closure captures enclosing scope variable and uses it on call
#[test]
fn closure_captures_local_value() {
    assert_eq!(
        run_main(
            r#"
fn make_adder(k), do: fn(x) -> x + k end
fn main() do
  f = make_adder(10)
  f.(5)
end
"#
        ),
        15
    );
}

// DROP: old-world CLIF IR closure alloc instruction names, no compiler2 analogue
#[test]
fn captured_closures_still_emit_closure_allocations() {
    let ir = compile_and_grab_all_ir(
        r#"
fn make_adder(k), do: fn(x) -> x + k end
fn main() do
  f = make_adder(10)
  f.(5)
end
"#,
    );
    assert!(
        ir.iter().any(|(_, body)| body.contains("fz_alloc_closure")),
        "captured closures should still allocate closure environments in codegen:\n{}",
        ir.iter()
            .map(|(name, body)| format!("-- {name} --\n{body}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// DROP: old-world CLIF IR alias-mark instruction for closure ref captures
#[test]
fn closure_literal_marks_ref_captures_as_published() {
    let ir = compile_and_grab_ir(
        r#"
fn main() do
  xs = [1, 2]
  f = fn() -> xs end
  f.()
end
"#,
        "main",
    );
    assert!(
        ir.contains("@fz_mark_published_ref_aliased") && ir.contains("@fz_closure_set_capture_ref"),
        "closure ref captures should be alias-marked before publication:\n{}",
        ir
    );
}

// PICKED: higher-order map applies function to each element and collects results
#[test]
fn map_higher_order_renders_doubled_list() {
    assert_eq!(
        capture_main(
            r#"
fn double(x), do: x * 2
fn map_l(_, []), do: []
fn map_l(f, [h | t]), do: [f.(h) | map_l(f, t)]
fn main(), do: dbg(map_l(double, [1, 2, 3]))
"#
        ),
        vec!["[2, 4, 6]"]
    );
}

// PICKED: list equality is structural not referential across distinct allocations
#[test]
fn list_structural_eq_same_content_distinct_allocations() {
    assert_eq!(run_main("fn main(), do: [1, 2, 3] == [1, 2, 3]"), 1);
}

// PICKED: list equality is false when lists have different lengths
#[test]
fn list_structural_eq_length_mismatch_is_false() {
    assert_eq!(run_main("fn main(), do: [1, 2] == [1, 2, 3]"), FALSE_HALT);
}

// PICKED: tuple equality holds when arity and all fields match
#[test]
fn tuple_structural_eq_same_arity_and_content() {
    assert_eq!(run_main("fn main(), do: {1, :ok} == {1, :ok}"), 1);
}

// PICKED: tuple equality is false when arities differ
#[test]
fn tuple_eq_different_arity_is_false() {
    assert_eq!(run_main("fn main(), do: {1, 2} == {1, 2, 3}"), FALSE_HALT);
}

// PICKED: bitstring equality compares byte content structurally
#[test]
fn bitstring_structural_eq_byte_aligned() {
    assert_eq!(run_main("fn main(), do: <<1, 2, 3>> == <<1, 2, 3>>"), 1);
}

// PICKED: map equality is order-independent, compares keys and values structurally
#[test]
fn map_structural_eq_ignores_construction_order() {
    assert_eq!(run_main("fn main(), do: %{a: 1, b: 2} == %{b: 2, a: 1}"), 1);
}

// PICKED: map equality is false when values differ for matching keys
#[test]
fn map_eq_different_value_is_false() {
    assert_eq!(run_main("fn main(), do: %{a: 1, b: 2} == %{a: 1, b: 3}"), FALSE_HALT);
}

// PICKED: different container kinds (list vs tuple) are never equal
#[test]
fn heterogeneous_kinds_compare_unequal() {
    assert_eq!(run_main("fn main(), do: [1, 2] == {1, 2}"), FALSE_HALT);
}

// PICKED: nested map containing list compares recursively by value
#[test]
fn nested_map_with_list_structural_eq() {
    assert_eq!(run_main("fn main(), do: %{x: [1, 2]} == %{x: [1, 2]}"), 1);
}

// PICKED: != operator returns logical inverse of structural equality
#[test]
fn neq_inverts_structural_eq() {
    assert_eq!(run_main("fn main(), do: [1, 2] != [1, 2]"), FALSE_HALT);
    assert_eq!(run_main("fn main(), do: [1, 2] != [1, 3]"), 1);
}

// PICKED: float literal preserves bit-exact value in return
#[test]
fn float_const_halt_round_trips_via_bits() {
    let (halt, _m) = run_main_returning_module("fn main(), do: 2.5");
    assert_eq!(f64::from_bits(halt as u64), 2.5);
}

// PICKED: float literals render with explicit decimal point in output
#[test]
fn print_float_renders_with_explicit_dot_zero() {
    assert_eq!(
        capture_main("fn main() do\n  dbg(4.0)\n  dbg(2.5)\nend"),
        vec!["4.0", "2.5"]
    );
}

// PICKED: float addition evaluates correctly and compares equal to expected result
#[test]
fn float_arithmetic_promotes_via_runtime_helper() {
    assert_eq!(run_main("fn main(), do: 1.5 + 2.5 == 4.0"), 1);
}

// PICKED: mixed int and float arithmetic promotes integer to float
#[test]
fn mixed_int_float_arithmetic_promotes() {
    assert_eq!(run_main("fn main(), do: 1 + 2.0 == 3.0"), 1);
}

// PICKED: integer and float with same numeric value are not equal by strict equality
#[test]
fn mixed_int_float_eq_does_not_promote() {
    assert_eq!(run_main("fn main(), do: 1 == 1.0"), FALSE_HALT);
}

// PICKED: identical float literals compare equal
#[test]
fn float_literals_compare_equal_by_value() {
    assert_eq!(run_main("fn main(), do: 1.5 == 1.5"), 1);
}

// PICKED: float ordered comparison returns correct boolean result
#[test]
fn float_ordered_comparison_dispatches_through_helper() {
    assert_eq!(run_main("fn main(), do: 1.5 < 2.0"), 1);
}

// PICKED: float bitstring field stores raw IEEE 754 bits big-endian
#[test]
fn float_bit_field_round_trips_via_bitstring() {
    let (halt, _m) = run_main_returning_module("fn main(), do: <<2.5::float>>");
    let halt = halt as u64;
    let p = bitstring_addr_from_tagged(halt).unwrap();
    let bytes = unsafe { std::slice::from_raw_parts(bitstring_bytes_ptr(p as *const u8), 8) };
    let mut buf = [0u8; 8];
    buf.copy_from_slice(bytes);
    let f = f64::from_bits(u64::from_be_bytes(buf));
    assert_eq!(f, 2.5);
}

// PICKED: float as list head allocates only one cons cell without boxing
#[test]
fn cons_with_float_head_no_box() {
    assert_eq!(
        run_main_and_count_live("fn main(), do: [3.14]"),
        1,
        "float list literal should allocate only the cons cell"
    );
}

// PICKED: float inside a list renders correctly
#[test]
fn render_raw_float_in_container() {
    assert_eq!(capture_main("fn main(), do: dbg([1.5])"), vec!["[1.5]"]);
}

// PICKED: list head projection retrieves float element with correct value
#[test]
fn float_list_head_projects_raw_f64() {
    let src = "fn first([h | _]), do: h\nfn main(), do: first([2.5])";
    let (halt, _m) = run_main_returning_module(src);
    assert_eq!(f64::from_bits(halt as u64), 2.5);
}

// PICKED: list containing float compares equal by value
#[test]
fn equality_float_in_container() {
    assert_eq!(run_main("fn main(), do: [1.5] == [1.5]"), 1);
}

// PICKED: map with float value allocates only one object without boxing float
#[test]
fn map_with_float_value_no_box() {
    assert_eq!(
        run_main_and_count_live("fn main(), do: %{a: 3.14}"),
        1,
        "float map literal should allocate only the map"
    );
}

// PICKED: map with float key allocates only one object without boxing float key
#[test]
fn map_with_float_key_no_box() {
    assert_eq!(
        run_main_and_count_live("fn main(), do: %{3.14 => :ok}"),
        1,
        "float map key should allocate only the map"
    );
}

// DROP: old-world CLIF IR map destination helper names, no compiler2 analogue
#[test]
fn map_literal_and_update_use_destinations_not_repeated_puts() {
    let ir = compile_and_grab_ir(
        "fn main() do\n  m = %{a: 1, b: 2}\n  n = %{m | a: 3, c: 4}\n  dbg(n[:a])\nend",
        "main",
    );
    assert!(
        ir.contains("@fz_map_dest_begin")
            && ir.contains("@fz_map_dest_begin_update")
            && ir.contains("@fz_map_dest_put")
            && ir.contains("@fz_map_dest_freeze"),
        "map literals and updates should lower through destination begin/put/freeze:\n{}",
        ir
    );
    assert!(
        !ir.contains(concat!("@fz_map", "_builder_")),
        "map destinations should not expose the old builder helper surface:\n{}",
        ir
    );
    assert!(
        !ir.contains("@fz_map_put_"),
        "known-entry map construction should not be repeated immutable map_put copies:\n{}",
        ir
    );
}

// DROP: old-world CLIF IR alias-mark for map ref entries, no compiler2 analogue
#[test]
fn map_literal_marks_ref_entries_as_published() {
    let ir = compile_and_grab_ir("fn main() do\n  xs = [1, 2]\n  %{a: xs}\nend", "main");
    assert!(
        ir.contains("@fz_mark_published_ref_aliased") && ir.contains("@fz_map_dest_put_ref"),
        "map ref entries should be alias-marked before publication:\n{}",
        ir
    );
}

// PICKED: self-applying closure in tail position reuses frame across iterations
#[test]
fn tail_call_closure_reuses_frame_via_count_loop() {
    // Self-applying closure forces TailCallClosure on every iteration.
    let src = r#"
fn loop_with(f, 0, acc), do: acc
fn loop_with(f, n, acc), do: f.(f, n - 1, acc + 1)
fn main(), do: loop_with(loop_with, 100000, 0)
"#;
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let entry = graph.module.fn_by_name("main").expect("main").id;
    let loop_with = graph.module.fn_by_name("loop_with").expect("loop_with").id;
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");

    assert_eq!(
        compiled
            .static_closure_targets()
            .iter()
            .filter(|(_, fn_id, _, _)| *fn_id == loop_with.0)
            .count(),
        2,
        "self-applying loop_with/3 needs one function-value singleton and one specialized direct-self singleton: {:?}",
        compiled.static_closure_targets()
    );
    assert_eq!(compiled.run(&ConfiguredTelemetry::new(), entry), 100_000);
}

#[test]
fn list_projection_accepts_block_env_nonempty_fact() {
    let mut t = crate::types::new();
    let xs = Var(1);
    let mut fn_types = SpecPlan::default();
    let list_ty = {
        let elem = t.any();
        t.list(elem)
    };
    fn_types.vars.insert(xs, list_ty);

    let mut block_env = HashMap::new();
    let nonempty_ty = {
        let elem = t.any();
        t.non_empty_list(elem)
    };
    block_env.insert(xs, nonempty_ty);

    assert!(
        list_projection_is_safe(&mut t, &fn_types, xs, Some(&block_env)),
        "branch-narrowed block env should make direct list projection safe"
    );
}

#[test]
fn list_projection_rejects_unnarrowed_block_env() {
    let mut t = crate::types::new();
    let xs = Var(1);
    let mut fn_types = SpecPlan::default();
    let list_ty = {
        let elem = t.any();
        t.list(elem)
    };
    fn_types.vars.insert(xs, list_ty.clone());

    let mut block_env = HashMap::new();
    block_env.insert(xs, list_ty);

    assert!(
        !list_projection_is_safe(&mut t, &fn_types, xs, Some(&block_env)),
        "possibly-empty list facts must stay on the checked helper path"
    );
}

/// Compile `src` through the production execution graph with IR text recording
/// enabled, and return every emitted CLIF body.
fn compile_and_grab_all_ir(src: &str) -> Vec<(String, String)> {
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    ir_text_record_enable();
    let _ = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    ir_text_record_take()
}

/// Lower `src`, compile with IR text recording enabled, and return the
/// recorded CLIF body for the fn whose name equals `fn_name`. Returns
/// an empty string if no such fn was emitted — matches the prior
/// `unwrap_or("")` pattern at the call sites.
fn compile_and_grab_ir(src: &str, fn_name: &str) -> String {
    compile_and_grab_all_ir(src)
        .into_iter()
        .find(|(n, _)| n == fn_name)
        .map(|(_, s)| s)
        .unwrap_or_default()
}

fn compiled_ir_body_containing(src: &str, needle: &str) -> String {
    compiled_ir_body_matching(src, needle, |body| body.contains(needle))
}

fn compiled_ir_body_matching<F>(src: &str, label: &str, pred: F) -> String
where
    F: Fn(&str) -> bool,
{
    let ir = compile_and_grab_all_ir(src);
    ir.iter()
        .find(|(_, body)| pred(body))
        .map(|(_, body)| body.clone())
        .unwrap_or_else(|| {
            let names = ir.into_iter().map(|(name, _)| name).collect::<Vec<_>>();
            panic!("no emitted CLIF body matched `{label}`; bodies: {names:?}")
        })
}

// DROP: old-world CLIF IR brif elision for int arithmetic, no compiler2 analogue
#[test]
fn arith_int_int_elides_dispatch() {
    let ir = compile_and_grab_ir("fn main(), do: 1 + 2", "main");
    assert!(!ir.contains("brif"), "elision should drop the both_int branch:\n{}", ir);
}

// DROP: old-world planner SpecPlan and ArgRepr uniform signature shape
#[test]
fn signature_uniform_when_not_native() {
    // Uniform (non-native) sig: `(i64, i64) -> i64` regardless of the
    // typer's narrower facts on the params.
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do dbg(add(1, 2)) end");
    let mt = plan_module_with_role(
        &mut crate::types::new(),
        &m,
        &crate::telemetry::ConfiguredTelemetry::new(),
        "test",
    );
    let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
    let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
    let mut t = crate::types::new();
    let prs = build_param_reprs(&mut t, &m.fns[add_idx], ft);
    let sig = build_fn_signature(&prs, false, true, None, None);
    assert_eq!(sig.params.len(), 2);
    assert_eq!(sig.returns.len(), 1);
    assert_eq!(sig.params[0].value_type, types::I64);
    assert_eq!(sig.params[1].value_type, types::I64);
    assert_eq!(sig.returns[0].value_type, types::I64);
}

#[test]
fn param_reprs_for_spec_use_concrete_key_when_entry_var_is_generic() {
    let mut t = crate::types::new();
    let mut builder = FnBuilder::new(FnId(0), "k");
    let x = builder.fresh_var();
    let entry = builder.block(vec![x]);
    builder.set_terminator(entry, Term::Return(x));
    let f = builder.build();

    let mut ft = SpecPlan::default();
    ft.vars.insert(x, t.any());
    let int = t.int();
    let key = SpecKey::value(f.id, key_slots_from_tys(vec![int]));

    let reprs = build_param_reprs_for_spec(&mut t, &f, &ft, &key, false);

    assert_eq!(reprs, vec![ArgRepr::RawInt]);
}

#[test]
fn tuple_field_return_demand_does_not_rewrite_plain_function_params() {
    let mut t = crate::types::new();
    let mut builder = FnBuilder::new(FnId(0), "pair");
    let a = builder.fresh_var();
    let b = builder.fresh_var();
    let entry = builder.block(vec![a, b]);
    let pair = builder.let_(entry, Prim::MakeTuple(vec![a, b]));
    builder.set_terminator(entry, Term::Return(pair));
    let f = builder.build();

    let mut ft = SpecPlan::default();
    ft.vars.insert(a, t.any());
    ft.vars.insert(b, t.any());
    let int = t.int();
    let float = t.float();
    let key = SpecKey {
        fn_id: f.id,
        input: key_slots_from_tys(vec![int, float]),
        demand: ReturnDemand::tuple_fields(2),
    };

    let reprs = build_param_reprs_for_spec(&mut t, &f, &ft, &key, false);

    assert_eq!(reprs, vec![ArgRepr::RawInt, ArgRepr::RawF64]);
}

// PICKED: chained non-tail closure calls compose correctly and return right values
#[test]
fn non_tail_closure_call_chain_uses_value_ref_continuation_abi() {
    let src = r#"
fn double(x), do: x * 2
fn neg(x), do: 0 - x
fn apply2(f, x), do: f.(x)
fn compose(f, g, x), do: f.(g.(x))
fn main() do
  assert(apply2(double, 21) == 42, "apply2 calls a passed fn")
  assert(apply2(neg, 7) == -7, "apply2 with neg")
  assert(compose(double, neg, 5) == -10, "compose chains two fns")
end
"#;
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "abi_contract"], cap.handler());

    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    #[derive(Debug)]
    struct AbiContract {
        fn_name: String,
        param_reprs: Vec<String>,
        return_repr: String,
        is_cont_fn: bool,
    }

    let contracts = cap
        .find(&["fz", "codegen", "abi_contract"])
        .into_iter()
        .map(|event| {
            let fn_name = match event.metadata.get("fn_name") {
                Some(Value::Str(name)) => name.to_string(),
                other => panic!("abi_contract missing fn_name: {other:?}"),
            };
            let param_reprs = match event.metadata.get("param_reprs") {
                Some(Value::StrSeq(reprs)) => reprs.to_vec(),
                other => panic!("abi_contract missing param_reprs: {other:?}"),
            };
            let return_repr = match event.metadata.get("return_repr") {
                Some(Value::Str(repr)) => repr.to_string(),
                other => panic!("abi_contract missing return_repr: {other:?}"),
            };
            let is_cont_fn = match event.metadata.get("is_cont_fn") {
                Some(Value::Bool(value)) => *value,
                other => panic!("abi_contract missing is_cont_fn: {other:?}"),
            };
            AbiContract {
                fn_name,
                param_reprs,
                return_repr,
                is_cont_fn,
            }
        })
        .collect::<Vec<_>>();

    let compose = contracts
        .iter()
        .find(|contract| contract.fn_name == "compose")
        .unwrap_or_else(|| panic!("compose ABI contract missing: {contracts:?}"));
    assert_eq!(
        compose.return_repr, "ValueRef",
        "compose returns through a non-tail closure-call chain; its native return lane must stay tagged"
    );

    let continuation_contracts = contracts
        .iter()
        .filter(|contract| contract.is_cont_fn && contract.fn_name.starts_with("k_"))
        .collect::<Vec<_>>();
    assert!(
        !continuation_contracts.is_empty(),
        "test premise: compose lowering should materialize continuation bodies; contracts={contracts:?}"
    );
    assert!(
        continuation_contracts
            .iter()
            .all(|contract| contract.param_reprs.first().is_some_and(|repr| repr == "ValueRef")),
        "closure-call continuations must accept the boxed ValueRef lane produced by callable entries: {continuation_contracts:?}"
    );
}

// DROP: old-world demand specialization telemetry, planner SpecKey internals
#[test]
fn codegen_lowers_distinct_native_bodies_for_demand_specializations() {
    let src = "fn pair(x), do: {x, x}\n\
               fn main() do\n\
                 {a, b} = pair(1)\n\
                 dbg({a, b, pair(2)})\n\
               end\n";
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "codegen", "function_lowered"], cap.handler());

    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    let pair_lowered: Vec<_> = cap
        .find(&["fz", "codegen", "function_lowered"])
        .into_iter()
        .filter(|event| {
            matches!(event.metadata.get("body_kind"), Some(Value::Str(kind)) if kind == "fz_spec")
                && matches!(event.metadata.get("fn_name"), Some(Value::Str(name)) if name.starts_with("pair"))
        })
        .collect();
    // `pair` is reached with two return demands — `tuple_fields(2)` from the
    // destructure and `value` from `pair(2)`. Demand is part of the spec
    // identity and drives the return ABI, so the two specializations lower as
    // distinct native bodies (fields vs struct), never merged onto one ABI.
    assert_eq!(
        pair_lowered.len(),
        2,
        "demand specializations with distinct return ABIs lower distinct native bodies: {pair_lowered:#?}"
    );
}

// DROP: old-world planner SpecPlan native signature shape with continuation param
#[test]
fn signature_native_uses_typed_params_and_cont() {
    // Same `add`, but call-site narrowing has typed both params as int.
    // Native sig is `(i64, i64, cont: i64) -> i64` (cont trailing).
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do dbg(add(1, 2)) end");
    let mt = plan_module_with_role(
        &mut crate::types::new(),
        &m,
        &crate::telemetry::ConfiguredTelemetry::new(),
        "test",
    );
    let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
    let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
    let mut t = crate::types::new();
    let prs = build_param_reprs(&mut t, &m.fns[add_idx], ft);
    let sig = build_fn_signature(&prs, true, false, None, None);
    assert_eq!(sig.params.len(), 3);
    assert_eq!(sig.returns.len(), 1);
    assert_eq!(sig.params.last().unwrap().value_type, types::I64);
    assert_eq!(sig.returns[0].value_type, types::I64);
}

// DROP: old-world planner native signature arity for float params and continuation
#[test]
fn signature_native_arity_matches_entry_params_plus_cont() {
    // Native sig is per-type typed: call-site narrowing types `x` and
    // `y` as float-only, so the sig is `(f64, f64, cont: i64) -> i64`.
    // (Return is canonicalized to i64 even when the value is a float —
    // see the i64-return assertion below.)
    let m = lower_src("fn dist(x, y) do x * x + y * y end\nfn main() do dbg(dist(1.5, 2.5)) end");
    let mt = plan_module_with_role(
        &mut crate::types::new(),
        &m,
        &crate::telemetry::ConfiguredTelemetry::new(),
        "test",
    );
    let dist_idx = m.fns.iter().position(|f| f.name == "dist").unwrap();
    let ft = mt.any_spec_for(m.fns[dist_idx].id).expect("registered spec");
    let mut t = crate::types::new();
    let prs = build_param_reprs(&mut t, &m.fns[dist_idx], ft);
    let sig = build_fn_signature(&prs, true, false, None, None);
    assert_eq!(sig.params.len(), 3);
    assert_eq!(sig.params[0].value_type, types::F64);
    assert_eq!(sig.params[1].value_type, types::F64);
    assert_eq!(sig.params[2].value_type, types::I64); // cont
    // Native return is canonicalized to i64: the cont indirect sig is
    // `(i64, i64) -> i64 tail`, and Cranelift's tail-call verifier
    // requires the caller's return type to match.
    assert_eq!(sig.returns[0].value_type, types::I64);
}

// DROP: old-world SpecRegistry SpecId/FnId identity invariant, planner internals
#[test]
fn spec_registry_registers_any_key_per_fn_with_spec_id_eq_fn_id() {
    // Pipeline registry must hold one any-key spec per fn, with
    // SpecId.0 == FnId.0.
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, "fn add(a, b) do a + b end\nfn main() do dbg(add(1, 2)) end");
    let compiled = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    // Driving a run forces the pipeline registry construction path
    // where the SpecId.0 == FnId.0 invariant is asserted.
    let _ = compiled.run(&ConfiguredTelemetry::new(), graph.module.fn_by_name("main").unwrap().id);
}

#[test]
fn spec_registry_any_key_lookup() {
    // Direct register/resolve/any_key contract — does not go through compile().
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let fid = FnId(0);
    let any_key_2 = vec![t.any(); 2];
    let sid = reg.register(&t, fid, any_key_2.clone());
    assert_eq!(sid.0, 0, "first registration gets SpecId(0)");
    let sid2 = reg.register(&t, fid, any_key_2.clone());
    assert_eq!(sid, sid2);
    let resolved = reg.resolve(&t, fid, &any_key_2);
    assert_eq!(resolved, Some(sid));
    let via_any = reg.any_key(fid, 2);
    assert_eq!(via_any, sid);
    let other_sid = reg.register(&t, FnId(1), Vec::<KeySlot>::new());
    assert_eq!(other_sid.0, 1);
    assert_eq!(reg.len(), 2);
}

#[test]
fn spec_registry_distinct_narrow_keys() {
    // Narrow keys are distinguished by the exact-match fast path
    // (subsumption fallback is exercised below).
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let fid = FnId(0);
    let int1 = vec![t.int()];
    let float1 = vec![t.float()];
    let sid_int = reg.register(&t, fid, int1.clone());
    let sid_float = reg.register(&t, fid, float1.clone());
    assert_ne!(sid_int, sid_float, "int-key and float-key must be distinct SpecIds");
    assert_eq!(reg.resolve(&t, fid, &int1), Some(sid_int));
    assert_eq!(reg.resolve(&t, fid, &float1), Some(sid_float));
    let atom1 = vec![t.atom()];
    assert_eq!(reg.resolve(&t, fid, &atom1), None);
}

#[test]
fn resolve_subsumes_narrower_query_to_wider_registered_spec() {
    // Only [int] registered; query [int_lit(4)] should subsume to it.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let fid = FnId(0);
    let int = t.int();
    let int_spec = reg.register(&t, fid, vec![int]);
    let q = vec![t.int_lit(4)];
    assert_eq!(reg.resolve(&t, fid, &q), Some(int_spec));
}

#[test]
fn resolve_picks_narrowest_among_multiple_supertype_matches() {
    // Both [int] and [any] cover [int_lit(4)]. [int] is narrower; pick it.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let fid = FnId(0);
    let any = t.any();
    let any_spec = reg.register(&t, fid, vec![any]);
    let int = t.int();
    let int_spec = reg.register(&t, fid, vec![int]);
    let q = vec![t.int_lit(4)];
    let resolved = reg.resolve(&t, fid, &q);
    assert_eq!(
        resolved,
        Some(int_spec),
        "should pick narrower [int] over wider [any]; got {:?}, any={:?}, int={:?}",
        resolved,
        any_spec,
        int_spec
    );
}

#[test]
fn resolve_returns_none_when_nothing_covers() {
    // [float] registered; query [int_lit(4)] is not a subtype → None.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let fid = FnId(0);
    let float = t.float();
    reg.register(&t, fid, vec![float]);
    let q = vec![t.int_lit(4)];
    assert_eq!(
        reg.resolve(&t, fid, &q),
        None,
        "int_lit(4) is not a subtype of float; no covering spec"
    );
}

#[test]
fn resolve_subtype_incomparable_uses_stable_precedence() {
    // [int, any] and [any, atom] both cover [int_lit(4), :foo] but
    // neither key is a subtype of the other on every axis. Stable
    // per-family precedence (not incidental SpecId order) breaks the tie.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let fid = FnId(0);
    let int = t.int();
    let any_a = t.any();
    let sid_a = reg.register_with_precedence(&t, fid, vec![int, any_a], 1);
    let any_b = t.any();
    let atom = t.atom();
    let sid_b = reg.register_with_precedence(&t, fid, vec![any_b, atom], 0);
    assert!(sid_a.0 < sid_b.0, "test expects precedence and SpecId order to diverge");
    let q = vec![t.int_lit(4), t.atom_lit(":foo")];
    let resolved = reg.resolve(&t, fid, &q).expect("a covering spec exists");
    assert_eq!(
        resolved, sid_b,
        "subtype-incomparable matches should honor stable precedence; got {:?}, a={:?}, b={:?}",
        resolved, sid_a, sid_b
    );
}

#[test]
fn resolve_exact_match_takes_fast_path() {
    // O(1) exact-match path still works alongside subsumption fallback.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let fid = FnId(0);
    let key = vec![t.int(), t.float()];
    let sid = reg.register(&t, fid, key.clone());
    assert_eq!(reg.resolve(&t, fid, &key), Some(sid));
}

#[test]
fn resolve_per_fn_isolation() {
    // Specs for one fn must not subsume queries for a different fn.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::new();
    let any = t.any();
    let _sid0 = reg.register(&t, FnId(0), vec![any]);
    let q = vec![t.int()];
    assert_eq!(reg.resolve(&t, FnId(1), &q), None);
}

/// Lazy continuation materialization keeps straight native continuation chains
/// off the heap on the production planned-codegen path.
// DROP: old-world frame_alloc_count instrumentation, no compiler2 analogue
#[test]
fn hot_loop_native_continuations_allocate_no_heap_closures() {
    let src = "fn step(x), do: x + 1\n\
               fn main(), do: step(step(step(step(step(step(step(step(step(step(0))))))))))";

    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    frame_alloc_count_reset();
    let entry = graph.module.fn_by_name("main").unwrap().id;
    let result = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned")
    .run(&ConfiguredTelemetry::new(), entry);
    let allocation_count = frame_alloc_count_take();

    assert_eq!(result, 10, "result must still be 10");
    assert_eq!(
        allocation_count, 0,
        "native continuation chain should not allocate heap closures"
    );
}

/// A typed `send(int, int)` call keeps raw integer literals raw at the caller
/// and boxes the message exactly once inside the selected `Kernel.send`
/// boundary before calling the mailbox runtime.
// DROP: old-world CLIF IR fz_box_int_for_any/fz_send_ref instruction names
#[test]
fn typed_send_literal_boxes_message_at_kernel_boundary() {
    let src = "fn relay() do\n\
                 msg = receive do x -> x end\n\
                 send(1, msg + 1)\n\
               end\n\
               fn main() do\n\
                 spawn(relay)\n\
                 send(2, 41)\n\
                 dbg(receive do x -> x end)\n\
               end";
    let caller_ir = compiled_ir_body_matching(src, "raw literal send caller", |body| {
        body.contains("iconst.i64 41") && body.contains("call fn0(v2, v3")
    });
    let caller_ir = caller_ir.as_str();
    assert!(
        !caller_ir.contains("@fz_box_int_for_any"),
        "send caller should pass raw int literals to the typed Kernel.send specialization:\n{}",
        caller_ir
    );

    let send_ir = compiled_ir_body_matching(src, "typed Kernel.send boundary", |body| {
        body.contains("@fz_box_int_for_any") && body.contains("@fz_send_ref")
    });
    let send_ir = send_ir.as_str();
    assert!(
        send_ir.contains("@fz_send_ref") && !send_ir.contains("iconst.i8 13"),
        "Kernel.send(int, int) should box once and call the one-word mailbox ABI:\n{}",
        send_ir
    );
}

// DROP: old-world CLIF IR fz_box_float/fz_send_ref instruction names for send
#[test]
fn mailbox_with_float_boxes_only_at_send_boundary() {
    let src = "fn main() do\n  send(self(), 3.14)\n  nil\nend";
    let send_ir = compiled_ir_body_containing(src, "@fz_send_ref");
    let send_ir = send_ir.as_str();
    assert!(
        send_ir.contains("fz_box_float_for_any") && send_ir.contains("fz_send_ref"),
        "expected float send to box explicitly at the one-word send boundary:\n{}",
        send_ir
    );
}

/// Catch-all selective receive must not re-tag the arithmetic input on
/// the relay side before forwarding it through `Kernel.send`.
// DROP: old-world CLIF IR ishl_imm retagging check, no compiler2 analogue
#[test]
fn receive_native_cont_no_box_unbox_roundtrip() {
    let src = "fn relay() do\n\
                 msg = receive do x -> x end\n\
                 send(1, msg + 1)\n\
               end\n\
               fn main() do\n\
                 spawn(relay)\n\
                 send(2, 41)\n\
                 dbg(receive do x -> x end)\n\
               end";
    let relay_ir = compile_and_grab_ir(src, "relay");
    let relay_ir = relay_ir.as_str();
    // The catch-all receive path should keep the integer arithmetic unboxed
    // through relay's block, so no spurious retagging appears here.
    assert!(
        !relay_ir.contains("ishl_imm"),
        "spurious box in relay CLIF — integer capture was re-tagged before Receive:\n{}",
        relay_ir
    );
}

/// TypeTest i1 cached in the `condition` map; Term::If consumes it
/// directly, bypassing the bool_to_fz → is_truthy roundtrip. Without
/// the cache, brif would be preceded by an `icmp ne` decoding the
/// tagged bool back to i1.
///
/// Per-spec fold otherwise resolves literal-only call sites entirely,
/// so this test routes through a closure to force `check`'s any-key
/// spec where the TypeTest+If actually survives.
// DROP: old-world CLIF IR brif/icmp-ne condition cache internals, no compiler2 analogue
#[test]
fn condition_cache_bypasses_is_truthy_in_type_dispatch() {
    let src = "fn check(x :: integer) do :is_int end\n\
               fn check(x) do :other end\n\
               fn main() do\n\
                 c = fn(x) -> check(x) end\n\
                 dbg(c.(42))\n\
                 dbg(c.(:foo))\n\
               end";
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    ir_text_record_enable();
    let _ = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    let ir = ir_text_record_take();
    // Per-spec fold may eliminate every brif if it can statically
    // resolve the dispatch — that's fine. For any spec that retains a
    // brif, verify no spurious icmp-ne decode sits next to it.
    let with_brif: Vec<(&str, &str)> = ir
        .iter()
        .filter(|(_, s)| s.contains("brif"))
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect();
    for (n, s) in &with_brif {
        assert!(
            !s.contains("icmp ne"),
            "spurious is_truthy icmp ne in {} CLIF — condition cache not applied:\n{}",
            n,
            s
        );
    }
}

/// ArgRepr::Condition: a pure-branch TypeTest does not materialize a
/// tagged bool — the i1 is fed straight to brif. Strict value decoding
/// elsewhere may legitimately use `select`, so this test gates the bool
/// materialization constants (the true/false atom words) instead of
/// banning every select in the function.
// DROP: old-world CLIF IR bool materialization constants, no compiler2 analogue
#[test]
fn pure_branch_type_test_does_not_materialize_bool() {
    // Route via closure so check's any-key spec retains the TypeTest+If
    // (per-spec fold otherwise eliminates it).
    let src = "fn check(x :: integer) do :is_int end\n\
               fn check(x) do :other end\n\
               fn main() do\n\
                 c = fn(x) -> check(x) end\n\
                 dbg(c.(42))\n\
                 dbg(c.(:foo))\n\
               end";
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    ir_text_record_enable();
    let _ = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    let ir = ir_text_record_take();
    let with_brif: Vec<(&str, &str)> = ir
        .iter()
        .filter(|(_, s)| s.contains("brif"))
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect();
    for (n, s) in &with_brif {
        assert!(
            !(s.contains("iconst.i64 10") || s.contains("iconst.i64 18")),
            "spurious bool_to_fz constants in {} CLIF — bool was emitted eagerly:\n{}",
            n,
            s
        );
    }
}

// PICKED: dbg/1 returns its argument allowing use in further expressions
#[test]
fn dbg_returns_the_value_it_prints() {
    let lines = capture_main(
        "fn main() do\n\
           x = dbg(41)\n\
           dbg(x + 1)\n\
         end",
    );
    assert_eq!(lines, vec!["41".to_string(), "42".to_string()]);
}

// DROP: old-world CLIF IR fz_box_int/fz_unbox_int instruction names for dbg
#[test]
fn dbg_direct_intrinsic_uses_any_extern_abi_without_result_coercion() {
    let src = "fn main(), do: dbg(40) + 2";
    let dbg_ir = compiled_ir_body_containing(src, "@fz_dbg_value");
    assert!(
        dbg_ir.contains("@fz_box_int_for_any"),
        "dbg should box the typed arg for the extern any ABI:\n{}",
        dbg_ir
    );
    assert!(
        dbg_ir.contains("@fz_dbg_value"),
        "dbg should call the generic any extern:\n{}",
        dbg_ir
    );
    assert!(
        !dbg_ir.contains("@fz_unbox_int"),
        "direct dbg returns the original typed value, so it must not unbox the extern's any result:\n{}",
        dbg_ir
    );
    assert!(
        !dbg_ir.contains("fz_print_"),
        "dbg should not use typed print helper ABI:\n{}",
        dbg_ir
    );
}

/// Const::Nil/Bool/Atom use canonical raw+kind parts; the old encoded
/// nil scalar (`iconst.i64 2`) should not survive codegen.
// DROP: old-world CLIF IR nil iconst encoding check, no compiler2 analogue
#[test]
fn const_nil_bool_atom_deduplicated_within_block() {
    let src = "fn main() do\n\
                 dbg(nil)\n\
               end";
    let main_ir = compile_and_grab_ir(src, "main");
    let main_ir = main_ir.as_str();
    let nil_count = main_ir.matches("iconst.i64 2").count();
    assert_eq!(
        nil_count, 0,
        "expected no encoded nil iconsts in main, got {}:\n{}",
        nil_count, main_ir
    );
    assert!(
        main_ir.contains("@fz_box_atom_for_any"),
        "expected live nil to cross the ValueRef ABI by boxing the atom payload:\n{}",
        main_ir
    );
}

// DROP: old-world planner telemetry role sequencing, no compiler2 analogue
#[test]
fn codegen_pipeline_reports_frontend_and_linked_plans() {
    let src = "fn main(), do: dbg(42)";
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "planner", "planned"], cap.handler());
    let mut t = crate::types::new();
    let graph = runtime_graph_observed(&mut t, src, &tel);
    let roles = planner_roles(&cap);
    assert_eq!(
        roles,
        vec!["frontend_check".to_string(), "linked_execution_graph".to_string()],
        "source execution graph should publish frontend and linked-module planner phases"
    );
    cap.clear();
    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");
    assert!(
        planner_roles(&cap).is_empty(),
        "planned codegen must consume the supplied plan without publishing another planner.planned event"
    );
}

// DROP: old-world planner phase telemetry events, no compiler2 analogue
#[test]
fn frontend_to_codegen_pipeline_reports_planner_phase_events() {
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let src = "fn id(x), do: x\nfn main(), do: dbg(id(42))\n";
    let mut t = crate::types::new();
    let frontend = match compile_source_with_types(&mut t, src.to_string(), "test.fz".to_string(), &tel) {
        Ok(frontend) => frontend,
        Err(_) => panic!("frontend"),
    };

    let checked = checked_module_for_mode(&mut t, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    let graph = prepare_execution_graph(&mut t, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));
    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    let roles = planner_roles(&cap);
    assert_eq!(
        roles,
        vec!["frontend_check".to_string(), "linked_execution_graph".to_string()],
        "pretyped pipeline should report only frontend and linked-module planner phases"
    );
}

// DROP: old-world planner activation projection telemetry, planner internals
#[test]
fn enum_take_drop_split_codegen_plan_reports_activation_projection_telemetry() {
    let src = include_str!("../../fixtures/enum_take_drop_split/input.fz");
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "planner", "planned"], cap.handler());
    let mut t = crate::types::new();
    let graph = runtime_graph_observed(&mut t, src, &tel);
    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile");

    let ev = cap
        .find(&["fz", "planner", "planned"])
        .into_iter()
        .filter(|ev| {
            matches!(
                ev.metadata.get("role"),
                Some(Value::Str(role)) if role == "linked_execution_graph"
            )
        })
        .last()
        .expect("linked-module planner event");
    let _ = ev;
    assert_authoritative_planner_consistent(&cap);
}

// DROP: old-world planner spec-pair inventory continuation edge telemetry
#[test]
fn enum_take_drop_split_planner_telemetry_reports_continuation_edges() {
    let src = include_str!("../../fixtures/enum_take_drop_split/input.fz");
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "planner", "spec_pair_inventory"], cap.handler());
    let mut t = crate::types::new();
    let graph = runtime_graph_observed(&mut t, src, &tel);
    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile");

    let events = cap
        .find(&["fz", "planner", "spec_pair_inventory"])
        .into_iter()
        .filter(|ev| {
            matches!(
                ev.metadata.get("role"),
                Some(Value::Str(role)) if role == "linked_execution_graph"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        !events.is_empty(),
        "compile should publish linked execution graph spec-pair inventory"
    );
    for body_name in ["Enum.take_positive", "Enum.drop_positive", "Enum.reduce"] {
        let has_cont_edge = events.iter().any(|ev| {
            matches!(
                ev.metadata.get("body_name"),
                Some(Value::Str(name)) if name == body_name
            ) && matches!(
                ev.metadata.get("plan_call_edges"),
                Some(Value::StrSeq(edges)) if edges.iter().any(|edge| edge.starts_with("cont@"))
            )
        });
        assert!(
            has_cont_edge,
            "linked execution graph telemetry should report a Cont edge for {body_name}; events={events:?}"
        );
    }
}

// DROP: old-world codegen/planner spec-pair inventory telemetry, no compiler2 analogue
#[test]
fn compile_emits_spec_pair_inventory_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let src = "fn id(x), do: x\nfn main(), do: dbg(id(42))\n";
    let mut t = crate::types::new();
    let frontend = compile_source_with_types(&mut t, src.to_string(), "test.fz".to_string(), &tel)
        .unwrap_or_else(|err| panic!("frontend: {:?}", err.diagnostics));

    let checked = checked_module_for_mode(&mut t, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    let graph = prepare_execution_graph(&mut t, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));
    compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");

    assert!(
        cap.count(&["fz", "codegen", "spec_pair_inventory"]) > 0,
        "compile should publish per-spec pair inventory"
    );
    assert!(
        cap.count(&["fz", "planner", "spec_pair_inventory"]) > 0,
        "compile should publish planner-side spec/body inventory"
    );
    let compile_spans = cap
        .find(&["fz", "compile"])
        .into_iter()
        .filter(|ev| ev.kind == EventKind::SpanStart)
        .collect::<Vec<_>>();
    assert!(
        !compile_spans.is_empty(),
        "frontend/codegen should publish compile spans"
    );
    let compile_span_ids = compile_spans.iter().map(|ev| ev.span_id).collect::<Vec<_>>();
    for ev in &compile_spans {
        assert!(
            matches!(ev.metadata.get("compile_nonce"), Some(Value::U64(n)) if *n > 0),
            "compile span should carry a non-zero compile_nonce"
        );
    }
    for ev in cap.find(&["fz", "codegen", "spec_pair_inventory"]) {
        assert!(
            compile_span_ids.contains(&ev.span_id),
            "spec-pair inventory {:?} should stay inside a compile span; compile spans={:?}, event_span={}",
            ev.name,
            compile_span_ids,
            ev.span_id
        );
    }
    assert_eq!(
        cap.count(&["fz", "codegen", "dispatch_missing"]),
        0,
        "simple compile should not report missing dispatches"
    );
}

// DROP: old-world CLIF IR k_* continuation body shape and capture accessor names
#[test]
fn tailcall_closure_capture_repro_emits_live_cont_body() {
    let src = r#"
fn each(_, []), do: nil
fn each(f, [h | t]) do
  f.(h)
  each(f, t)
end

fn main() do
  k = 10
  each(fn(x) -> dbg(x + k) end, [1, 2, 3])
end
"#;
    let mut t = crate::types::new();
    let graph = runtime_graph(&mut t, src);
    ir_text_record_enable();
    let _ = compile_planned(
        &mut t,
        &graph.module,
        &graph.module_plan,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("compile planned");
    let ir = ir_text_record_take();
    let names: Vec<String> = ir.iter().map(|(name, _)| name.clone()).collect();
    let cont_body = ir
        .iter()
        .find(|(name, _)| name.starts_with("k_"))
        .map(|(_, body)| body.as_str())
        .unwrap_or_else(|| panic!("expected emitted k_* body, saw {:?}", names));
    assert!(
        !cont_body.contains("trap user"),
        "k_* continuation should not compile as an unreached trap stub:\n{}",
        cont_body
    );
    assert!(
        cont_body.contains("@fz_closure_get_capture_ref")
            && cont_body.matches("call fn0").count() >= 3
            && cont_body.contains("return_call"),
        "k_* continuation should project captures through the closure env accessors:\n{}",
        cont_body
    );
}

/// `fn f([])` does NOT match a `nil` argument: `nil` falls through to
/// the `:match_error` halt. (Pre-split, `nil` and `[]` shared a
/// runtime bit pattern and this call returned 1.)
// PICKED: nil value does not match empty-list pattern — distinct types
#[test]
fn nil_does_not_match_empty_list_pattern() {
    let (halt, module) = run_main_returning_module("fn f([]), do: 1\nfn main(), do: f(nil)");
    assert_eq!(
        module.atom_names[halt as usize], "match_error",
        "expected :match_error halt; got atom id {}",
        halt,
    );
}

/// `fn f(nil)` does NOT match an `[]` argument. Symmetric to the above.
// PICKED: empty list does not match nil pattern — distinct types
#[test]
fn empty_list_does_not_match_nil_pattern() {
    let (halt, module) = run_main_returning_module("fn f(nil), do: 1\nfn main(), do: f([])");
    assert_eq!(
        module.atom_names[halt as usize], "match_error",
        "expected :match_error halt; got atom id {}",
        halt,
    );
}

// PICKED: cons pattern falls through to next clause for non-list arguments
#[test]
fn cons_function_clause_falls_through_for_non_lists_in_interp_and_native() {
    const SRC: &str = r#"
fn f([head | _tail]), do: head
fn f(_other), do: 99

fn main() do
  f([7]) + f([]) + f(%{a: 1}) + f(42)
end
"#;
    let mut t = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let frontend = compile_source_with_types(&mut t, SRC.to_string(), "cons_clause.fz".into(), &tel)
        .unwrap_or_else(|err| panic!("frontend: {:?}", err.diagnostics));
    let entry = frontend.module.fn_by_name("main").expect("main").id;

    let interp = crate::ir_interp::run_main(&tel, &frontend.module).expect("interp run");
    assert_eq!(interp, 304, "interpreter function-clause dispatch");

    let compiled = compile_planned(&mut t, &frontend.module, &frontend.module_plan, &tel).expect("compile planned");
    let image = CompiledImage::from_linked(&tel, 1, compiled);
    assert_eq!(image.run(&tel, entry), 304, "native function-clause dispatch");
}

// PICKED: recursive multi-clause function dispatches on list vs other types
#[test]
fn recursive_cons_function_clause_runs_in_interp_and_native() {
    const SRC: &str = r#"
fn count([]), do: 0
fn count([_head | tail]), do: count(tail) + 1
fn count(_value), do: 99

fn main() do
  count([1, 2]) + count([]) + count(%{a: 1}) + count(42)
end
"#;
    let mut t = crate::types::new();
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());
    let frontend = compile_source_with_types(&mut t, SRC.to_string(), "recursive_cons_clause.fz".into(), &tel)
        .unwrap_or_else(|err| panic!("frontend: {:?}", err.diagnostics));
    let entry = frontend.module.fn_by_name("main").expect("main").id;

    let interp = crate::ir_interp::run_main(&tel, &frontend.module).expect("interp run");
    assert_eq!(interp, 200, "interpreter recursive function-clause dispatch");

    let compiled = compile_planned(&mut t, &frontend.module, &frontend.module_plan, &tel).expect("compile planned");
    let image = CompiledImage::from_linked(&tel, 1, compiled);
    assert_eq!(image.run(&tel, entry), 200, "native recursive function-clause dispatch");
    assert_eq!(
        cap.count(&["fz", "codegen", "dispatch_missing"]),
        0,
        "recursive cons compile should not report missing dispatch"
    );
    let roles = planner_roles(&cap);
    assert_eq!(
        roles,
        vec!["frontend_check".to_string(), "test".to_string()],
        "frontend + interpreter + planned native compile should expose frontend and interpreter planning"
    );
    let planned_events = cap.find(&["fz", "planner", "planned"]);
    let planned = planned_events
        .iter()
        .find(|ev| {
            matches!(
                ev.metadata.get("role"),
                Some(Value::Str(role)) if role == "frontend_check"
            )
        })
        .expect("frontend planner event");
    match planned.measurements.get("activation_return_unresolved_entry_count") {
        Some(Value::U64(0)) => {}
        other => panic!("final activation inference should be complete, got {other:?}"),
    }
}

/// `dbg(nil)` and `dbg([])` render as distinct strings — codegen
/// pin for the broader fixture-driven check.
// PICKED: nil and empty list are distinct values with distinct string representations
#[test]
fn print_distinguishes_nil_from_empty_list() {
    let lines = capture_main("fn main() do\n  dbg(nil)\n  dbg([])\nend");
    assert_eq!(lines, vec!["nil".to_string(), "[]".to_string()]);
}

// Refcount + dtor on the JIT path. Mirrors the interp-leg tests in
// `ir_interp::resource_bif_tests`, but drives compile(...).run(...). The
// JIT lowers `make_resource(payload, &dwrap/1)` to an extern call into
// `fz_make_resource`, which dispatches through the `MakeResourceHook` that
// `Runtime::with_module` installs for the duration of `run_until_idle` (the
// hook takes `&Module` so the thunk can walk the dtor closure's IR body —
// see src/exec/runtime.rs).
//
// Dtor firing happens on the production task-exit drain: when a task Exits,
// the Runtime runs the MSO sweep and dispatches each surviving Resource's
// dtor closure, so the counters reflect the run by the time `run_until_idle`
// returns.

mod resource_jit_tests {
    use super::*;
    use crate::ir_interp::{
        tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset, tests_support_lock,
    };

    /// Drive `main` through the production Runtime with the module attached
    /// so `make_resource` can resolve dtor closures, and so surviving
    /// Resource dtors fire on the task-exit drain. Returns after
    /// `run_until_idle`, by which point the dtor counters reflect every
    /// Resource the run produced.
    fn run_jit_with_resources(src: &str) {
        let mut t = crate::types::new();
        let graph = runtime_graph(&mut t, src);
        let entry = graph.module.fn_by_name("main").expect("main fn").id;
        let tel = ConfiguredTelemetry::new();
        let compiled = compile_planned(&mut t, &graph.module, &graph.module_plan, &tel).expect("compile planned");
        // with_module installs the MakeResourceHook for the duration of
        // run_until_idle; the task-exit path runs the MSO sweep + dtors.
        let mut rt = Runtime::new(&compiled, 1, &tel).with_module(&graph.module);
        let _pid = rt.spawn(entry);
        rt.run_until_idle();
    }

    /// JIT-leg round trip mirroring `make_resource_bif_round_trip`
    /// from the interp leg.
    // PICKED: make_resource creates resource and fires destructor at heap drop
    #[test]
    fn make_resource_round_trip_in_jit() {
        let _g = tests_support_lock().lock().unwrap_or_else(|e| e.into_inner());
        tests_support_dtor_reset();
        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn main() do
  r = make_resource(42, &dwrap/1)
  nil
end
"#;
        run_jit_with_resources(src);
        assert_eq!(
            tests_support_dtor_fired(),
            1,
            "JIT-built resource must fire its dtor exactly once at heap drop",
        );
        assert_eq!(
            tests_support_dtor_last_payload(),
            42,
            "dtor body runs as fz code; `:: integer` marshal class unboxes \
             before the C extern, so the recorded payload is the raw int 42",
        );
    }

    /// Aliasing inside one JIT-run process still produces exactly one
    /// dtor invocation. Mirrors the interp leg's
    /// `aliasing_in_one_process_fires_dtor_once`.
    // PICKED: aliased resource fires destructor exactly once despite multiple references
    #[test]
    fn aliasing_in_one_jit_process_fires_dtor_once() {
        let _g = tests_support_lock().lock().unwrap_or_else(|e| e.into_inner());
        tests_support_dtor_reset();
        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn main() do
  r1 = make_resource(7, &dwrap/1)
  r2 = r1
  r3 = r2
  nil
end
"#;
        run_jit_with_resources(src);
        assert_eq!(
            tests_support_dtor_fired(),
            1,
            "three JIT-bound aliases of one resource must still produce one dtor call",
        );
        assert_eq!(tests_support_dtor_last_payload(), 7);
    }

    /// Two distinct `make_resource` calls each fire once. Mirrors the
    /// interp leg's `two_distinct_resources_each_fire_once`.
    // PICKED: two distinct resources each fire their destructor exactly once
    #[test]
    fn two_distinct_resources_in_jit_each_fire_once() {
        let _g = tests_support_lock().lock().unwrap_or_else(|e| e.into_inner());
        tests_support_dtor_reset();
        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn main() do
  a = make_resource(11, &dwrap/1)
  b = make_resource(22, &dwrap/1)
  nil
end
"#;
        run_jit_with_resources(src);
        assert_eq!(
            tests_support_dtor_fired(),
            2,
            "two distinct JIT-built resources must each fire their dtor exactly once",
        );
    }
}
