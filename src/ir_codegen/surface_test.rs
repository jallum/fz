use super::*;
use crate::diag::Diagnostics;
use crate::frontend::spec_registry::SpecRegistry;
use crate::fz_ir::{Block, BlockId, Const, FnCategory, FnId, FnIr, Module, Prim, Stmt, Term, Var};
use crate::ir_codegen::{JitBackend, driver};
use crate::ir_planner::{SpecPlan, fn_types::SpecKey};
use crate::telemetry::ConfiguredTelemetry;
use std::collections::{BTreeMap, HashMap, HashSet};

#[test]
fn compile_with_backend_surface_jit_compiles_a_trivial_native_body_without_planner_prepare() {
    let tel = ConfiguredTelemetry::new();
    let mut t = crate::types::new();
    let int = t.int();
    let fn_id = FnId(0);
    let key = SpecKey::value(fn_id, vec![]);

    let body = FnIr {
        id: fn_id,
        name: "main".to_string(),
        frame_schema_id: 0,
        blocks: vec![Block {
            id: BlockId(0),
            params: Vec::new(),
            stmts: vec![Stmt::Let(Var(0), Prim::Const(Const::Int(42)))],
            terminator: Term::Return(Var(0)),
        }],
        entry: BlockId(0),
        category: FnCategory::User,
        owner_module: String::new(),
        ignored_entry_params: Vec::new(),
        physical_entry_params: Vec::new(),
        physical_capabilities: Vec::new(),
    };

    let mut module = Module::default();
    module.fns.push(body);
    module.fn_idx.insert(fn_id, 0);

    let mut plan = SpecPlan::default();
    plan.vars.insert(Var(0), int.clone());
    plan.reachable_blocks.insert(BlockId(0));
    let mut body_registry = SpecRegistry::new();
    let _ = body_registry.register_spec_key_with_precedence(&t, key.clone(), 0);

    let surface = NativeCodegenSurface {
        module: &module,
        diagnostics: Diagnostics::new(),
        main_fn_id: Some(fn_id),
        body_slots: vec![Some(NativeCodegenBody {
            codegen_id: 0,
            fn_idx: 0,
            fn_id,
            spec_key: key,
            spec_plan: plan,
            native_body: None,
            body: &module.fns[0],
            display_name: "main".to_string(),
            reachable: true,
        })],
        body_registry,
        callable_entries: BTreeMap::new(),
        mid_flight_cont_keys: Vec::new(),
        return_tys: vec![int],
        param_reprs: vec![Vec::new()],
        return_reprs: vec![ArgRepr::RawInt],
        native_abi_fns: HashSet::from([fn_id]),
        cont_target_fns: HashSet::new(),
        cont_fns: HashSet::new(),
        closure_capture_counts: HashMap::new(),
        cont_extras_count: HashMap::new(),
        fn_halt_kinds: HashMap::from([(fn_id.0, ArgRepr::RawInt.halt_kind())]),
    };

    let compiled = driver::compile_with_backend_surface(&mut t, &surface, JitBackend::new(), &tel)
        .expect("shared native backend should accept a codegen surface without planner preparation");

    assert!(
        compiled.fn_ptr(fn_id).is_some(),
        "shared native codegen should publish a JIT body for the surface entry without prepare_preplanned_native",
    );
    assert_eq!(
        compiled.run(&tel, fn_id),
        42,
        "the surface-compiled native body should execute through the shared JIT path",
    );
}
