use super::*;
use crate::ast::{BinOp as AstBinOp, Expr as AstExpr, Pattern as AstPattern, Spanned};
use crate::compiler::source::Span;
use crate::dispatch_matrix::pattern::{PatternBodyId, PatternRow, SourcePatternRows};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, pattern_dispatch_from_source};
use crate::dispatch_matrix::{
    DispatchArm, DispatchEdge, DispatchGraph, DispatchMatrix, DispatchNode, EdgeEvidence, GraphNodeId, Order, Outcome,
    OutcomeId, OutcomeMultiplicity, Region, RegionPredicate, Subject, SubjectId, SubjectSource,
};
use crate::fz_ir::{CallsiteIdent, FnId, ReceiveClause, ReceiveJoinMode, Var};
use crate::ir_codegen::backend::register_runtime_symbols;
use crate::ir_codegen::runtime_syms::declare_runtime_symbols;
use crate::runtime_type_predicate::{self, ObservedSet, RuntimeTypePredicate};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::default_libcall_names;
use fz_runtime::any_value::AnyValue;
use fz_runtime::heap::{Schema, SchemaRegistry};
use fz_runtime::ir_runtime::fz_box_int_for_any;
use fz_runtime::process::Process;
use std::cell::RefCell;
use std::mem::{replace, transmute};
use std::rc::Rc;

fn make_jit() -> (JITModule, FunctionBuilderContext) {
    let isa_builder = cranelift_native::builder().expect("native isa");
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "none").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish");
    let mut builder = JITBuilder::with_isa(isa, default_libcall_names());
    // Production symbol registration — keep the test linker in lockstep with
    // the real JIT so signatures can't drift (tests use production code).
    register_runtime_symbols(&mut builder);
    (JITModule::new(builder), FunctionBuilderContext::new())
}

type ReceiveDispatchAbi = extern "C" fn(*mut Process, u64, *const AnyValueRef, *mut AnyValueRef) -> u32;

/// Stand up a fresh process for a matcher test. The caller holds the box
/// and threads `process.as_mut()` to the matcher fn (its 1st arg) and to
/// `int_ref` — exactly as production threads the process. No ambient state.
fn new_process() -> Box<Process> {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    Box::new(Process::new(schemas))
}

/// Box a scalar onto `proc`'s heap via the production BIF — same call the
/// compiled/interpreted any-boundary uses.
fn int_ref(proc: *mut Process, value: i64) -> AnyValueRef {
    let raw = fz_box_int_for_any(proc, value);
    AnyValueRef::from_raw_word(raw).expect("int ref")
}

fn struct_ref(addr: *mut u8) -> AnyValueRef {
    AnyValueRef::from_heap_object(ValueKind::STRUCT, addr.cast_const()).expect("struct ref")
}

fn empty_module() -> Module {
    let mut m = Module::default();
    m.atom_names.push("nil".into());
    m.atom_names.push("true".into());
    m.atom_names.push("false".into());
    m
}

fn sp<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn clause_meta(bound_names: Vec<&str>) -> ReceiveClause {
    ReceiveClause {
        ident: CallsiteIdent::synthetic(),
        bound_names: bound_names.into_iter().map(str::to_string).collect(),
        guard: None,
        body: FnId(0),
        join_mode: ReceiveJoinMode::OuterCont,
        span: Span::DUMMY,
    }
}

fn dispatch_from_rows(rows: Vec<(AstPattern, Option<Spanned<AstExpr>>)>) -> PatternDispatchPlan<RuntimeTypePredicate> {
    let source_patterns = SourcePatternRows {
        input_count: 1,
        rows: rows
            .into_iter()
            .enumerate()
            .map(|(i, (pattern, guard))| PatternRow {
                patterns: vec![sp(pattern)],
                preconditions: Vec::new(),
                guard,
                body_id: i as PatternBodyId,
            })
            .collect(),
    };
    pattern_dispatch_from_source(source_patterns)
        .expect("compile dispatch")
        .map_type_handle(&mut runtime_type_predicate::from_legacy_ty)
}

fn finalize_and_get(mut jmod: JITModule, fid: FuncId) -> ReceiveDispatchAbi {
    jmod.finalize_definitions().expect("finalize");
    let addr = jmod.get_finalized_function(fid);
    Box::leak(Box::new(jmod));
    unsafe { transmute(addr) }
}

fn build_dispatch_fn(
    jmod: &mut JITModule,
    fbctx: &mut FunctionBuilderContext,
    fz_module: &Module,
    tuple_schemas: &HashMap<usize, u32>,
    pinned: &[(String, Var)],
    clauses: &[ReceiveClause],
    dispatch: &PatternDispatchPlan<RuntimeTypePredicate>,
    name: &str,
) -> ReceiveDispatchAbi {
    let fid = declare_receive_dispatch(jmod, name).expect("declare receive dispatch");
    let named_schema_ids = {
        let mut reg = SchemaRegistry::new();
        let mut arities = tuple_schemas.keys().copied().collect::<Vec<_>>();
        arities.sort_unstable();
        for arity in arities {
            reg.register(Schema::tuple_of_arity(arity));
        }
        let mut ids = HashMap::new();
        let mut named = fz_module.struct_schemas.iter().collect::<Vec<_>>();
        named.sort_by_key(|(name, _)| *name);
        for (name, fields) in named {
            ids.insert(
                name.clone(),
                reg.register(Schema::named_struct(name.clone(), fields.clone())),
            );
        }
        ids
    };
    // Declare the runtime symbols from the production source so the dispatch
    // helper signatures can never drift from the real pipeline (tests use
    // production code). Mirrors the DispatchRuntimeHelpers wiring in driver.rs.
    let runtime = declare_runtime_symbols(jmod).expect("declare runtime symbols");
    emit_receive_dispatch_body(
        jmod,
        fbctx,
        fid,
        fz_module,
        tuple_schemas,
        &named_schema_ids,
        pinned,
        clauses,
        dispatch,
        &DispatchRuntimeHelpers {
            value_eq_typed_id: Some(runtime.value_eq_ref_id),
            matcher_eq_bytes_id: Some(runtime.matcher_eq_bytes_id),
            matcher_map_get_id: Some(runtime.matcher_map_get_id),
            matcher_map_get_ref_id: Some(runtime.matcher_map_get_ref_id),
            type_of_id: Some(runtime.type_of_id),
            unbox_int_id: Some(runtime.unbox_int_id),
            unbox_float_id: Some(runtime.unbox_float_id),
            unbox_atom_id: Some(runtime.unbox_atom_id),
            struct_schema_id_ref_id: Some(runtime.struct_schema_id_ref_id),
            truthy_ref_id: Some(runtime.truthy_ref_id),
            box_int_for_any_id: Some(runtime.box_int_for_any_id),
            box_float_for_any_id: Some(runtime.box_float_for_any_id),
            box_atom_for_any_id: Some(runtime.box_atom_for_any_id),
            map_is_map_id: Some(runtime.map_is_map_id),
            bs_reader_init_id: Some(runtime.bs_reader_init_ref_id),
            bs_read_field_id: Some(runtime.bs_read_field_ref_id),
            struct_get_field_id: Some(runtime.struct_get_field_id),
            list_is_cons_id: Some(runtime.list_is_cons_id),
            list_head_id: Some(runtime.list_head_fallback_id),
            list_tail_id: Some(runtime.list_tail_fallback_id),
        },
    )
    .expect("emit receive dispatch");
    finalize_and_get(replace(jmod, make_jit().0), fid)
}

fn direct_runtime_type_predicate_dispatch(
    predicate: RuntimeTypePredicate,
) -> PatternDispatchPlan<RuntimeTypePredicate> {
    PatternDispatchPlan {
        matrix: DispatchMatrix {
            subjects: vec![Subject {
                id: SubjectId(0),
                source: SubjectSource::Input { ordinal: 0 },
            }],
            outcomes: vec![Outcome {
                id: OutcomeId(0),
                multiplicity: OutcomeMultiplicity::Unique,
            }],
            arms: vec![DispatchArm {
                id: crate::dispatch_matrix::ArmId(0),
                questions: vec![],
                evidence: EdgeEvidence::empty(),
                outcome: OutcomeId(0),
            }],
            order: Order::Source,
        },
        graph: DispatchGraph {
            nodes: vec![
                DispatchNode::Test {
                    predicate: RegionPredicate::new(SubjectId(0), Region::Type(predicate)),
                    on_match: DispatchEdge::with_evidence(GraphNodeId(1), EdgeEvidence::empty()),
                    on_miss: DispatchEdge::with_evidence(GraphNodeId(2), EdgeEvidence::empty()),
                },
                DispatchNode::Outcome {
                    outcome: OutcomeId(0),
                    evidence: EdgeEvidence::empty(),
                },
                DispatchNode::Fail,
            ],
            root: GraphNodeId(0),
        },
        input_count: 1,
        subjects: vec![Some(crate::dispatch_matrix::pattern::PatternSubjectRef::Input(0))],
        outcomes: vec![crate::dispatch_matrix::pattern::PatternDispatchOutcome {
            outcome: OutcomeId(0),
            body_id: 0,
            bindings: vec![],
            span: Span::DUMMY,
        }],
        guards: vec![],
        pinned: vec![],
        prepared_keys: vec![],
        bitstring_direct_bindings: Default::default(),
    }
}

#[test]
fn cached_matcher_int_literal_hits_only_exact_tagged_value() {
    let mut process = new_process();
    let pp = process.as_mut() as *mut Process;
    let (mut jmod, mut fbctx) = make_jit();
    let m = empty_module();
    let tuple_ids = HashMap::new();
    let pinned = Vec::new();
    let clauses = vec![clause_meta(vec![])];
    let dispatch = dispatch_from_rows(vec![(AstPattern::Int(42), None)]);
    let f = build_dispatch_fn(
        &mut jmod,
        &mut fbctx,
        &m,
        &tuple_ids,
        &pinned,
        &clauses,
        &dispatch,
        "cached_matcher_int_42",
    );
    let pin: [AnyValueRef; 0] = [];
    let mut out: [AnyValueRef; 0] = [];
    assert_eq!(f(pp, int_ref(pp, 42).raw_word(), pin.as_ptr(), out.as_mut_ptr()), 1);
    assert_eq!(f(pp, int_ref(pp, 41).raw_word(), pin.as_ptr(), out.as_mut_ptr()), 0);
}

#[test]
fn cached_matcher_var_writes_input_to_out_slot_zero() {
    let mut process = new_process();
    let pp = process.as_mut() as *mut Process;
    let (mut jmod, mut fbctx) = make_jit();
    let m = empty_module();
    let tuple_ids = HashMap::new();
    let pinned = Vec::new();
    let clauses = vec![clause_meta(vec!["x"])];
    let dispatch = dispatch_from_rows(vec![(AstPattern::Var("x".into()), None)]);
    let f = build_dispatch_fn(
        &mut jmod,
        &mut fbctx,
        &m,
        &tuple_ids,
        &pinned,
        &clauses,
        &dispatch,
        "cached_matcher_var_x",
    );
    let pin: [AnyValueRef; 0] = [];
    let mut out = [AnyValueRef::null()];
    let msg = 7;
    assert_eq!(f(pp, int_ref(pp, msg).raw_word(), pin.as_ptr(), out.as_mut_ptr()), 1);
    assert_eq!(out[0].load_int().expect("out int"), msg);
}

#[test]
fn cached_matcher_guard_falls_through_when_false() {
    let mut process = new_process();
    let pp = process.as_mut() as *mut Process;
    let (mut jmod, mut fbctx) = make_jit();
    let m = empty_module();
    let tuple_ids = HashMap::new();
    let pinned = Vec::new();
    let clauses = vec![clause_meta(vec!["x"]), clause_meta(vec![])];
    let guard = sp(AstExpr::BinOp(
        AstBinOp::Gt,
        Box::new(sp(AstExpr::Var("x".into()))),
        Box::new(sp(AstExpr::Int(10))),
    ));
    let dispatch = dispatch_from_rows(vec![
        (AstPattern::Var("x".into()), Some(guard)),
        (AstPattern::Wildcard, None),
    ]);
    let f = build_dispatch_fn(
        &mut jmod,
        &mut fbctx,
        &m,
        &tuple_ids,
        &pinned,
        &clauses,
        &dispatch,
        "cached_matcher_guard_gt",
    );
    let pin: [AnyValueRef; 0] = [];
    let mut out = [AnyValueRef::null()];
    assert_eq!(f(pp, int_ref(pp, 11).raw_word(), pin.as_ptr(), out.as_mut_ptr()), 1);
    assert_eq!(out[0].load_int().expect("out int"), 11);
    assert_eq!(f(pp, int_ref(pp, 9).raw_word(), pin.as_ptr(), out.as_mut_ptr()), 2);
}

#[test]
fn cached_matcher_guard_reads_pinned_capture() {
    let mut process = new_process();
    let pp = process.as_mut() as *mut Process;
    let (mut jmod, mut fbctx) = make_jit();
    let m = empty_module();
    let tuple_ids = HashMap::new();
    let pinned = vec![("limit".to_string(), Var(0))];
    let clauses = vec![clause_meta(vec![]), clause_meta(vec![])];
    let guard = sp(AstExpr::BinOp(
        AstBinOp::Eq,
        Box::new(sp(AstExpr::Var("limit".into()))),
        Box::new(sp(AstExpr::Int(9))),
    ));
    let dispatch = dispatch_from_rows(vec![(AstPattern::Wildcard, Some(guard)), (AstPattern::Wildcard, None)]);
    let f = build_dispatch_fn(
        &mut jmod,
        &mut fbctx,
        &m,
        &tuple_ids,
        &pinned,
        &clauses,
        &dispatch,
        "cached_matcher_guard_pinned",
    );
    let mut out: [AnyValueRef; 0] = [];
    let pin_9 = [int_ref(pp, 9)];
    let pin_8 = [int_ref(pp, 8)];
    assert_eq!(f(pp, int_ref(pp, 0).raw_word(), pin_9.as_ptr(), out.as_mut_ptr()), 1);
    assert_eq!(f(pp, int_ref(pp, 0).raw_word(), pin_8.as_ptr(), out.as_mut_ptr()), 2);
}

#[test]
fn cached_matcher_tuple_with_atom_pinned_var_matches_arrived_message() {
    let (mut jmod, mut fbctx) = make_jit();
    let mut m = empty_module();
    m.atom_names.push("reply".into());

    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Box::new(Process::new(schemas));
    let pp = process.as_mut() as *mut Process;
    let tuple_schema_id = unsafe { &mut *pp }.heap.register_schema(Schema::tuple_of_arity(3));
    let mut tuple_ids = HashMap::new();
    tuple_ids.insert(3, tuple_schema_id);

    let pinned = vec![("ref".to_string(), Var(0))];
    let clauses = vec![clause_meta(vec!["v"])];
    let pat = AstPattern::Tuple(vec![
        sp(AstPattern::Atom("reply".into())),
        sp(AstPattern::Pinned("ref".into())),
        sp(AstPattern::Var("v".into())),
    ]);
    let dispatch = dispatch_from_rows(vec![(pat, None)]);
    let f = build_dispatch_fn(
        &mut jmod,
        &mut fbctx,
        &m,
        &tuple_ids,
        &pinned,
        &clauses,
        &dispatch,
        "cached_matcher_tuple_reply",
    );

    let tuple_p = unsafe { &mut *pp }.heap.alloc_struct(tuple_schema_id);
    let proc = unsafe { &mut *pp };
    proc.heap.write_field_slot(tuple_p, 0, AnyValue::atom(3));
    proc.heap.write_field_slot(tuple_p, 8, AnyValue::int(170));
    proc.heap.write_field_slot(tuple_p, 16, AnyValue::int(23));

    let pin = [int_ref(pp, 170)];
    let mut out = [AnyValueRef::null()];
    let val = struct_ref(tuple_p);
    assert_eq!(f(pp, val.raw_word(), pin.as_ptr(), out.as_mut_ptr()), 1);
    assert_eq!(out[0].load_int().expect("out int"), 23);

    let pin_other = [int_ref(pp, 255)];
    let mut out2 = [AnyValueRef::null()];
    assert_eq!(f(pp, val.raw_word(), pin_other.as_ptr(), out2.as_mut_ptr()), 0);
}

#[test]
fn cached_matcher_type_region_uses_runtime_type_predicate() {
    let mut process = new_process();
    let pp = process.as_mut() as *mut Process;
    let (mut jmod, mut fbctx) = make_jit();
    let m = empty_module();
    let tuple_ids = HashMap::new();
    let pinned = Vec::new();
    let clauses = vec![clause_meta(vec![])];
    let dispatch = direct_runtime_type_predicate_dispatch(RuntimeTypePredicate {
        ints: ObservedSet::lit(42),
        ..RuntimeTypePredicate::none()
    });
    let f = build_dispatch_fn(
        &mut jmod,
        &mut fbctx,
        &m,
        &tuple_ids,
        &pinned,
        &clauses,
        &dispatch,
        "cached_matcher_type_region_int_42",
    );
    let pin: [AnyValueRef; 0] = [];
    let mut out: [AnyValueRef; 0] = [];
    assert_eq!(f(pp, int_ref(pp, 42).raw_word(), pin.as_ptr(), out.as_mut_ptr()), 1);
    assert_eq!(f(pp, int_ref(pp, 41).raw_word(), pin.as_ptr(), out.as_mut_ptr()), 0);
}
