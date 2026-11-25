use super::*;
use crate::compiler2::drive_harness::Drive;
use crate::compiler2::identity::{ActivationKey, ExecutableKey, ExecutableNeed, FunctionId};
use crate::compiler2::pull::TransportCarrier;
use crate::compiler2::transport::{LaneDescr, TransportClass};
use crate::telemetry::sink::NullTelemetry;

#[test]
fn entry_function_references_schedule_each_recursive_helper_once() {
    let mut module = ModuleBuilder::new();
    let mut entries = EntryFns::default();
    let first = ControlEntryId::from_u32(7);
    let second = ControlEntryId::from_u32(2);
    assert!(entries.pending.is_empty());
    let first_fn = entries.reference(&mut module, first);
    assert_eq!(entries.pending.pop_front(), Some((first, first_fn)));
    let second_fn = entries.reference(&mut module, second);
    assert_eq!(entries.reference(&mut module, first), first_fn);
    assert_eq!(entries.pending.pop_front(), Some((second, second_fn)));
    assert_eq!(entries.reference(&mut module, second), second_fn);
    assert_eq!(entries.reference(&mut module, first), first_fn);
    assert!(
        entries.pending.is_empty(),
        "self and mutual references reuse emitted helpers"
    );
    assert_ne!(first_fn, second_fn);
}

fn empty_backend_program() -> BackendProgram {
    BackendProgram::empty_for_test()
}

fn encode_for_layout<T: crate::telemetry::Telemetry>(
    lowerer: &mut NativeLowerer<'_, '_, T>,
    ctx: &mut NativeFnCtx,
    executable: &BackendExecutable,
    value: &NativeBoundValue,
    shape: ShapeId,
) -> Result<Vec<Var>, FatalError> {
    encode_with_layout(lowerer, ctx, executable, value, TransportLayout::structural(shape))
}

fn encode_with_layout<T: crate::telemetry::Telemetry>(
    lowerer: &mut NativeLowerer<'_, '_, T>,
    ctx: &mut NativeFnCtx,
    executable: &BackendExecutable,
    value: &NativeBoundValue,
    layout: TransportLayout,
) -> Result<Vec<Var>, FatalError> {
    let mut encoded = Vec::new();
    lowerer.encode_transport_layout(ctx, executable, None, value, layout, &mut encoded)?;
    Ok(encoded)
}

fn defining_prim(function: &crate::fz_ir::FnIr, value: Var) -> Option<&Prim> {
    function
        .blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .find_map(|statement| match statement {
            crate::fz_ir::Stmt::Let(defined, prim) => (*defined == value).then_some(prim),
            crate::fz_ir::Stmt::LetMany(_, _) => None,
        })
}

fn tuple_shape(world: &mut World, fields: &[ShapeId]) -> ShapeId {
    world.intern_shape(ShapeDescr::Tuple(
        fields
            .iter()
            .copied()
            .map(TransportLayout::structural)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    ))
}

#[test]
fn nested_callable_adapter_preserves_the_source_lane_type_and_repr() {
    use crate::compiler2::transport::CallableDescr;

    let mut world = World::new();
    let int = world.types_mut().int();
    let any = world.types_mut().any();
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let mut nested_callable = |ty| {
        let lane = world.intern_lane(LaneDescr {
            ty,
            class: TransportClass::Value,
        });
        let scalar = world.intern_shape(ShapeDescr::Lane(lane));
        let inner = world.intern_callable(CallableDescr {
            function: Some(FunctionId::from_coordinate(1)),
            arity: 0,
            capture_layouts: Box::new([TransportLayout::structural(scalar)]),
        });
        let inner_shape = world.intern_shape(ShapeDescr::Callable(inner));
        let outer = world.intern_callable(CallableDescr {
            function: Some(FunctionId::from_coordinate(2)),
            arity: 0,
            capture_layouts: Box::new([TransportLayout::structural(inner_shape)]),
        });
        world.intern_shape(ShapeDescr::Callable(outer))
    };
    let source = nested_callable(int);
    let destination = nested_callable(any);
    let root = RootId::for_test(0);
    let key = ExecutableKey {
        activation: ActivationKey::from_inputs(root, FunctionId::from_coordinate(0), &[], world.types_mut()),
        need: ExecutableNeed::Value,
    };
    let executable = BackendExecutable::for_test(key.clone(), int, nothing);
    let program = empty_backend_program();
    let telemetry = NullTelemetry;
    let mut lowerer = NativeLowerer::new(&mut world, &telemetry, root, &program).expect("test native lowerer");
    let mut ctx = NativeFnCtx::new(
        FnId(0),
        "nested_callable_adapter",
        FnCategory::User,
        NativeBodyOrigin::Executable(key),
        NativeEntryAbi::Direct,
        vec![AbiValueRepr::RawInt],
        int,
        vec![AbiValueRepr::RawInt],
        EffectSummary::default(),
    );
    let params = ctx.entry_params(&[int]);
    let value = NativeBoundValue::Transport {
        shape: source,
        lanes: params.clone(),
    };
    let encoded = encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, destination)
        .expect("nested callable captures project through their published source layouts");

    assert_eq!(encoded, params);
    assert_eq!(ctx.param_reprs, [AbiValueRepr::RawInt]);
    assert_eq!(
        ctx.value_types.get(&params[0]),
        Some(&int),
        "a destination Any lane requires ABI boxing, not relabeling the existing raw integer"
    );
}

/// A lane-form tuple parameter is decided from its lanes.
///
/// The input arrives as a two-field tuple whose first field carries nothing
/// and whose second is one lane. Both clause-head questions -- the arity and
/// the literal in field 1 -- are answered from that form, so the entry
/// function builds no tuple and reads no field out of one. A tuple could not
/// be built here anyway: the absent field has no runtime value to put in it.
#[test]
fn entry_dispatch_decides_a_lane_form_tuple_from_its_lanes() {
    use crate::dispatch_matrix::demand::DispatchDemand;
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};
    use std::collections::BTreeMap;
    let mut world = World::new();
    let int = world.types_mut().int();
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let lane = world.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let scalar = world.intern_shape(ShapeDescr::Lane(lane));
    let tuple = tuple_shape(&mut world, &[nothing, scalar]);
    let root = RootId::for_test(0);
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "unwrap_tuple", 1);
    let activation = ActivationKey::from_inputs(root, function, &[int], world.types_mut());
    let key = ExecutableKey {
        activation,
        need: ExecutableNeed::Value,
    };
    let scalar_layout = crate::compiler2::artifact::BackendValueLayout {
        structural: scalar,
        carrier: TransportCarrier::ValueRef(lane),
        tys: Box::from([int]),
        reprs: Box::from([AbiValueRepr::ValueRef]),
    };
    let mut executable = BackendExecutable::for_test(key.clone(), int, nothing);
    let abi = Rc::make_mut(&mut executable.abi);
    abi.param_reprs = vec![AbiValueRepr::ValueRef];
    abi.return_layout.layout = scalar_layout.clone();
    let tuple_layout = crate::compiler2::artifact::BackendValueLayout {
        structural: tuple,
        carrier: TransportCarrier::Absent,
        tys: Box::from([int]),
        reprs: Box::from([AbiValueRepr::ValueRef]),
    };
    abi.semantic_inputs = Box::from([crate::compiler2::artifact::BackendSemanticInputLayout {
        semantic_index: 0,
        layout: tuple_layout.clone(),
    }]);
    let param = ValueId::from_u32(0);
    let result = ValueId::from_u32(1);
    abi.value_layouts.insert(param, tuple_layout);
    abi.value_layouts.insert(result, scalar_layout);
    let plan = pattern_dispatch_from_source(
        SourcePatternRows::lexical(
            1,
            vec![PatternRow {
                patterns: vec![crate::ast::Spanned::dummy(crate::ast::Pattern::Tuple(vec![
                    crate::ast::Spanned::dummy(crate::ast::Pattern::Wildcard),
                    crate::ast::Spanned::dummy(crate::ast::Pattern::Int(7)),
                ]))],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
        )
        .raising(crate::dispatch_matrix::pattern::LastResort::function_clause(
            None,
            "unwrap_tuple".to_string(),
            1,
        )),
    )
    .unwrap();
    // The plan the analysis hands an activation whose parameter is known to be
    // a pair: the arity question is already answered.
    let plan = plan
        .trimmed(
            &|id| match plan.graph.node(id) {
                Some(crate::dispatch_matrix::DispatchNode::Test { predicate, .. })
                    if matches!(predicate.region, crate::dispatch_matrix::Region::TupleArity(_)) =>
                {
                    crate::dispatch_matrix::LiveEdges::Match
                }
                _ => crate::dispatch_matrix::LiveEdges::Both,
            },
            &|_| false,
            &|_| false,
        )
        .expect("the arity question is settled by the parameter's shape");
    let dispatch = crate::compiler2::ExecutableDispatch::new(Rc::new(plan), vec![0]);
    assert_eq!(
        dispatch.plan().input_demand(),
        [DispatchDemand::TupleFields(BTreeMap::from([(
            1,
            DispatchDemand::Class
        )]))],
        "the clause head questions its tuple parameter; the field is only type-tested"
    );
    let materialized = Rc::make_mut(&mut abi.materialized);
    materialized.entry_dispatch = Some(dispatch);
    materialized.value_types.insert(result, int);
    let clauses = vec![BackendClause {
        span: Span::DUMMY,
        params: vec![param],
        arguments: Box::default(),
        entry: ControlEntryId::from_u32(0),
    }];
    let entries = vec![BackendEntry {
        span: Span::DUMMY,
        origin: crate::compiler2::BackendEntryOrigin::Clause,
        params: Vec::new(),
        captures: Vec::new(),
        physical_captures: Vec::new(),
        physical_params: Vec::new(),
        steps: vec![BackendStep::Const {
            value: result,
            literal: crate::ground_value::GroundValue::Int(42).into(),
        }],
        tail: BackendTail::Value {
            value: result,
            dest: ControlDestination::Return,
        },
    }];
    executable.body = BackendBody::Clauses {
        clauses: clauses.clone(),
        entries: entries.clone(),
        generated: Vec::new(),
    };
    // A pair whose second field is not 7 raises, so the executable names the
    // atoms the raised struct's fields write among its atoms.
    let raised = executable
        .abi
        .materialized
        .entry_dispatch
        .as_ref()
        .and_then(|dispatch| dispatch.plan().last_resort.as_ref())
        .expect("the clause head raises when nothing matches");
    executable.atom_names = raised.atoms().chain(["nil", "true"]).map(AtomName::from).collect();
    let raised = raised.exception().expect("the clause head raises an exception");
    let raised = fz_runtime::module_name::ModuleName::from_atom_name(raised).expect("an exception's module");
    let executable = Rc::new(executable);
    let mut program = BackendProgram::empty(key);
    // The program carries the struct the clause head raises, as declared by
    // `FunctionClauseError`.
    let declared = [
        "__exception__",
        "module",
        "function",
        "arity",
        "kind",
        "args",
        "clauses",
    ];
    let unset = crate::literal_term::LiteralTerm::Ground(crate::ground_value::GroundValue::Nil);
    let marked = crate::literal_term::LiteralTerm::Ground(crate::ground_value::GroundValue::Bool(true));
    let mut defaults = vec![unset; declared.len()];
    defaults[0] = marked;
    let module = world.reference_module(raised.clone());
    program.replace_schema(
        module,
        Some(Rc::new(crate::compiler2::backend_program::BackendSchema {
            module,
            name: Rc::new(raised),
            fields: Rc::new(declared.map(str::to_string).to_vec()),
            defaults: Rc::new(defaults),
        })),
    );
    program.add_executable(executable.clone(), world.types());
    let telemetry = NullTelemetry;
    let mut lowerer = NativeLowerer::new(&mut world, &telemetry, root, &program).expect("test native lowerer");
    let mut entry_fns = EntryFns::default();
    lowerer
        .lower_executable_head(0, &executable, &clauses, &entries, &mut entry_fns)
        .expect("a lane-form tuple parameter is decided without being boxed");
    let module = lowerer.module.build();
    let entry = module
        .fns
        .iter()
        .find(|function| function.name.contains("__e"))
        .expect("the dispatch entry function");
    assert!(
        entry
            .blocks
            .iter()
            .flat_map(|block| &block.stmts)
            .all(|statement| !matches!(
                statement,
                crate::fz_ir::Stmt::Let(_, Prim::MakeTuple(_) | Prim::TupleField(_, _))
            )),
        "the entry decides its tuple parameter from the lanes it already holds"
    );
}

#[test]
fn tuple_encoding_reprojects_same_arity_partial_transport_by_position() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let inner_tuple_ty = world.types_mut().tuple(&[int, int, int]);
    let outer_tuple_ty = world.types_mut().tuple(&[int, inner_tuple_ty]);
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let lane = world.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let scalar = world.intern_shape(ShapeDescr::Lane(lane));
    let inner_tuple_lane = world.intern_lane(LaneDescr {
        ty: inner_tuple_ty,
        class: TransportClass::Value,
    });
    let inner_tuple_value = world.intern_shape(ShapeDescr::Lane(inner_tuple_lane));
    let outer_tuple_lane = world.intern_lane(LaneDescr {
        ty: outer_tuple_ty,
        class: TransportClass::Value,
    });
    let source_inner = tuple_shape(&mut world, &[scalar, scalar, scalar]);
    let source = tuple_shape(&mut world, &[nothing, source_inner]);
    let destination = tuple_shape(&mut world, &[nothing, inner_tuple_value]);
    let selective_inner = tuple_shape(&mut world, &[nothing, scalar, nothing]);
    let selective_destination = tuple_shape(&mut world, &[nothing, selective_inner]);
    let source_with_present_discard = tuple_shape(&mut world, &[scalar, source_inner]);
    let required_absent_destination = tuple_shape(&mut world, &[scalar, nothing]);
    let arity_mismatch_destination = tuple_shape(&mut world, &[scalar]);
    let root = RootId::for_test(0);
    let function = FunctionId::from_coordinate(0);
    let activation = ActivationKey::from_inputs(root, function, &[], world.types_mut());
    let key = ExecutableKey {
        activation,
        need: ExecutableNeed::Value,
    };
    let executable = BackendExecutable::for_test(key.clone(), int, nothing);
    let program = empty_backend_program();
    let telemetry = NullTelemetry;
    let mut lowerer = NativeLowerer::new(&mut world, &telemetry, root, &program).expect("test native lowerer");
    let mut ctx = NativeFnCtx::new(
        FnId(0),
        "tuple_reprojection",
        FnCategory::User,
        NativeBodyOrigin::Executable(key),
        NativeEntryAbi::Direct,
        Vec::new(),
        int,
        vec![AbiValueRepr::ValueRef],
        EffectSummary::default(),
    );
    let params = ctx.entry_params(&[int, int, int]);
    let value = NativeBoundValue::Transport {
        shape: source,
        lanes: params.clone(),
    };
    let encoded = encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, destination)
        .expect("the destination erases the absent field before encoding the required inner tuple");

    assert_eq!(encoded.len(), 1);

    let selectively_encoded = encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, selective_destination)
        .expect("a second consumer should independently select one nested source field");
    assert_eq!(selectively_encoded, vec![params[1]]);

    let (present_tag, _) = ctx.emit_let(Prim::Const(Const::Int(99)));
    let value_with_present_discard = NativeBoundValue::Transport {
        shape: source_with_present_discard,
        lanes: std::iter::once(present_tag).chain(params.iter().copied()).collect(),
    };
    let present_discarded = encode_for_layout(
        &mut lowerer,
        &mut ctx,
        &executable,
        &value_with_present_discard,
        destination,
    )
    .expect("destination Nothing should discard a present source field");
    assert_eq!(present_discarded.len(), 1);

    let whole_carrier = encode_with_layout(
        &mut lowerer,
        &mut ctx,
        &executable,
        &value_with_present_discard,
        TransportLayout {
            structural: source_with_present_discard,
            carrier: TransportCarrier::ValueRef(outer_tuple_lane),
        },
    )
    .expect("a whole tuple should satisfy an outer ValueRef carrier");
    assert_eq!(whole_carrier.len(), 1);
    assert!(
        encode_with_layout(
            &mut lowerer,
            &mut ctx,
            &executable,
            &value,
            TransportLayout {
                structural: destination,
                carrier: TransportCarrier::ValueRef(outer_tuple_lane),
            },
        )
        .is_err(),
        "same-arity reprojection must not bypass an outer ValueRef obligation",
    );

    assert!(
        encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, required_absent_destination,).is_err(),
        "a required destination field cannot be invented from an absent source field",
    );
    assert!(
        encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, arity_mismatch_destination,).is_err(),
        "arity-mismatched tuples retain outer materialization behavior",
    );
    assert!(
        lowerer
            .encode_runtime_value(&mut ctx, &executable, None, &value, scalar, &mut Vec::new())
            .is_err(),
        "non-tuple destinations retain outer materialization behavior",
    );

    let mut identical = Vec::new();
    lowerer
        .encode_runtime_value(&mut ctx, &executable, None, &value, source, &mut identical)
        .expect("an identical layout keeps the direct lane-copy path");
    assert_eq!(identical, params);

    ctx.set_term(Term::Return(encoded[0]));
    let (function, body) = ctx.finish();
    assert_eq!(body.value_types.get(&encoded[0]), Some(&inner_tuple_ty));
    assert_eq!(body.value_types.get(&present_discarded[0]), Some(&inner_tuple_ty));
    assert!(
        matches!(defining_prim(&function, encoded[0]), Some(Prim::MakeTuple(items)) if items == &params),
        "the absent-tag consumer should build only the required inner tuple",
    );
    assert!(
        matches!(defining_prim(&function, present_discarded[0]), Some(Prim::MakeTuple(items)) if items == &params),
        "the present-tag consumer should discard the tag before building the inner tuple",
    );
    assert!(
        matches!(defining_prim(&function, whole_carrier[0]), Some(Prim::MakeTuple(items)) if items.len() == 2 && items[0] == present_tag),
        "the explicit whole carrier should build one outer tuple value",
    );
    assert!(
        function
            .blocks
            .iter()
            .flat_map(|block| &block.stmts)
            .all(|statement| { !matches!(statement, crate::fz_ir::Stmt::Let(_, Prim::TupleField(_, _))) })
    );
}

/// An entry that only its own function's direct transfers reach is a block of
/// that function: native emits no function for a branch arm or for a join, and
/// control reaches each by `Goto`. A join two arms deliver to is one block with
/// two incoming transfers.
#[test]
fn entries_reached_only_by_their_functions_direct_transfers_are_blocks() {
    use crate::compiler2::drive_harness::NativeProgramCapture;
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};
    use crate::telemetry::ConfiguredTelemetry;
    use std::collections::BTreeSet;

    let source = "\
def pick(x) do
  sign = if x > 0 do
    :pos
  else
    :neg
  end
  pair = case x do
    n -> {n, sign}
  end
  dbg(pair)
end

def main(), do: pick(3)
";
    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("entry_blocks.fz".into()),
        text: source.into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, crate::compiler2::dump::DumpStage::Native)
        .expect("native product should settle");
    let program = native.last(root).program;
    let names = program
        .module
        .fns
        .iter()
        .map(|function| function.name.as_str())
        .collect::<Vec<_>>();
    assert!(
        names.iter().all(|name| !name.contains("__branch_")),
        "an arm is reached only from its own function, so it is never a function of its own: {names:?}"
    );
    let pick = names
        .iter()
        .filter(|name| name.starts_with("pick__"))
        .map(|name| name.split_once("__e").expect("executable-named").1)
        .map(|rest| rest.split_once("__").map_or("", |(_, suffix)| suffix))
        .collect::<BTreeSet<_>>();
    // `x > 0` is an extern the entry calls itself, so the entry that resumes
    // after it is a block of the entry's function. e3 is the join both `if`
    // arms deliver to; the `case` arm and the join only that arm delivers to
    // follow it. All of `pick` is one function.
    assert_eq!(
        pick,
        BTreeSet::from([""]),
        "pick lowers to one function holding its join and its arms: {names:?}"
    );
    let pick_fn = program
        .module
        .fns
        .iter()
        .find(|function| function.name.starts_with("pick__"))
        .expect("pick lowers to a function");
    let predecessors = |target: crate::fz_ir::BlockId| {
        pick_fn
            .blocks
            .iter()
            .filter(|block| matches!(&block.terminator, Term::Goto(to, _) if *to == target))
            .count()
    };
    assert!(
        pick_fn.blocks.iter().any(|block| predecessors(block.id) == 2),
        "the join both `if` arms deliver to is one block with two incoming Gotos"
    );
}

fn native_fn_names(program: &crate::compiler2::artifact::NativeProgram) -> Vec<&str> {
    program
        .module
        .fns
        .iter()
        .map(|function| function.name.as_str())
        .collect()
}

fn fns_of_executable<'p>(
    program: &'p crate::compiler2::artifact::NativeProgram,
    function: &str,
) -> Vec<&'p crate::fz_ir::FnIr> {
    let prefix = format!("{function}__e");
    program
        .module
        .fns
        .iter()
        .filter(|candidate| {
            candidate
                .name
                .strip_prefix(&prefix)
                .is_some_and(|rest| rest.starts_with(|c: char| c.is_ascii_digit()))
        })
        .collect()
}

/// `P.f` adds in a position that is not its tail and `P.g` multiplies in one.
/// Kernel's `+` and `*` are each a clause that only calls an extern, so each
/// is frame-free and lowered in its caller: each caller is one function that
/// calls the extern itself, with no call and no function for the entry that
/// goes on after it.
#[test]
fn a_delivered_call_to_a_forwarder_of_an_extern_is_the_extern_inline_in_its_caller() {
    let settled = Drive::fixture(1177).dump_stage(crate::compiler2::dump::DumpStage::Native);
    let program = settled.native_program();
    let names = native_fn_names(&program);
    for caller in ["f", "g"] {
        let fns = fns_of_executable(&program, caller);
        let [function] = fns.as_slice() else {
            panic!("{caller} is one function, with no resume function of its own: {names:?}");
        };
        assert!(
            makes_no_call(function),
            "{caller} reaches its extern without a call and its continuation"
        );
        let calls_extern = function.blocks.iter().flat_map(|block| &block.stmts).any(|stmt| {
            matches!(
                stmt,
                crate::fz_ir::Stmt::Let(_, Prim::Extern(..)) | crate::fz_ir::Stmt::LetMany(_, Prim::Extern(..))
            )
        });
        assert!(calls_extern, "{caller} calls its extern inline");
    }
}

/// `Loop.frame_free` calls `Callee.classify/1`, which has three clauses, an
/// `if` and a call of its own, and can suspend nothing. The loop is then one
/// function: classify's clauses and its call to `half/1` are blocks of it, and
/// it makes no call and has no function for the entry that goes on after the
/// call.
#[test]
fn a_delivered_call_to_a_frame_free_callee_is_lowered_as_blocks_of_its_caller() {
    let settled = Drive::fixture(1880).dump_stage(crate::compiler2::dump::DumpStage::Native);
    let program = settled.native_program();
    let fns = fns_of_executable(&program, "frame_free");
    let [function] = fns.as_slice() else {
        panic!(
            "the loop is one function, with no resume function: {:?}",
            native_fn_names(&program)
        );
    };
    assert!(
        makes_no_call(function),
        "the loop reaches classify/1 and half/1 without a call"
    );
}

/// A callee in a call cycle, one that enters a `try` or a `receive`, and a
/// closure each can be left and returned to by something outside the loop, so
/// each loop's call keeps its continuation and the entry after it is a
/// function of its own.
#[test]
fn a_delivered_call_to_a_callee_that_needs_a_frame_keeps_its_continuation() {
    let settled = Drive::fixture(1880).dump_stage(crate::compiler2::dump::DumpStage::Native);
    let program = settled.native_program();
    for caller in ["cycle", "tried", "received", "closure"] {
        let fns = fns_of_executable(&program, caller);
        assert!(
            fns.iter().any(|function| function.name.contains("__resume_")),
            "{caller}'s call resumes in a function of its own: {:?}",
            native_fn_names(&program)
        );
        assert!(
            fns.iter().any(|function| !makes_no_call(function)),
            "{caller} calls its callee with a continuation"
        );
    }
}

fn makes_no_call(function: &crate::fz_ir::FnIr) -> bool {
    function
        .blocks
        .iter()
        .all(|block| !matches!(block.terminator, Term::Call { .. } | Term::CallClosure { .. }))
}
/// How many times the functions of `function` test a value for being `true`
/// or `false`, which is how a guard checks that an operand is a boolean.
fn boolean_tests(program: &crate::compiler2::artifact::NativeProgram, function: &str) -> usize {
    fns_of_executable(program, function)
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.stmts)
        .filter(|stmt| {
            matches!(
                stmt,
                crate::fz_ir::Stmt::Let(_, Prim::BinOp(crate::fz_ir::BinOp::Identical, _, _))
            )
        })
        .count()
}

/// A comparison, a type test and an `and`, `or` or `not` all answer with a
/// boolean, so a guard built only from them checks none of its operands.
/// `flagged/2` takes an operand that may be `:maybe`, and checks that one.
#[test]
fn a_guard_tests_an_operand_for_being_a_boolean_only_when_its_type_leaves_it_open() {
    let settled = Drive::fixture(1374).dump_stage(crate::compiler2::dump::DumpStage::Native);
    let program = settled.native_program();
    assert_eq!(
        boolean_tests(&program, "class"),
        0,
        "every operand in class/1 is already a boolean"
    );
    assert_eq!(
        boolean_tests(&program, "flagged"),
        2,
        "flagged/2 compares its open operand with true and with false, once"
    );
}

/// The native program lowered for `source`'s `main`.
fn native_program_of(source: &str) -> Rc<crate::compiler2::NativeProgram> {
    use crate::compiler2::drive_harness::NativeProgramCapture;
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};
    use crate::telemetry::ConfiguredTelemetry;

    let tel = ConfiguredTelemetry::new();
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("native_functions.fz".into()),
        text: source.into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, crate::compiler2::dump::DumpStage::Native)
        .expect("native product should settle");
    native.last(root).program
}

fn native_function_names(source: &str) -> Vec<String> {
    let program = native_program_of(source);
    program
        .module
        .fns
        .iter()
        .map(|function| function.name.clone())
        .collect()
}

/// A clause body is reached only from its function's dispatch, so a function
/// of several clauses is one machine function, and a walk that calls itself
/// from its first clause is that one function and nothing else.
#[test]
fn a_function_of_several_clauses_is_one_function_and_its_self_tail_call_makes_no_other() {
    let names = native_function_names(
        "\
def walk(<<c, rest :: binary>>, acc) when c < 128, do: walk(rest, acc + c)
def walk(_bytes, acc), do: acc

def main(), do: dbg(walk(\"hello\", 0))
",
    );
    let walk = names
        .iter()
        .filter(|name| name.starts_with("walk__"))
        .collect::<Vec<_>>();
    assert_eq!(
        walk.len(),
        1,
        "both clauses of walk are blocks of its one function: {names:?}"
    );
    assert!(
        names.iter().all(|name| !name.contains("__clause_")),
        "no clause is a function of its own: {names:?}"
    );
}

/// A tail call to the function being compiled is the one loop inside a
/// function, so the function holds a tail call to itself.
#[test]
fn a_self_tail_call_stays_in_its_function() {
    let program = native_program_of(
        "\
def count(0, acc), do: acc
def count(n, acc), do: count(n - 1, acc + n)

def main(), do: dbg(count(10, 0))
",
    );
    let count = program
        .module
        .fns
        .iter()
        .find(|function| function.name.starts_with("count__"))
        .expect("count lowers to a function");
    assert!(
        count.blocks.iter().any(|block| matches!(
            &block.terminator,
            Term::TailCall { callee, is_back_edge: true, .. } if callee.local_fn_id() == Some(count.id)
        )),
        "count's second clause tail-calls count itself, marked as the back edge that charges a reduction"
    );
}

/// The function that pushes a try's handler record enters the body itself, so
/// the body is a block of it. Only a raise, which the runtime delivers, reaches
/// the handler, so the handler is the one function a try adds.
#[test]
fn a_try_body_is_a_block_and_its_handler_is_the_only_function_the_try_adds() {
    let names = native_function_names(
        "\
def guarded(n) do
  try do
    n * 3
  rescue
    _ -> 0
  end
end

def main(), do: dbg(guarded(2))
",
    );
    let of_guarded = |marker: &str| {
        names
            .iter()
            .filter(|name| name.starts_with("guarded__") && name.contains(marker))
            .count()
    };
    assert_eq!(of_guarded("__handler"), 1, "the handler is a function: {names:?}");
    assert_eq!(of_guarded("__branch"), 0, "the body is a block of guarded: {names:?}");
}

/// Two appends whose left operand the function still reads after the call:
/// one result feeds a tail call, the other is delivered into a tuple.
const RETAINED_APPEND_SOURCE: &str = "\
defmodule M do
  def into_tail_call(acc, x), do: pair(acc <> x, acc)
  def delivered(acc, x) do
    longer = acc <> x
    {acc, longer}
  end
  def pair(a, b), do: {a, b}
end

def main() do
  {M.into_tail_call(\"ab\", \"c\"), M.delivered(\"ab\", \"c\")}
end
";

const PASSED_TWICE_SOURCE: &str = "\
defmodule M do
  def loop(0, kept, _last), do: kept
  def loop(n, kept, _last), do: loop(n - 1, kept, kept)
end

def main() do
  M.loop(3, {\"a\", \"b\", \"c\"}, {\"d\", \"e\", \"f\"})
end
";

#[test]
fn a_value_passed_twice_in_one_call_is_shared_once() {
    let program = native_program_of(PASSED_TWICE_SOURCE);
    let fns = fns_of_executable(&program, "loop");
    let origin = block_param_origins(&fns);
    let mut shares: HashMap<crate::fz_ir::Var, usize> = HashMap::default();
    for function in &fns {
        for block in &function.blocks {
            for stmt in &block.stmts {
                if let crate::fz_ir::Stmt::Let(_, Prim::Share(value)) = stmt {
                    *shares.entry(origin(*value)).or_default() += 1;
                }
            }
        }
    }
    assert!(
        !shares.is_empty(),
        "the kept tuple is shared before the call that passes it twice"
    );
    assert!(
        shares.values().all(|count| *count == 1),
        "a mark once set is never cleared, so each value is shared once per call: {shares:?}"
    );
}

/// The value each variable of `fns` names, found by following a block
/// parameter back through the jumps that pass it along; a block that more
/// than one jump enters keeps its parameters as their own values.
fn block_param_origins(fns: &[&crate::fz_ir::FnIr]) -> impl Fn(crate::fz_ir::Var) -> crate::fz_ir::Var {
    let mut passed: HashMap<crate::fz_ir::Var, Vec<crate::fz_ir::Var>> = HashMap::default();
    for function in fns {
        for block in &function.blocks {
            if let crate::fz_ir::Term::Goto(target, args) = &block.terminator {
                let target = function
                    .blocks
                    .iter()
                    .find(|candidate| candidate.id == *target)
                    .expect("a jump's block");
                for (param, arg) in target.params.iter().zip(args) {
                    passed.entry(*param).or_default().push(*arg);
                }
            }
        }
    }
    move |mut var| {
        while let Some([from]) = passed.get(&var).map(Vec::as_slice) {
            var = *from;
        }
        var
    }
}

/// `<>` may write past its left operand's last byte when nothing else holds
/// it, so a left operand the caller reads again must be shared before the
/// call that appends to it. The append is an extern inline in its caller, and
/// a share of the extern's left operand comes ahead of it.
#[test]
fn an_append_whose_left_operand_is_read_again_shares_it_before_the_append() {
    let program = native_program_of(RETAINED_APPEND_SOURCE);
    for caller in ["into_tail_call", "delivered"] {
        let fns = fns_of_executable(&program, caller);
        let stmts: Vec<&crate::fz_ir::Stmt> = fns
            .iter()
            .flat_map(|function| function.blocks.iter().flat_map(|block| &block.stmts))
            .collect();
        let origin = block_param_origins(&fns);
        let shared_before_its_append = stmts.iter().enumerate().any(|(appended_at, stmt)| {
            let crate::fz_ir::Stmt::Let(_, Prim::Extern(_, _, args)) = stmt else {
                return false;
            };
            let Some(left) = args.first().map(|arg| origin(arg.var)) else {
                return false;
            };
            stmts[..appended_at].iter().any(
                |earlier| matches!(earlier, crate::fz_ir::Stmt::Let(_, Prim::Share(value)) if origin(*value) == left),
            )
        });
        assert!(
            shared_before_its_append,
            "{caller}: an append's left operand is shared before the append"
        );
    }
}

/// What `lane_form_type_test` asked of a cursor: the answer, and the prims the
/// question put into the function.
fn ask_a_cursor(predicate: &RuntimeTypePredicate) -> (bool, Option<bool>, Vec<Prim>) {
    let mut world = World::new();
    let int = world.types_mut().int();
    let any = world.types_mut().any();
    let cursor = world.binary_cursor_shape();
    let root = RootId::for_test(0);
    let program = empty_backend_program();
    let telemetry = NullTelemetry;
    let mut lowerer = NativeLowerer::new(&mut world, &telemetry, root, &program).expect("test native lowerer");
    let mut ctx = NativeFnCtx::new(
        FnId(0),
        "cursor_type_test",
        FnCategory::User,
        NativeBodyOrigin::Executable(ExecutableKey {
            activation: ActivationKey::from_inputs(
                root,
                FunctionId::from_coordinate(0),
                &[],
                lowerer.world.types_mut(),
            ),
            need: ExecutableNeed::Value,
        }),
        NativeEntryAbi::Direct,
        vec![AbiValueRepr::ValueRef, AbiValueRepr::RawInt],
        int,
        vec![AbiValueRepr::ValueRef, AbiValueRepr::RawInt],
        EffectSummary::default(),
    );
    let lanes = ctx.entry_params(&[any, int]);
    let value = NativeBoundValue::Transport { shape: cursor, lanes };
    let answer = lowerer
        .lane_form_type_test(&mut ctx, &value, predicate)
        .expect("a cursor is a bitstring and answers a type test from its lanes");
    let (settled, runtime) = match answer {
        DispatchAnswer::Static(admitted) => (Some(admitted), false),
        DispatchAnswer::Runtime(_) => (None, true),
    };
    let ir = ctx.builder.build();
    let prims = ir
        .blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .filter_map(|stmt| match stmt {
            crate::fz_ir::Stmt::Let(_, prim) => Some(prim.clone()),
            _ => None,
        })
        .collect();
    (runtime, settled, prims)
}

fn bitstring_predicate(admitted: crate::runtime_type_predicate::BitstringAlignment) -> RuntimeTypePredicate {
    let mut predicate = RuntimeTypePredicate::none();
    predicate.bitstrings = admitted;
    predicate
}

/// A cursor stands for a bitstring, so a predicate that admits none answers
/// no and one that admits every length answers yes, with nothing read.
#[test]
fn a_cursor_answers_a_predicate_that_ignores_its_length_without_reading_it() {
    use crate::runtime_type_predicate::BitstringAlignment;
    for (predicate, admitted) in [
        (RuntimeTypePredicate::none(), false),
        (bitstring_predicate(BitstringAlignment::NONE), false),
        (bitstring_predicate(BitstringAlignment::ANY), true),
    ] {
        let (runtime, settled, prims) = ask_a_cursor(&predicate);
        assert!(!runtime);
        assert_eq!(settled, Some(admitted));
        assert!(prims.is_empty(), "a settled answer emits nothing: {prims:?}");
    }
}

/// A predicate that asks whether the bits remaining are whole bytes is
/// answered from the source's header and the position: the length is read
/// once, one fit question is asked of it, and no suffix is built.
#[test]
fn a_cursor_answers_a_length_question_from_its_lanes_without_being_built() {
    use crate::runtime_type_predicate::BitstringAlignment;
    for (alignment, negated) in [
        (BitstringAlignment::WHOLE_BYTES, false),
        (BitstringAlignment::PARTIAL_BYTE, true),
    ] {
        let (runtime, _, prims) = ask_a_cursor(&bitstring_predicate(alignment));
        assert!(runtime);
        let count = |is: fn(&Prim) -> bool| prims.iter().filter(|prim| is(prim)).count();
        assert_eq!(count(|p| matches!(p, Prim::BinaryBitLen(_))), 1, "{prims:?}");
        assert_eq!(count(|p| matches!(p, Prim::BitFieldFits { .. })), 1, "{prims:?}");
        assert_eq!(
            count(|p| matches!(p, Prim::UnOp(crate::fz_ir::UnOp::Not, _))),
            usize::from(negated),
            "{prims:?}"
        );
        assert_eq!(
            count(|p| matches!(p, Prim::BitReadField { .. } | Prim::RuntimeTypeTest(..))),
            0,
            "{prims:?}"
        );
    }
}
