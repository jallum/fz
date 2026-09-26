use super::*;
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

fn test_executable(key: ExecutableKey, return_ty: Ty, nothing: ShapeId) -> BackendExecutable {
    BackendExecutable::for_test(key, return_ty, nothing)
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
    let executable = test_executable(key.clone(), int, nothing);
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
        None,
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
    let mut executable = test_executable(key.clone(), int, nothing);
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
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
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
    ))
    .unwrap();
    let dispatch = crate::compiler2::ExecutableDispatch::new(Rc::new(plan), vec![0]);
    assert_eq!(
        dispatch.plan().input_demand(),
        [DispatchDemand::TupleFields(BTreeMap::from([(
            1,
            DispatchDemand::Whole
        )]))],
        "the clause head questions its tuple parameter"
    );
    let materialized = Rc::make_mut(&mut abi.materialized);
    materialized.entry_dispatch = Some(dispatch);
    materialized.value_types.insert(result, int);
    let clauses = vec![BackendClause {
        span: Span::DUMMY,
        params: vec![param],
        projections: Vec::new(),
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
            literal: crate::ground_value::GroundValue::Int(42),
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
    let executable = Rc::new(executable);
    let mut program = BackendProgram::empty(key);
    program.add_executable(executable.clone(), world.types());
    let telemetry = NullTelemetry;
    let mut lowerer = NativeLowerer::new(&mut world, &telemetry, root, &program).expect("test native lowerer");
    let mut entry_fns = EntryFns::default();
    lowerer
        .lower_clause_dispatch_executable(0, &executable, &clauses, &entries, &mut entry_fns)
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
    let executable = test_executable(key.clone(), int, nothing);
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
        None,
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

    ctx.set_term(Term::Halt(encoded[0]));
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
