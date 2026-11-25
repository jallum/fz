use super::*;

fn dispatch_projection(world: &mut World, ty: Ty) -> RuntimeDemand {
    let any = world.types_mut().any();
    let mut builder = RuntimeDemandTypeBuilder::new(any);
    prepare_type_projection(world, &mut builder, ty);
    builder.dispatch_demand(ty)
}

/// A value that dispatch reads must stay in the executable ABI, so reading an
/// empty tuple, or a tuple of empty tuples, is never an ignored input.
#[test]
fn a_dispatch_read_of_a_zero_width_tuple_is_present() {
    let mut world = World::new();
    let empty = world.types_mut().tuple(&[]);
    let nested = world.types_mut().tuple(&[empty]);
    assert_eq!(dispatch_projection(&mut world, empty), RuntimeDemand::whole());
    assert!(!dispatch_projection(&mut world, nested).is_ignore());
}

/// A tuple whose first field may be a callable or an integer and whose second
/// is always a callable: a consumer that calls both fields needs the first
/// boxed, so a type test can tell it from an integer, and the second direct.
#[test]
fn a_callable_that_shares_its_position_with_an_integer_is_boxed() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let callable = world.types_mut().arrow(&[int], int);
    let maybe_callable = world.types_mut().union(callable, int);
    let pair = world.types_mut().tuple(&[maybe_callable, callable]);
    let any = world.types_mut().any();
    let mut builder = RuntimeDemandTypeBuilder::new(any);
    prepare_type_projection(&mut world, &mut builder, pair);

    let called = || RuntimeDemand::callable(CallableDemand::opaque());
    let mut demand = RuntimeDemand::tuple_fields(vec![called(), called()]);
    read_against_type(&builder.projections, &mut demand, pair);

    let ShapeDemand::TupleFields(fields) = &demand.shape else {
        panic!("the pair is still read field by field: {demand:?}");
    };
    assert!(
        fields[0].callable.escape,
        "the field that may be an integer travels boxed: {demand:?}"
    );
    assert!(
        !fields[1].callable.escape,
        "the field that is always a callable stays direct: {demand:?}"
    );
}

/// A value that is not one exact tuple travels as one built value, which has
/// every field, so a reader that asks for some of its fields asks for all of
/// it: a union of tuples of two arities, and a tuple that may be `nil`.
#[test]
fn a_field_reading_of_a_value_that_is_not_one_exact_tuple_reads_it_whole() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let nil = world.types_mut().atom_lit("nil");
    let pair = world.types_mut().tuple(&[int, int]);
    let triple = world.types_mut().tuple(&[int, int, int]);
    let pair_or_triple = world.types_mut().union(pair, triple);
    let maybe_pair = world.types_mut().union(pair, nil);
    let any = world.types_mut().any();
    let mut builder = RuntimeDemandTypeBuilder::new(any);
    let first_and_third = || {
        RuntimeDemand::tuple_fields(vec![
            RuntimeDemand::whole(),
            RuntimeDemand::ignore(),
            RuntimeDemand::whole(),
        ])
    };
    for ty in [pair_or_triple, maybe_pair] {
        prepare_type_projection(&mut world, &mut builder, ty);
        let mut demand = first_and_third();
        read_against_type(&builder.projections, &mut demand, ty);
        assert_eq!(demand, RuntimeDemand::whole(), "{}", world.types().display(&ty));
    }

    prepare_type_projection(&mut world, &mut builder, triple);
    let mut demand = first_and_third();
    read_against_type(&builder.projections, &mut demand, triple);
    assert_eq!(demand, first_and_third(), "an exact tuple keeps its field reading");
}

/// A tuple with a wide field keeps its per-field demand.
#[test]
fn a_dispatch_read_of_a_wide_tuple_keeps_its_field_demands() {
    let mut world = World::new();
    let one = world.types_mut().int_lit(1);
    let tuple = world.types_mut().tuple(&[one]);
    let demand = dispatch_projection(&mut world, tuple);
    assert!(!demand.is_ignore());
    assert_ne!(demand, RuntimeDemand::whole());
}

/// Building a body's value tables and its value origins reads each value by
/// its number in the body: no value id is ever hashed.
#[test]
fn a_bodys_value_tables_are_built_without_hashing_a_value_id() {
    use crate::compiler2::body::value_id_hashes;
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};
    use crate::modules::identity::ModuleName;
    use crate::telemetry::ConfiguredTelemetry;

    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("value_tables.fz".into()),
        text: r#"
defmodule Tables do
  def pairs(list, acc) do
    case list do
      [] -> acc
      [head | tail] -> pairs(tail, [{head, head * 2} | acc])
    end
  end
end
"#
        .into(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("value_tables_main.fz".into()),
        text: "require Tables\ndef main(), do: length(Tables.pairs([1, 2, 3], []))\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(3));
    let module = compiler
        .world_mut()
        .reference_module(ModuleName::parse_dotted("Tables").unwrap());
    let pairs = compiler.world_mut().reference_function(module, "pairs", 2);
    let body = compiler.world().lowered_body(pairs);
    let LoweredBody::Clauses {
        clauses,
        entries,
        generated,
        ..
    } = &*body;

    let before = value_id_hashes::so_far();
    let rebuilt = LoweredBody::clauses(clauses.clone(), entries.clone(), generated.clone());
    let origins = collect_value_origins(&rebuilt);
    let hashed = value_id_hashes::so_far() - before;

    assert!(
        !origins.is_empty(),
        "the body defines values whose origins are collected"
    );
    assert_eq!(hashed, 0, "{hashed} value ids were hashed while building the tables");
}

/// What one type contributes to an executable's runtime-demand inputs is a
/// function of the type alone: preparing it again, once the world has memoized
/// its projection, yields the same inputs as preparing it cold.
#[test]
fn preparing_a_callable_type_twice_yields_equal_inputs() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let callable = world.types_mut().arrow(&[int], int);
    let any = world.types_mut().any();

    let mut cold = RuntimeDemandTypeBuilder::new(any);
    prepare_type_projection(&mut world, &mut cold, callable);
    let mut warm = RuntimeDemandTypeBuilder::new(any);
    prepare_type_projection(&mut world, &mut warm, callable);

    assert_eq!(cold.inputs, warm.inputs);
}

/// A call's returned value is made of the call itself, in the form its tail
/// makes: a direct call returns its call site, a closure call also names the
/// closure it called. A call site the body does not make has no return origin.
#[test]
fn a_calls_return_origin_is_derived_from_its_tail() {
    use crate::compiler2::body::{ControlDestination, ControlEntryOrigin, DirectCallee};
    use crate::source::Span;
    let entry = |tail| LoweredEntry {
        span: Span::DUMMY,
        origin: ControlEntryOrigin::Clause,
        params: Vec::new(),
        captures: Vec::new(),
        capture_owners: Vec::new(),
        physical_captures: Vec::new(),
        physical_params: Vec::new(),
        steps: Vec::new(),
        tail,
    };
    let (direct, closure) = (CallSiteId::from_u32(0), CallSiteId::from_u32(1));
    let body = LoweredBody::clauses(
        Vec::new(),
        vec![
            entry(LoweredTail::DirectCall {
                value: ValueId::from_u32(0),
                callsite: direct,
                callee: DirectCallee::Function(FunctionId::from_coordinate(0)),
                args: Vec::new(),
                dest: ControlDestination::Return,
            }),
            entry(LoweredTail::ClosureCall {
                value: ValueId::from_u32(1),
                callsite: closure,
                callee: ValueId::from_u32(2),
                args: Vec::new(),
                dest: ControlDestination::Return,
            }),
        ],
        Vec::new(),
    );

    assert_eq!(
        callsite_return_origin(&body, direct),
        Some(TransportOrigin::CallsiteReturn(direct))
    );
    assert_eq!(
        callsite_return_origin(&body, closure),
        Some(TransportOrigin::ClosureCallReturn {
            callsite: closure,
            callee: ValueId::from_u32(2),
        })
    );
    assert_eq!(callsite_return_origin(&body, CallSiteId::from_u32(5)), None);
}

/// A recursive type whose every value is a tuple holds itself only below a
/// field that is not one -- here a list -- because a value is finite. So
/// preparing it descends through its tuple fields, stops at the list, and
/// never reads its own unfinished projection.
#[test]
fn a_recursive_tuple_type_is_projected_field_by_field() {
    let mut world = World::new();
    let rose = world.types_mut().recursive(1, |t, me| {
        let int = t.int();
        let children = t.list(me[0]);
        vec![t.tuple(&[int, children])]
    })[0];
    let any = world.types_mut().any();
    let mut builder = RuntimeDemandTypeBuilder::new(any);
    prepare_type_projection(&mut world, &mut builder, rose);
    let int = world.types_mut().int();
    let children = world.types_mut().list(rose);
    assert_eq!(builder.projections[&rose].field_tys, vec![int, children]);
    assert!(builder.projections[&children].field_tys.is_empty());
}

/// A projection is made once per type: asking for a type that has none makes
/// it, and asking again leaves the memo as it is.
#[test]
fn ensuring_a_projection_makes_it_once() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let pair = world.types_mut().tuple(&[int, int]);
    assert!(world.runtime_demand_type_projection(pair).is_none());

    let missing = world.types_missing_runtime_demand_projection(&[pair]);
    assert_eq!(missing, vec![pair]);
    project_missing_runtime_demand_types(&mut world, missing);
    assert!(world.runtime_demand_type_projection(pair).is_some());
    let size = world.runtime_demand_type_projections().len();

    assert!(world.types_missing_runtime_demand_projection(&[pair, int]).is_empty());
    project_missing_runtime_demand_types(&mut world, Vec::new());
    assert_eq!(world.runtime_demand_type_projections().len(), size);
}
