use super::*;
use crate::ast::{Pattern, Spanned};
use crate::compiler2::World;
use crate::compiler2::transport::{LaneDescr, ShapeDescr, ShapeId, TransportClass, TransportLayout};
use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};

/// A head over `input_count` inputs, one row per clause and one pattern per
/// input in each row.
fn plan_over_inputs(input_count: usize, rows: Vec<Vec<Pattern>>) -> PatternDispatchPlan<Ty> {
    pattern_dispatch_from_source(SourcePatternRows::lexical(
        input_count,
        rows.into_iter()
            .enumerate()
            .map(|(body_id, patterns)| PatternRow {
                patterns: patterns.into_iter().map(Spanned::dummy).collect(),
                preconditions: Vec::new(),
                guard: None,
                body_id: body_id as u32,
            })
            .collect(),
    ))
    .expect("the head compiles")
}

fn one_input_plan(patterns: Vec<Pattern>) -> PatternDispatchPlan<Ty> {
    plan_over_inputs(1, patterns.into_iter().map(|pattern| vec![pattern]).collect())
}

/// An entry head whose captures arrive as leading inputs, pinning the one
/// that delivers `want`.
fn entry_plan_pinning_input_zero() -> PatternDispatchPlan<Ty> {
    pattern_dispatch_from_source(SourcePatternRows::entry(
        2,
        vec![PatternRow {
            patterns: vec![
                Spanned::dummy(Pattern::Wildcard),
                Spanned::dummy(Pattern::Pinned("want".to_string())),
            ],
            preconditions: Vec::new(),
            guard: None,
            body_id: 0,
        }],
        vec![("want".to_string(), 0)],
    ))
    .expect("an entry head that pins a delivered input compiles")
}

/// A tuple shape whose every field is one integer lane, the form a caller
/// delivers a tuple in when nothing forced it onto the heap.
fn int_lane_tuple(transport: &mut TransportStore, types: &mut Types, arity: usize) -> ShapeId {
    let int = types.int();
    let lane = transport.interners_mut().intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let field = transport.interners_mut().intern_shape(ShapeDescr::Lane(lane));
    transport.interners_mut().intern_shape(ShapeDescr::Tuple(
        std::iter::repeat_n(TransportLayout::structural(field), arity)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    ))
}

/// The subject a plan names for one of its inputs.
fn input_subject(plan: &PatternDispatchPlan<Ty>, ordinal: u32) -> SubjectId {
    plan.matrix
        .subjects
        .iter()
        .find(|subject| matches!(subject.source, SubjectSource::Input { ordinal: read } if read == ordinal))
        .expect("the plan reads that input")
        .id
}

/// The subject a plan names for one field of its tuple input.
fn tuple_field_subject(plan: &PatternDispatchPlan<Ty>, index: u32) -> SubjectId {
    plan.matrix
        .subjects
        .iter()
        .find(|subject| {
            matches!(&subject.source, SubjectSource::Projection(projection)
                if matches!(projection.kind, ProjectionKind::TupleField(field) if field == index))
        })
        .expect("the plan projects that tuple field")
        .id
}

/// The subjects a plan extracts out of a bitstring input.
fn bitstring_field_subjects(plan: &PatternDispatchPlan<Ty>) -> Vec<SubjectId> {
    plan.matrix
        .subjects
        .iter()
        .filter(|subject| {
            matches!(&subject.source, SubjectSource::Projection(projection)
                if matches!(projection.kind, ProjectionKind::BitstringField(_)))
        })
        .map(|subject| subject.id)
        .collect()
}

/// One byte of a bitstring pattern, bound to a name.
fn byte_field(name: &str) -> crate::ast::BitField<Spanned<Pattern>> {
    crate::ast::BitField {
        value: Spanned::dummy(Pattern::Var(name.to_string())),
        spec: crate::ast::BitFieldSpec {
            size: Some(crate::ast::BitSize::Literal(8)),
            ..Default::default()
        },
    }
}

/// A map pattern keyed by a binary, which is what makes a plan carry a
/// prepared key.
fn binary_key_pattern(key: &str, bind: &str) -> Pattern {
    Pattern::Map(vec![(
        Spanned::dummy(Pattern::Binary(key.as_bytes().to_vec())),
        Spanned::dummy(Pattern::Var(bind.to_string())),
    )])
}

fn bitstring_value(proc: *mut Process, bytes: &[u8]) -> AnyValue {
    let word = fz_runtime::ir_runtime::fz_alloc_bitstring_const(
        proc,
        bytes.as_ptr() as u64,
        bytes.len() as u64,
        (bytes.len() * 8) as u64,
    );
    interp_value_from_ref_word(word, "test bitstring").expect("a bitstring value")
}

fn map_with_binary_key(proc: *mut Process, key: &str, value: i64) -> AnyValue {
    let empty = fz_runtime::ir_runtime::fz_map_empty(proc);
    let key = bitstring_value(proc, key.as_bytes())
        .as_ref_word(proc)
        .expect("a binary key reference");
    let map = fz_runtime::ir_runtime::fz_map_put_int(proc, empty, key, value);
    interp_value_from_ref_word(map, "test map").expect("a map value")
}

/// How many bitstrings this process has put on its heap. A prepared binary
/// key is one of them, which is what makes building one observable.
fn bitstring_allocs(proc: *mut Process) -> u64 {
    unsafe { &*proc }.heap.alloc_stats_snapshot().bitstring.allocs
}

fn live_runtime() -> IrInterpRuntime {
    let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
    runtime.current_proc = runtime.process_ptr(1).unwrap();
    runtime
}

/// An input the plan reads that never arrived is a disagreement between the
/// plan and its caller, not a subject that simply failed its test.
#[test]
fn an_input_the_plan_reads_but_never_received_stops_the_run() {
    let plan = one_input_plan(vec![Pattern::Tuple(vec![Spanned::dummy(Pattern::Wildcard)])]);
    let mut runtime = live_runtime();
    let world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let transport = TransportStore::new();
    let pinned = DispatchValues::default();
    let module = Module::default();
    let error = Dispatch::new(
        &mut runtime,
        world.types(),
        &program,
        &module,
        &plan,
        DispatchOperands {
            transport: &transport,
            inputs: &[],
            pinned: &pinned,
        },
    )
    .run()
    .err()
    .expect("the plan reads the only input, which was never delivered");
    assert_eq!(error, "dispatch reads input 0, which did not arrive");
}

/// The door answers which clause of a multi-clause plan the operands chose.
#[test]
fn the_door_decides_which_clause_the_operands_choose() {
    let plan = one_input_plan(vec![Pattern::Int(1), Pattern::Var("other".to_string())]);
    let mut runtime = live_runtime();
    let world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let transport = TransportStore::new();
    let pinned = DispatchValues::default();
    let module = Module::default();
    for (input, expected_body) in [(1, 0u32), (2, 1)] {
        let inputs = [Some(BackendBoundValue::Runtime(AnyValue::Int(input)))];
        let decided = Dispatch::new(
            &mut runtime,
            world.types(),
            &program,
            &module,
            &plan,
            DispatchOperands {
                transport: &transport,
                inputs: &inputs,
                pinned: &pinned,
            },
        )
        .run()
        .expect("the plan decides")
        .expect("a clause matched");
        assert_eq!(
            plan.body_id(decided.outcome()),
            expected_body,
            "the door answers the clause the operands chose"
        );
    }
}

/// The outcome's arguments are read off the decision itself: the bindings a
/// winning clause carries name subjects, and the run that decided produces
/// them from the operands it already holds.
#[test]
fn an_outcome_argument_reads_the_run_that_decided_it() {
    let plan = one_input_plan(vec![Pattern::Int(1), Pattern::Var("other".to_string())]);
    let mut runtime = live_runtime();
    let world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let transport = TransportStore::new();
    let pinned = DispatchValues::default();
    let module = Module::default();
    let inputs = [Some(BackendBoundValue::Runtime(AnyValue::Int(7)))];
    let mut decided = Dispatch::new(
        &mut runtime,
        world.types(),
        &program,
        &module,
        &plan,
        DispatchOperands {
            transport: &transport,
            inputs: &inputs,
            pinned: &pinned,
        },
    )
    .run()
    .expect("the plan decides")
    .expect("a clause matched");
    let binding = plan
        .outcome(decided.outcome())
        .expect("a winning outcome")
        .bindings
        .first()
        .expect("the matching clause binds its variable")
        .clone();
    let bound = decided
        .subject_word(binding.source)
        .expect("the decision holds the subject");
    assert_eq!(
        bound.as_i64(),
        Some(7),
        "the winning outcome's argument comes from the operands the run decided on"
    );
}

/// One pin, two doors: an entry plan reads it out of the input that
/// delivered it and a match site reads it out of its environment, through
/// the same operand builder.
#[test]
fn a_pin_comes_from_an_input_ordinal_or_from_an_environment_value() {
    let entry_plan = entry_plan_pinning_input_zero();
    let site_plan = one_input_plan(vec![Pattern::Pinned("want".to_string())]);
    let runtime = live_runtime();
    let transport = TransportStore::new();
    let want = AnyValue::Int(41);

    let inputs = [Some(BackendBoundValue::Runtime(want)), None];
    let from_input = dispatch_values(
        runtime.cur_proc(),
        &transport,
        &entry_plan,
        DispatchSource::Inputs(&inputs),
    )
    .expect("the delivering input supplies the pin");

    let value = ValueId::from_u32(3);
    let env = HashMap::from([(value, BackendBoundValue::Runtime(want))]);
    let bindings = DispatchBindings {
        pinned: vec![value],
        prepared: Vec::new(),
    };
    let from_env = dispatch_values(
        runtime.cur_proc(),
        &transport,
        &site_plan,
        DispatchSource::Bound {
            env: &env,
            bindings: &bindings,
        },
    )
    .expect("the named environment value supplies the pin");

    assert_eq!(
        from_input.pinned.len(),
        1,
        "an entry plan's pin is one operand beyond its inputs"
    );
    assert_eq!(
        from_input.pinned[0].as_i64(),
        from_env.pinned[0].as_i64(),
        "both doors hand the executor the same pinned word"
    );
}

/// A pin is compared whole, so a delivering input that arrived as lanes
/// carries no operand for it, and the refusal names the pin.
#[test]
fn a_pin_whose_input_arrives_in_lane_form_is_refused_by_name() {
    let plan = entry_plan_pinning_input_zero();
    let runtime = live_runtime();
    let mut transport = TransportStore::new();
    let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
    let tuple = transport
        .interners_mut()
        .intern_shape(ShapeDescr::Tuple(Box::from([TransportLayout::structural(nothing)])));
    let inputs = [
        Some(BackendBoundValue::Transport {
            shape: tuple,
            lanes: Vec::new(),
        }),
        None,
    ];
    let error = dispatch_values(runtime.cur_proc(), &transport, &plan, DispatchSource::Inputs(&inputs))
        .expect_err("a lane-form input holds no single word to compare against");
    assert_eq!(error, "dispatch pin `want` has no runtime argument operand");
}

/// A test that misses leaves nothing of what it produced.
///
/// The arity question resolves the input to ask it, and then misses. The
/// arm that gets its turn next reads a state that holds no answer from the
/// arm that lost, so nothing a failed question decided can decide anything
/// after it.
#[test]
fn a_failed_test_undoes_the_subjects_it_produced() {
    let plan = one_input_plan(vec![
        Pattern::Tuple(vec![Spanned::dummy(Pattern::Int(1))]),
        Pattern::Var("other".to_string()),
    ]);
    let mut runtime = live_runtime();
    let mut world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let mut transport = TransportStore::new();
    let pair = int_lane_tuple(&mut transport, world.types_mut(), 2);
    let pinned = DispatchValues::default();
    let module = Module::default();
    let inputs = [Some(BackendBoundValue::Transport {
        shape: pair,
        lanes: vec![AnyValue::Int(9), AnyValue::Int(8)],
    })];
    let decided = Dispatch::new(
        &mut runtime,
        world.types(),
        &program,
        &module,
        &plan,
        DispatchOperands {
            transport: &transport,
            inputs: &inputs,
            pinned: &pinned,
        },
    )
    .run()
    .expect("the plan decides")
    .expect("the wildcard arm matches");
    assert_eq!(
        plan.body_id(decided.outcome()),
        1,
        "a two-field tuple answers no one-field tuple question"
    );
    assert!(
        decided.run.state.get(input_subject(&plan, 0)).is_none(),
        "the input the failed arity test resolved is not carried past it"
    );
}

/// A branch that is taken keeps what its test learned.
///
/// The arity question matches and projects both fields; the literal
/// question after it misses. The fields stay, because the branch that
/// produced them is the branch the walk took, and the question after the
/// miss reads them instead of projecting them again.
#[test]
fn a_taken_branch_keeps_what_its_test_learned() {
    let plan = one_input_plan(vec![
        Pattern::Tuple(vec![Spanned::dummy(Pattern::Int(1)), Spanned::dummy(Pattern::Wildcard)]),
        Pattern::Var("other".to_string()),
    ]);
    let mut runtime = live_runtime();
    let mut world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let mut transport = TransportStore::new();
    let pair = int_lane_tuple(&mut transport, world.types_mut(), 2);
    let pinned = DispatchValues::default();
    let module = Module::default();
    let inputs = [Some(BackendBoundValue::Transport {
        shape: pair,
        lanes: vec![AnyValue::Int(9), AnyValue::Int(8)],
    })];
    let decided = Dispatch::new(
        &mut runtime,
        world.types(),
        &program,
        &module,
        &plan,
        DispatchOperands {
            transport: &transport,
            inputs: &inputs,
            pinned: &pinned,
        },
    )
    .run()
    .expect("the plan decides")
    .expect("the wildcard arm matches");
    assert_eq!(
        plan.body_id(decided.outcome()),
        1,
        "field 0 is 9, so the literal arm loses"
    );
    for (index, expected) in [(0u32, 9i64), (1, 8)] {
        let field = tuple_field_subject(&plan, index);
        assert_eq!(
            decided
                .run
                .state
                .get(field)
                .and_then(BackendBoundValue::runtime_word)
                .and_then(|word| word.as_i64()),
            Some(expected),
            "the arity test that matched keeps the field it projected"
        );
    }
}

/// A field a failing bitstring shape extracted is not visible to the next
/// arm.
///
/// Reading a bitstring binds field by field, so a shape that fails on its
/// last field has already bound the ones before it. Those bindings belong
/// to the arm that failed, and the arm that wins never sees them.
#[test]
fn a_bitstring_field_a_failed_shape_extracted_is_not_visible_to_the_next_arm() {
    let plan = one_input_plan(vec![
        Pattern::Bitstring(vec![byte_field("first"), byte_field("second")]),
        Pattern::Var("other".to_string()),
    ]);
    let mut runtime = live_runtime();
    let world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let transport = TransportStore::new();
    let pinned = DispatchValues::default();
    let module = Module::default();
    let inputs = [Some(BackendBoundValue::Runtime(bitstring_value(
        runtime.cur_proc(),
        b"a",
    )))];
    let fields = bitstring_field_subjects(&plan);
    assert_eq!(fields.len(), 2, "the shape names one subject per field");
    let decided = Dispatch::new(
        &mut runtime,
        world.types(),
        &program,
        &module,
        &plan,
        DispatchOperands {
            transport: &transport,
            inputs: &inputs,
            pinned: &pinned,
        },
    )
    .run()
    .expect("the plan decides")
    .expect("the wildcard arm matches");
    assert_eq!(plan.body_id(decided.outcome()), 1, "one byte answers no two-byte shape");
    for field in fields {
        assert!(
            decided.run.state.get(field).is_none(),
            "a field the failed shape read is gone with it"
        );
    }
}

/// A prepared binary key no test reads is never built.
///
/// The key of a map pattern is a copy onto the process heap, and the arm
/// that wins here is decided before the map pattern is ever asked, so the
/// copy is never made.
#[test]
fn a_prepared_binary_key_no_test_reads_is_never_built() {
    let plan = one_input_plan(vec![
        Pattern::Tuple(vec![Spanned::dummy(Pattern::Int(1))]),
        binary_key_pattern("key", "value"),
        Pattern::Var("other".to_string()),
    ]);
    assert_eq!(plan.prepared_keys.len(), 1, "the map pattern prepares its binary key");
    let mut runtime = live_runtime();
    let mut world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let mut transport = TransportStore::new();
    let single = int_lane_tuple(&mut transport, world.types_mut(), 1);
    let module = Module::default();
    let proc = runtime.cur_proc();
    let inputs = [Some(BackendBoundValue::Transport {
        shape: single,
        lanes: vec![AnyValue::Int(1)],
    })];
    let before = bitstring_allocs(proc);
    let values = dispatch_values(proc, &transport, &plan, DispatchSource::Inputs(&inputs))
        .expect("the plan's operands are built");
    let decided = Dispatch::new(
        &mut runtime,
        world.types(),
        &program,
        &module,
        &plan,
        DispatchOperands {
            transport: &transport,
            inputs: &inputs,
            pinned: &values,
        },
    )
    .run()
    .expect("the plan decides")
    .expect("the tuple arm matches");
    assert_eq!(plan.body_id(decided.outcome()), 0, "the tuple arm answers first");
    assert_eq!(
        bitstring_allocs(proc) - before,
        0,
        "a key no question reaches costs the process nothing"
    );
    let PreparedValues::Constants(cells) = &values.prepared else {
        panic!("an entry plan builds its own prepared keys");
    };
    assert!(cells[0].get().is_none(), "the key's cell is still empty");
}

/// A prepared binary key two tests read is built once.
///
/// Both inputs are asked for the same key. The first question that reads it
/// builds the one copy the run has, and the second reads that copy.
#[test]
fn a_prepared_binary_key_two_tests_read_is_built_once() {
    let plan = plan_over_inputs(
        2,
        vec![vec![
            binary_key_pattern("key", "left"),
            binary_key_pattern("key", "right"),
        ]],
    );
    assert_eq!(
        plan.prepared_keys.len(),
        1,
        "one constant, however many questions ask it"
    );
    let mut runtime = live_runtime();
    let world = World::new();
    let program = crate::compiler2::BackendProgram::empty_for_test();
    let transport = TransportStore::new();
    let module = Module::default();
    let proc = runtime.cur_proc();
    let map = map_with_binary_key(proc, "key", 42);
    let inputs = [
        Some(BackendBoundValue::Runtime(map)),
        Some(BackendBoundValue::Runtime(map)),
    ];
    let before = bitstring_allocs(proc);
    let values = dispatch_values(proc, &transport, &plan, DispatchSource::Inputs(&inputs))
        .expect("the plan's operands are built");
    let decided = Dispatch::new(
        &mut runtime,
        world.types(),
        &program,
        &module,
        &plan,
        DispatchOperands {
            transport: &transport,
            inputs: &inputs,
            pinned: &values,
        },
    )
    .run()
    .expect("the plan decides")
    .expect("both maps hold the key");
    assert_eq!(plan.body_id(decided.outcome()), 0, "the only arm matches");
    assert_eq!(
        bitstring_allocs(proc) - before,
        1,
        "two questions over one constant are one copy"
    );
}
