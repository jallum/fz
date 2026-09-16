use super::*;
use crate::compiler2::pull::TransportCarrier;
use crate::compiler2::transport::{LaneDescr, TransportClass};
use crate::compiler2::{
    AbiValueRepr, ActivationKey, BackendEntryOrigin, BackendSemanticInputLayout, BackendValueLayout, CallSiteId,
    ClosureCallEdge, ControlEntryId, ExecutableNeed, ModuleId, RootId, Ty, World,
};
use crate::source::Span;
use crate::telemetry::ConfiguredTelemetry;
use fz_runtime::ir_runtime::{fz_list_head_ref, fz_list_tail_ref};

/// Entry dispatch refuses to decide when an input its plan reads never
/// arrived: the questions it asks have no value to ask them of.
#[test]
fn entry_dispatch_refuses_an_input_its_plan_reads_but_never_received() {
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};
    let plan = pattern_dispatch_from_source::<crate::compiler2::Ty>(SourcePatternRows::lexical(
        1,
        vec![
            PatternRow {
                patterns: vec![crate::ast::Spanned::dummy(crate::ast::Pattern::Int(1))],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            },
            PatternRow {
                patterns: vec![crate::ast::Spanned::dummy(crate::ast::Pattern::Wildcard)],
                preconditions: Vec::new(),
                guard: None,
                body_id: 1,
            },
        ],
    ))
    .expect("a two-clause head compiles");
    let dispatch = crate::compiler2::ExecutableDispatch::new(Rc::new(plan), vec![0, 1]);
    let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
    runtime.current_proc = runtime.process_ptr(1).unwrap();
    let world = crate::compiler2::World::new();
    let program = empty_backend_program();
    let error = select_clause(
        &mut runtime,
        world.types(),
        &TransportStore::new(),
        &program,
        &Module::default(),
        &dispatch,
        &[None],
    )
    .expect_err("the plan reads the only input, which never arrived");
    assert_eq!(error, "backend clause dispatch required omitted semantic input 0");
}

#[test]
fn kernel_panic_preserves_a_composite_reason_without_terminating_the_interpreter_host() {
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};

    let mut compiler = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("composite_panic_reason.fz".into()),
        text: "def main() do\n  panic({:stop, [1, 2]})\n  dbg(:unreachable)\nend\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let error = compiler
        .run_root_interp(root)
        .expect_err("panic is an interpreter process error");
    assert!(error.contains("fz panic: {:stop, [1, 2]}"), "{error}");

    let mut survivor = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
    survivor.submit_code(CodeSubmission {
        name: Some("after_interpreted_panic.fz".into()),
        text: "def main(), do: 42\n".into(),
    });
    let survivor_root = survivor.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(survivor.run_root_interp(survivor_root), Ok(42));
}

#[test]
fn generic_panic_dispatch_consumes_the_context_fault_before_the_never_return_error() {
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};

    let mut compiler = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("panic_callback_error.fz".into()),
        text: "def main(), do: panic(9)\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .expect_err("compile and execute real Kernel panic path");
    let program = compiler.retained_backend_program(root);
    let signature = program
        .executables()
        .iter()
        .find_map(|executable| match &executable.body {
            BackendBody::Extern { signature } if signature.symbol == "fz_panic" => Some(signature.clone()),
            _ => None,
        })
        .expect("real lowered fz_panic declaration");

    let names = program
        .atom_names
        .iter()
        .map(|name| name.as_ref().clone())
        .collect::<Vec<_>>();
    let module = Module {
        atom_names: names.clone(),
        ..Module::default()
    };
    let transport = TransportStore::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut runtime = IrInterpRuntime::fresh_with_atoms(names);
    let process = runtime.process_ptr(1).unwrap();
    runtime.current_proc = process;
    let types = compiler.world_mut().types_mut() as *mut crate::compiler2::Types;
    let mut scheduler_adapter = BackendSchedulerAdapter {
        runtime: &mut runtime,
        types,
        transport: &transport,
        tel: &tel,
        program: program.as_ref(),
        module: &module,
    };
    let mut exec_ctx = ExecCtx {
        scheduler: &mut scheduler_adapter as *mut BackendSchedulerAdapter<_> as *mut (),
        fault: Some(interp_fault_hook::<crate::telemetry::ConfiguredTelemetry>),
        ..ExecCtx::empty()
    };
    unsafe { &mut *process }.ctx = &mut exec_ctx;

    let error = call_lowered_extern(&mut runtime, &signature, None, &[AnyValue::Int(9)])
        .expect_err("the callback error must win over the generic Never-returned fallback");
    assert_eq!(error, "fz panic: 9");
    assert_eq!(
        runtime.take_callback_error(),
        None,
        "the callback error is consumed once"
    );
}

#[test]
fn a_foreign_function_declared_never_cannot_return_into_interpreted_code() {
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};

    let mut compiler = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("returning_never_extern.fz".into()),
        text: "extern \"C\" defp _test_never_returns() :: never\ndef main() do\n  _test_never_returns()\n  dbg(:unreachable)\nend\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let error = compiler
        .run_root_interp(root)
        .expect_err("a Never extern returning is a runtime contract violation");
    assert!(
        error.contains("extern `_test_never_returns` declared Never returned"),
        "the generic return policy must diagnose the declaration, not resume unreachable source: {error}",
    );
}

#[test]
fn generic_spawn_dispatch_returns_adapter_error_before_pid_sentinel() {
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};

    let mut compiler = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("spawn_callback_error.fz".into()),
        text: "def main(), do: spawn(fn () -> nil end)\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root).expect("compile real Kernel spawn path");
    let program = compiler.retained_backend_program(root);
    let signature = program
        .executables()
        .iter()
        .find_map(|executable| match &executable.body {
            BackendBody::Extern { signature } if signature.symbol == "fz_spawn" => Some(signature.clone()),
            _ => None,
        })
        .expect("real lowered fz_spawn declaration");
    assert_eq!(signature.abi, crate::fz_ir::ExternAbi::Fz);
    assert_eq!(signature.params, [crate::fz_ir::ExternTy::Any]);
    assert_eq!(signature.ret, crate::fz_ir::ExternTy::I64);

    let names = program
        .atom_names
        .iter()
        .map(|name| name.as_ref().clone())
        .collect::<Vec<_>>();
    let module = Module {
        atom_names: names.clone(),
        ..Module::default()
    };
    let transport = TransportStore::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut runtime = IrInterpRuntime::fresh_with_atoms(names);
    let sender = runtime.process_ptr(1).unwrap();
    runtime.current_proc = sender;
    let types = compiler.world_mut().types_mut() as *mut crate::compiler2::Types;
    let mut scheduler_adapter = BackendSchedulerAdapter {
        runtime: &mut runtime,
        types,
        transport: &transport,
        tel: &tel,
        program: program.as_ref(),
        module: &module,
    };
    let mut exec_ctx = ExecCtx {
        scheduler: &mut scheduler_adapter as *mut BackendSchedulerAdapter<_> as *mut (),
        spawn: Some(interp_spawn_hook::<crate::telemetry::ConfiguredTelemetry>),
        ..ExecCtx::empty()
    };
    unsafe { &mut *sender }.ctx = &mut exec_ctx;

    let result = call_lowered_extern(&mut runtime, &signature, None, &[AnyValue::Int(9)]);
    let error = result.expect_err("a non-closure must not become pid sentinel 0");
    assert!(
        error.contains("call_closure on non-closure value"),
        "the scheduler adapter's actual closure error must cross the physical extern call: {error}",
    );
    assert_eq!(
        runtime.take_callback_error(),
        None,
        "generic return handling consumes the callback error exactly once",
    );
}

#[test]
fn scheduler_adapter_copies_spawn_inputs_and_dead_send_is_observation_free() {
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};

    let mut compiler = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("scheduler_adapter_ownership.fz".into()),
        text: "def main(), do: nil\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root).expect("compile ownership witness");
    let program = compiler.retained_backend_program(root);
    let executable = backend_executable_ref(&program, compiler.world().types(), program.entry()).unwrap();
    let names = program
        .atom_names
        .iter()
        .map(|name| name.as_ref().clone())
        .collect::<Vec<_>>();
    let module = Module {
        atom_names: names.clone(),
        ..Module::default()
    };
    let mut runtime = IrInterpRuntime::fresh_with_atoms(names);
    let sender = runtime.process_ptr(1).unwrap();
    runtime.current_proc = sender;
    let input = interp_list_cons(sender, AnyValue::Int(1), AnyValue::EmptyList, "spawn input").unwrap();
    let input_ref = input.as_any_value_ref(sender).unwrap();

    let receiver_pid = runtime
        .spawn_backend(sender, Rc::clone(&executable), vec![input])
        .unwrap();
    let BackendResumeEntry::Executable { args, .. } =
        runtime.backend_resume.get(&receiver_pid).expect("spawned child entry")
    else {
        panic!("spawned child starts at its executable")
    };
    let copied = args[0]
        .as_any_value_ref(runtime.process_ptr(receiver_pid).unwrap())
        .unwrap();
    let input_addr = input_ref.heap_addr(ValueKind::LIST).unwrap();
    let copied_addr = copied.heap_addr(ValueKind::LIST).unwrap();
    assert_ne!(copied_addr, input_addr);
    assert!(unsafe { &*sender }.heap.contains_heap_addr(input_addr));
    assert!(
        runtime
            .process_ref(receiver_pid)
            .unwrap()
            .heap
            .contains_heap_addr(copied_addr)
    );

    runtime.set_process_state(receiver_pid, ProcessState::Exited);
    let message = interp_list_cons(sender, AnyValue::Int(2), AnyValue::EmptyList, "send message").unwrap();
    let message_ref = message.as_any_value_ref(sender).unwrap();
    let receiver = runtime.process_ref(receiver_pid).unwrap();
    let before_heap = receiver.heap.alloc_stats_snapshot();
    let before_mailbox = receiver.mailbox.clone();
    let before_queue = runtime.run_queue.clone();
    let before_resume_len = runtime.backend_resume.len();
    let before_parked_len = runtime.backend_parked.len();

    for pid in [receiver_pid, u32::MAX] {
        runtime
            .send_ref(
                compiler.world_mut().types_mut(),
                &TransportStore::new(),
                &crate::telemetry::ConfiguredTelemetry::new(),
                &program,
                &module,
                &pid,
                message_ref,
            )
            .unwrap();
    }

    let receiver = runtime.process_ref(receiver_pid).unwrap();
    assert_eq!(receiver.heap.alloc_stats_snapshot(), before_heap);
    assert_eq!(receiver.mailbox, before_mailbox);
    assert_eq!(receiver.state, ProcessState::Exited);
    assert_eq!(runtime.run_queue, before_queue);
    assert_eq!(runtime.backend_resume.len(), before_resume_len);
    assert_eq!(runtime.backend_parked.len(), before_parked_len);
}

#[test]
fn parked_receive_copies_only_winning_subjects_into_receiver_heap() {
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
    let mut compiler = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("parked_projection.fz".into()),
        text: "def main() do\n receive do\n [_, h | t] -> [h | t]\n end\nend\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root).expect("compile and park receive");
    let program = compiler.retained_backend_program(root);
    let executable = backend_executable_ref(&program, compiler.world().types(), program.entry()).unwrap();
    let entries = entries_for_executable(&executable).unwrap();
    let owner = entries
        .iter()
        .position(|entry| matches!(entry.tail, BackendTail::Receive(_)))
        .unwrap();
    let source = entries
        .iter()
        .flat_map(|entry| &entry.steps)
        .find_map(|step| match step {
            ProgramStep::List {
                retention: Some(retention),
                ..
            } => Some(retention.source),
            _ => None,
        })
        .expect("physical exact source operand");
    let names = program
        .atom_names
        .iter()
        .map(|name| name.as_ref().clone())
        .collect::<Vec<_>>();
    let module = Module {
        atom_names: names.clone(),
        ..Module::default()
    };
    let mut runtime = IrInterpRuntime::fresh_with_atoms(names);
    let sender = runtime.process_ptr(1).unwrap();
    runtime.current_proc = sender;
    let receiver_pid = runtime
        .spawn_backend(sender, Rc::clone(&executable), Vec::new())
        .unwrap();
    runtime.backend_parked.insert(
        receiver_pid,
        BackendParkRecord {
            executable,
            entry: crate::compiler2::ControlEntryId::from_u32(owner as u32),
            env: HashMap::new(),
            continuations: Vec::new(),
        },
    );
    let mut ignored = AnyValue::EmptyList;
    for value in 0..20 {
        ignored = interp_list_cons(sender, AnyValue::Int(value), ignored, "ignored").unwrap();
    }
    let tail = interp_list_cons(sender, AnyValue::Int(2), AnyValue::EmptyList, "tail").unwrap();
    let retained = interp_list_cons(sender, AnyValue::Int(1), tail, "source").unwrap();
    let message = interp_list_cons(sender, ignored, retained, "message").unwrap();
    runtime
        .send_ref(
            compiler.world_mut().types_mut(),
            &TransportStore::new(),
            &crate::telemetry::ConfiguredTelemetry::new(),
            &program,
            &module,
            &receiver_pid,
            message.as_any_value_ref(sender).unwrap(),
        )
        .unwrap();
    let BackendResumeEntry::Entry { env, .. } = runtime.take_backend_resume(receiver_pid).expect("winning wake") else {
        panic!("direct outcome entry")
    };
    let receiver = runtime.process_ptr(receiver_pid).unwrap();
    let copied = env_get(&TransportStore::new(), receiver, &env, source)
        .unwrap()
        .as_any_value_ref(receiver)
        .unwrap();
    let address = copied.heap_addr(ValueKind::LIST).expect("retained cell");
    assert!(unsafe { &*receiver }.heap.contains_heap_addr(address));
    assert!(!unsafe { &*sender }.heap.contains_heap_addr(address));
    assert_eq!(
        unsafe { &*receiver }.heap.alloc_stats_snapshot().list_cons.allocs,
        2,
        "only the two-cell winning source crosses heaps; ignored list and outer cell do not"
    );
    let mut roots = [copied];
    unsafe { &mut *receiver }
        .heap
        .gc_with_any_value_ref_roots(&mut std::ptr::null_mut(), &mut roots);
    let source = roots[0].raw_word();
    let retained = fz_runtime::ir_runtime::fz_list_reuse_or_cons_ref(
        receiver,
        source,
        fz_list_head_ref(source),
        fz_list_tail_ref(source),
        0,
    );
    assert_eq!(retained, source, "receiver GC preserves the exact retention operand");
}

#[test]
fn generic_callable_input_retains_structure_without_demanding_a_box() {
    let mut transport = TransportStore::new();
    let callable = transport
        .interners_mut()
        .intern_callable(crate::compiler2::transport::CallableDescr {
            function: None,
            arity: 0,
            capture_layouts: Box::default(),
        });
    let shape = transport.interners_mut().intern_shape(ShapeDescr::Callable(callable));
    let value = decode_transport_layout(&transport, &[], TransportLayout::structural(shape), &mut 0)
        .expect("an unused structural callable input requires no runtime allocation");
    assert!(
        matches!(value, BackendBoundValue::Transport { shape: actual, lanes } if actual == shape && lanes.is_empty())
    );
}

#[test]
fn zero_lane_inputs_preserve_tuple_structure_without_inventing_absence() {
    let mut world = crate::compiler2::World::new();
    let mut transport = TransportStore::new();
    let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "zero_lane", 4);
    let zero_capture = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "zero_capture", 0);
    let callable = transport
        .interners_mut()
        .intern_callable(crate::compiler2::transport::CallableDescr {
            function: Some(zero_capture),
            arity: 0,
            capture_layouts: Box::default(),
        });
    let callable = transport.interners_mut().intern_shape(ShapeDescr::Callable(callable));
    let empty_tuple = tuple_shape(&mut transport, &[]);
    let tuple = tuple_shape(&mut transport, &[empty_tuple, callable]);
    let ty = world.types_mut().any();
    let key = ExecutableKey {
        activation: crate::compiler2::ActivationKey::from_inputs(
            crate::compiler2::RootId::for_test(0),
            function,
            &[ty; 4],
            world.types_mut(),
        ),
        need: crate::compiler2::ExecutableNeed::Value,
    };
    let mut executable = BackendExecutable::for_test(key, ty, nothing);
    let empty_layout = executable.abi.return_layout.layout.clone();
    Rc::make_mut(&mut executable.abi).semantic_inputs = [nothing, callable, tuple]
        .into_iter()
        .enumerate()
        .map(|(semantic_index, structural)| {
            let mut layout = empty_layout.clone();
            layout.structural = structural;
            crate::compiler2::BackendSemanticInputLayout { semantic_index, layout }
        })
        .collect();
    let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
    let bound = bind_executable_inputs(&transport, &executable, &[]).expect("zero physical lanes");
    assert!(
        matches!(&bound[0], Some(BackendBoundValue::Absent)),
        "a published Nothing layout carries explicit absence"
    );
    assert!(
        matches!(&bound[1], Some(BackendBoundValue::Transport { shape, lanes }) if *shape == callable && lanes.is_empty()),
        "a published lane-free callable retains its structural identity"
    );
    assert!(
        matches!(&bound[2], Some(BackendBoundValue::Transport { shape, lanes }) if *shape == tuple && lanes.is_empty()),
        "a recursive zero-lane tuple is a concrete structural value"
    );
    assert!(
        bound[3].is_none(),
        "only an unpublished semantic ordinal remains missing"
    );
    for (index, input) in executable.abi.semantic_inputs.iter().enumerate() {
        assert!(input.layout.publishes_no_lanes());
        assert_eq!(
            transport
                .interners()
                .shape(input.layout.structural)
                .is_semantically_absent(),
            index == 0
        );
        let layout = crate::compiler2::BackendReturnLayout {
            layout: input.layout.clone(),
            diverges: false,
        };
        let result = bind_delivered_value(
            &transport,
            &empty_backend_program(),
            std::ptr::null_mut(),
            crate::compiler2::ControlEntryId::from_u32(0),
            None,
            &layout,
        );
        assert_eq!(
            result.is_ok(),
            index == 0,
            "only Nothing/Absent permits a missing delivery"
        );
        let mut lane_index = 0;
        let decoded = decode_transport_layout(
            &transport,
            &[],
            TransportLayout::structural(input.layout.structural),
            &mut lane_index,
        )
        .unwrap();
        assert_eq!(
            matches!(decoded, BackendBoundValue::Absent),
            index == 0,
            "zero lanes do not imply semantic absence"
        );
        assert_eq!(
            encode_for_layout(
                &transport,
                std::ptr::null_mut(),
                &BackendBoundValue::Absent,
                input.layout.structural
            )
            .is_ok(),
            index == 0,
            "an absent value cannot satisfy a zero-lane tuple or callable contract"
        );
    }
    runtime.current_proc = runtime.process_ptr(1).unwrap();
    for structural in [callable, tuple] {
        Rc::make_mut(&mut executable.abi).return_layout.layout.structural = structural;
        let entries = [BackendEntry {
            span: crate::source::Span::DUMMY,
            origin: crate::compiler2::BackendEntryOrigin::Branch,
            params: Vec::new(),
            captures: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps: Vec::new(),
            tail: BackendTail::Value {
                value: ValueId::from_u32(99),
                dest: ControlDestination::Return,
            },
        }];
        let result = step_eval_entry(
            &mut runtime,
            world.types_mut(),
            &transport,
            &crate::telemetry::ConfiguredTelemetry::new(),
            &empty_backend_program(),
            &Module::default(),
            &Rc::new(executable.clone()),
            &entries,
            crate::compiler2::ControlEntryId::from_u32(0),
            HashMap::new(),
            Vec::new(),
        );
        assert!(
            matches!(result, Ok(BackendEvalTransition::Done(_))),
            "a zero-lane return decodes its concrete contract without reading the missing value"
        );
    }
}

#[test]
fn entry_dispatch_does_not_materialize_unneeded_structural_inputs() {
    use crate::dispatch_matrix::demand::DispatchDemand;
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};
    let mut world = crate::compiler2::World::new();
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "ignore_tuple", 1);
    let ty = world.types_mut().any();
    let key = ExecutableKey {
        activation: crate::compiler2::ActivationKey::from_inputs(
            crate::compiler2::RootId::for_test(0),
            function,
            &[ty],
            world.types_mut(),
        ),
        need: crate::compiler2::ExecutableNeed::Value,
    };
    let mut transport = TransportStore::new();
    let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
    let tuple = tuple_shape(&mut transport, &[nothing]);
    let mut executable = BackendExecutable::for_test(key, ty, nothing);
    let abi = Rc::make_mut(&mut executable.abi);
    let mut layout = abi.return_layout.layout.clone();
    layout.structural = tuple;
    abi.semantic_inputs = Box::new([crate::compiler2::BackendSemanticInputLayout {
        semantic_index: 0,
        layout,
    }]);
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![PatternRow {
            patterns: vec![crate::ast::Spanned::dummy(crate::ast::Pattern::Wildcard)],
            preconditions: Vec::new(),
            guard: None,
            body_id: 0,
        }],
    ))
    .unwrap();
    let dispatch = ExecutableDispatch::new(Rc::new(plan), vec![0]);
    assert_eq!(
        dispatch.plan().input_demand(),
        [DispatchDemand::Ignore],
        "a wildcard head asks nothing of its parameter"
    );
    Rc::make_mut(&mut abi.materialized).entry_dispatch = Some(dispatch);
    let value = ValueId::from_u32(0);
    let result_value = ValueId::from_u32(1);
    executable.body = BackendBody::Clauses {
        clauses: vec![crate::compiler2::BackendClause {
            span: crate::source::Span::DUMMY,
            params: vec![value],
            projections: Vec::new(),
            entry: crate::compiler2::ControlEntryId::from_u32(0),
        }],
        entries: vec![BackendEntry {
            span: crate::source::Span::DUMMY,
            origin: crate::compiler2::BackendEntryOrigin::Clause,
            params: Vec::new(),
            captures: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps: vec![
                ProgramStep::AssertTuple {
                    source: value,
                    arity: 1,
                },
                ProgramStep::Const {
                    value: result_value,
                    literal: crate::ground_value::GroundValue::Int(42),
                },
            ],
            tail: BackendTail::Value {
                value: result_value,
                dest: ControlDestination::Return,
            },
        }],
        generated: Vec::new(),
    };
    let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
    runtime.current_proc = runtime.process_ptr(1).unwrap();
    let result = step_backend_executable(
        &mut runtime,
        world.types_mut(),
        &transport,
        &crate::telemetry::ConfiguredTelemetry::new(),
        &empty_backend_program(),
        &Module::default(),
        Rc::new(executable),
        Vec::new(),
        Vec::new(),
    );
    let result = result.unwrap_or_else(|error| panic!("entry dispatch must reach its body: {error}"));
    assert!(
        matches!(result, BackendEvalTransition::Done(value) if value.as_i64() == Some(42)),
        "dispatch must preserve the partial tuple for its body without trying to box its absent field"
    );
}

/// A lane-form tuple parameter is decided from its lanes.
///
/// The input arrives as a two-field tuple whose first field carries nothing
/// and whose second is one lane. The clause head asks about both: the arity,
/// and the literal in field 1. Neither question needs a heap tuple, and one
/// could not be built anyway, because the absent field has no value.
#[test]
fn entry_dispatch_decides_a_lane_form_tuple_from_its_lanes() {
    use crate::dispatch_matrix::demand::DispatchDemand;
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};
    use std::collections::BTreeMap;
    let mut world = crate::compiler2::World::new();
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "unwrap_tuple", 1);
    let ty = world.types_mut().any();
    let key = ExecutableKey {
        activation: crate::compiler2::ActivationKey::from_inputs(
            crate::compiler2::RootId::for_test(0),
            function,
            &[ty],
            world.types_mut(),
        ),
        need: crate::compiler2::ExecutableNeed::Value,
    };
    let mut transport = TransportStore::new();
    let int = world.types_mut().int();
    let lane = transport
        .interners_mut()
        .intern_lane(crate::compiler2::transport::LaneDescr {
            ty: int,
            class: crate::compiler2::transport::TransportClass::Value,
        });
    let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
    let scalar = transport.interners_mut().intern_shape(ShapeDescr::Lane(lane));
    let tuple = tuple_shape(&mut transport, &[nothing, scalar]);
    let mut executable = BackendExecutable::for_test(key, ty, nothing);
    let abi = Rc::make_mut(&mut executable.abi);
    let mut layout = abi.return_layout.layout.clone();
    layout.structural = tuple;
    abi.semantic_inputs = Box::new([crate::compiler2::BackendSemanticInputLayout {
        semantic_index: 0,
        layout,
    }]);
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
    let dispatch = ExecutableDispatch::new(Rc::new(plan), vec![0]);
    assert_eq!(
        dispatch.plan().input_demand(),
        [DispatchDemand::TupleFields(BTreeMap::from([(
            1,
            DispatchDemand::Whole
        )]))],
        "the clause head questions its tuple parameter"
    );
    Rc::make_mut(&mut abi.materialized).entry_dispatch = Some(dispatch);
    let value = ValueId::from_u32(0);
    let result_value = ValueId::from_u32(1);
    executable.body = BackendBody::Clauses {
        clauses: vec![crate::compiler2::BackendClause {
            span: crate::source::Span::DUMMY,
            params: vec![value],
            projections: Vec::new(),
            entry: crate::compiler2::ControlEntryId::from_u32(0),
        }],
        entries: vec![BackendEntry {
            span: crate::source::Span::DUMMY,
            origin: crate::compiler2::BackendEntryOrigin::Clause,
            params: Vec::new(),
            captures: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps: vec![ProgramStep::Const {
                value: result_value,
                literal: crate::ground_value::GroundValue::Int(42),
            }],
            tail: BackendTail::Value {
                value: result_value,
                dest: ControlDestination::Return,
            },
        }],
        generated: Vec::new(),
    };
    let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
    runtime.current_proc = runtime.process_ptr(1).unwrap();
    let result = step_backend_executable(
        &mut runtime,
        world.types_mut(),
        &transport,
        &crate::telemetry::ConfiguredTelemetry::new(),
        &empty_backend_program(),
        &Module::default(),
        Rc::new(executable),
        vec![AnyValue::Int(7)],
        Vec::new(),
    );
    let result = result.unwrap_or_else(|error| panic!("entry dispatch must reach its body: {error}"));
    assert!(
        matches!(result, BackendEvalTransition::Done(value) if value.as_i64() == Some(42)),
        "the clause head decides the lane-form tuple without boxing it"
    );
}

#[test]
fn continuations_and_local_resumes_execute_the_retained_body_without_inventory_lookup() {
    let mut world = crate::compiler2::World::new();
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "retained_resume", 0);
    let key = ExecutableKey {
        activation: crate::compiler2::ActivationKey::from_inputs(
            crate::compiler2::RootId::for_test(0),
            function,
            &[],
            world.types_mut(),
        ),
        need: crate::compiler2::ExecutableNeed::Value,
    };
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let return_ty = world.types_mut().int();
    let mut executable = BackendExecutable::for_test(key.clone(), return_ty, nothing);
    let value = ValueId::from_u32(0);
    let first = crate::compiler2::ControlEntryId::from_u32(0);
    let last = crate::compiler2::ControlEntryId::from_u32(1);
    executable.body = BackendBody::Clauses {
        clauses: Vec::new(),
        entries: [ControlDestination::Deliver(last), ControlDestination::Return]
            .into_iter()
            .map(|dest| BackendEntry {
                span: crate::source::Span::DUMMY,
                origin: crate::compiler2::BackendEntryOrigin::Branch,
                params: Vec::new(),
                captures: Vec::new(),
                physical_captures: Vec::new(),
                physical_params: Vec::new(),
                steps: vec![ProgramStep::Const {
                    value,
                    literal: crate::ground_value::GroundValue::Int(42),
                }],
                tail: BackendTail::Value { value, dest },
            })
            .collect(),
        generated: Vec::new(),
    };
    let executable = Rc::new(executable);
    let mut program = BackendProgram::empty(key.clone());
    program.add_executable(Rc::clone(&executable), world.types());
    let retained = backend_executable_ref(&program, world.types(), &key).expect("root boundary lookup");
    assert!(Rc::ptr_eq(&retained, &executable));
    let continuation = BackendContinuation {
        executable: retained,
        entry: first,
        env: HashMap::new(),
    };
    program.remove_executable(&key, world.types());
    assert!(
        program.executables().is_empty(),
        "no ordinal or key lookup can find the retained frame"
    );

    let transport = TransportStore::new();
    let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
    runtime.current_proc = runtime.process_ptr(1).expect("test process");
    let next = continue_backend_value(
        &mut runtime,
        &transport,
        &program,
        BackendBoundValue::Runtime(AnyValue::Int(0)),
        vec![continuation],
    )
    .expect("retained continuation");
    let BackendEvalTransition::Next(BackendEvalState::Entry {
        executable: resumed,
        entry,
        env,
        continuations,
    }) = next
    else {
        panic!("continuation must resume its local body")
    };
    assert!(Rc::ptr_eq(&resumed, &executable));
    runtime
        .enqueue_backend_local_entry(1, resumed, entry, env, continuations)
        .expect("queue retained resume");
    let resume = runtime.take_backend_resume(1).expect("queued resume");
    let outcome = run_backend_resume(
        &mut runtime,
        world.types_mut(),
        &transport,
        &crate::telemetry::ConfiguredTelemetry::new(),
        &program,
        &Module::default(),
        resume,
    )
    .expect("local transitions must execute the retained allocation even without root membership");
    assert!(matches!(outcome, BackendRunStep::Done(value) if value.as_i64() == Some(42)));
}

fn empty_backend_program() -> BackendProgram {
    BackendProgram::empty_for_test()
}

fn encode_for_layout(
    transport: &TransportStore,
    process: *mut Process,
    value: &BackendBoundValue,
    shape: ShapeId,
) -> Result<Vec<AnyValue>, String> {
    encode_with_layout(transport, process, value, TransportLayout::structural(shape))
}

fn encode_with_layout(
    transport: &TransportStore,
    process: *mut Process,
    value: &BackendBoundValue,
    layout: TransportLayout,
) -> Result<Vec<AnyValue>, String> {
    let mut encoded = Vec::new();
    encode_transport_layout(
        transport,
        &empty_backend_program(),
        process,
        value,
        layout,
        &mut encoded,
    )?;
    Ok(encoded)
}

fn tuple_shape(transport: &mut TransportStore, fields: &[ShapeId]) -> ShapeId {
    transport.interners_mut().intern_shape(ShapeDescr::Tuple(
        fields
            .iter()
            .copied()
            .map(TransportLayout::structural)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    ))
}

#[test]
fn tuple_decode_keeps_an_absent_parent_decomposed_and_a_carried_parent_boxed() {
    let mut transport = TransportStore::new();
    let mut types = crate::compiler2::Types::new();
    let int = types.int();
    let tuple_ty = types.tuple(&[int]);
    let lane = transport
        .interners_mut()
        .intern_lane(crate::compiler2::transport::LaneDescr {
            ty: int,
            class: crate::compiler2::transport::TransportClass::Value,
        });
    let tuple_lane = transport
        .interners_mut()
        .intern_lane(crate::compiler2::transport::LaneDescr {
            ty: tuple_ty,
            class: crate::compiler2::transport::TransportClass::Value,
        });
    let scalar = transport.interners_mut().intern_shape(ShapeDescr::Lane(lane));
    let tuple = transport
        .interners_mut()
        .intern_shape(ShapeDescr::Tuple(Box::new([TransportLayout {
            structural: scalar,
            carrier: TransportCarrier::ValueRef(lane),
        }])));
    let args = [AnyValue::Int(7)];
    let mut decomposed_index = 0;
    let decomposed = decode_transport_layout(
        &transport,
        &args,
        TransportLayout::structural(tuple),
        &mut decomposed_index,
    )
    .expect("an absent parent carrier preserves its recursive physical lanes");
    assert!(matches!(
        decomposed,
        BackendBoundValue::Transport { shape, lanes }
            if shape == tuple && matches!(lanes.as_slice(), [AnyValue::Int(7)])
    ));
    assert_eq!(decomposed_index, 1);

    let mut boxed_index = 0;
    let boxed = decode_transport_layout(
        &transport,
        &args,
        TransportLayout {
            structural: tuple,
            carrier: TransportCarrier::ValueRef(tuple_lane),
        },
        &mut boxed_index,
    )
    .expect("the parent carrier dominates its structural tuple");
    assert!(matches!(boxed, BackendBoundValue::Runtime(AnyValue::Int(7))));
    assert_eq!(boxed_index, 1);
}

#[test]
fn tuple_encoding_reprojects_same_arity_partial_transport_by_position() {
    let mut transport = TransportStore::new();
    let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
    let mut types = crate::compiler2::Types::new();
    let int = types.int();
    let inner_tuple_ty = types.tuple(&[int, int, int]);
    let outer_tuple_ty = types.tuple(&[int, inner_tuple_ty]);
    let lane = transport
        .interners_mut()
        .intern_lane(crate::compiler2::transport::LaneDescr {
            ty: int,
            class: crate::compiler2::transport::TransportClass::Value,
        });
    let scalar = transport.interners_mut().intern_shape(ShapeDescr::Lane(lane));
    let inner_tuple_lane = transport
        .interners_mut()
        .intern_lane(crate::compiler2::transport::LaneDescr {
            ty: inner_tuple_ty,
            class: crate::compiler2::transport::TransportClass::Value,
        });
    let inner_tuple_value = transport
        .interners_mut()
        .intern_shape(ShapeDescr::Lane(inner_tuple_lane));
    let outer_tuple_lane = transport
        .interners_mut()
        .intern_lane(crate::compiler2::transport::LaneDescr {
            ty: outer_tuple_ty,
            class: crate::compiler2::transport::TransportClass::Value,
        });
    let source_inner = tuple_shape(&mut transport, &[scalar, scalar, scalar]);
    let source = tuple_shape(&mut transport, &[nothing, source_inner]);
    let destination = tuple_shape(&mut transport, &[nothing, inner_tuple_value]);
    let selective_inner = tuple_shape(&mut transport, &[nothing, scalar, nothing]);
    let selective_destination = tuple_shape(&mut transport, &[nothing, selective_inner]);
    let required_absent_destination = tuple_shape(&mut transport, &[scalar, nothing]);
    let arity_mismatch_destination = tuple_shape(&mut transport, &[scalar]);
    let value = BackendBoundValue::Transport {
        shape: source,
        lanes: vec![AnyValue::Int(1), AnyValue::Int(2), AnyValue::Int(3)],
    };
    let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
    let mut process = runtime.take_process(1).expect("test process");
    let process = &mut process as *mut Process;
    let encoded = encode_for_layout(&transport, process, &value, destination)
        .expect("the destination erases the absent field before encoding the required inner tuple");

    assert_eq!(encoded.len(), 1);
    assert!(
        matches!(encoded[0], AnyValue::Ref(_)),
        "the inner tuple crosses as one value ref"
    );
    assert_eq!(transport.interners().lane(inner_tuple_lane).ty, inner_tuple_ty);
    let inner_fields = (0..3)
        .map(|index| {
            with_value_ref(process, encoded[0], "reprojected inner tuple", |tuple| {
                fz_struct_get_field_ref(process, tuple, index * 8)
            })
            .and_then(|word| interp_value_from_ref_word(word, "reprojected inner tuple field"))
            .and_then(|value| {
                value
                    .as_i64()
                    .ok_or_else(|| "inner tuple field was not an int".to_string())
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .expect("the destination lane should hold the materialized inner tuple");
    assert_eq!(inner_fields, [1, 2, 3]);

    let selectively_encoded = encode_for_layout(&transport, process, &value, selective_destination)
        .expect("a second consumer should independently select one nested source field");
    assert_eq!(selectively_encoded.len(), 1);
    assert_eq!(selectively_encoded[0].as_i64(), Some(2));

    let source_with_present_discard = tuple_shape(&mut transport, &[scalar, source_inner]);
    let value_with_present_discard = BackendBoundValue::Transport {
        shape: source_with_present_discard,
        lanes: vec![AnyValue::Int(99), AnyValue::Int(1), AnyValue::Int(2), AnyValue::Int(3)],
    };
    let present_discarded = encode_for_layout(&transport, process, &value_with_present_discard, destination)
        .expect("destination Nothing should discard a present source field");
    assert_eq!(present_discarded.len(), 1);
    assert!(matches!(present_discarded[0], AnyValue::Ref(_)));

    let whole_carrier = encode_with_layout(
        &transport,
        process,
        &value_with_present_discard,
        TransportLayout {
            structural: source_with_present_discard,
            carrier: TransportCarrier::ValueRef(outer_tuple_lane),
        },
    )
    .expect("a whole tuple should satisfy an outer ValueRef carrier");
    assert_eq!(whole_carrier.len(), 1);
    assert!(matches!(whole_carrier[0], AnyValue::Ref(_)));
    assert!(
        encode_with_layout(
            &transport,
            process,
            &value,
            TransportLayout {
                structural: destination,
                carrier: TransportCarrier::ValueRef(outer_tuple_lane),
            },
        )
        .is_err(),
        "same-arity reprojection must not bypass an outer ValueRef obligation",
    );

    let required_absent = encode_for_layout(&transport, process, &value, required_absent_destination)
        .expect_err("a required destination field cannot be invented from an absent source field");
    assert_eq!(required_absent, "backend value was absent and cannot be materialized");

    let arity_mismatch = encode_for_layout(&transport, process, &value, arity_mismatch_destination)
        .expect_err("arity-mismatched tuples retain outer materialization behavior");
    assert_eq!(arity_mismatch, "backend value was absent and cannot be materialized");

    let non_tuple = encode_runtime_value(
        &transport,
        &empty_backend_program(),
        process,
        &value,
        scalar,
        &mut Vec::new(),
    )
    .expect_err("non-tuple destinations retain outer materialization behavior");
    assert_eq!(non_tuple, "backend value was absent and cannot be materialized");

    let mut identical = Vec::new();
    encode_runtime_value(
        &transport,
        &empty_backend_program(),
        process,
        &value,
        source,
        &mut identical,
    )
    .expect("an identical layout keeps the direct lane-copy path");
    assert_eq!(
        identical.iter().map(|value| value.as_i64()).collect::<Vec<_>>(),
        [Some(1), Some(2), Some(3)]
    );
}

#[test]
fn direct_callable_lanes_cannot_be_published_as_a_runtime_environment() {
    let mut transport = TransportStore::new();
    let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
    let callable = transport
        .interners_mut()
        .intern_callable(crate::compiler2::transport::CallableDescr {
            function: Some(FunctionId::from_fn_id(FnId(123))),
            arity: 0,
            capture_layouts: Box::new([TransportLayout::structural(nothing)]),
        });
    let shape = transport.interners_mut().intern_shape(ShapeDescr::Callable(callable));
    let mut process = IrInterpRuntime::fresh_with_atoms(Vec::new()).take_process(1).unwrap();
    assert!(
        materialize_transport_value(&transport, &mut process, shape, &[]).is_err(),
        "an elided capture has no value to publish; the source construction must retain it",
    );
}

#[test]
fn backend_destructor_closure_unpack_errors_propagate() {
    let error = unpack_pending_dtor_closure(RuntimeAnyValue::null()).expect_err("non-closure destructor must fail");
    assert!(error.contains("backend dtor drain: invalid closure"), "{error}");
}

/// A direct closure edge names its target, so the call goes there whatever
/// the callee binding looks like: the binding is only where the captures
/// come from. A capture-free target asks for none, so an unbound callee and
/// an explicitly absent one are the same nothing and both reach it.
#[test]
fn a_direct_closure_edge_calls_its_named_target_from_what_the_caller_holds() {
    let mut edge = DirectClosureEdge::new(&[]);
    let key = edge.key.clone();

    assert!(matches!(
        edge.step(HashMap::new()),
        Ok(BackendEvalTransition::Next(BackendEvalState::Executable { executable: target, .. })) if target.key == key
    ));
    assert!(
        matches!(
            edge.step(HashMap::from([(edge.callee, BackendBoundValue::Absent)])),
            Ok(BackendEvalTransition::Next(BackendEvalState::Executable { executable: target, .. })) if target.key == key
        ),
        "a capture-free target asks for nothing, which is what an absent binding holds"
    );
}

/// A direct closure edge takes its target's captures out of the callee value.
/// A target that declares a capture lane and a callee value that carries none
/// is a plan that cannot be run, and the call says so rather than inventing a
/// capture.
#[test]
fn a_direct_closure_edge_refuses_a_callee_that_carries_none_of_the_target_captures() {
    let mut edge = DirectClosureEdge::new(&[Capture::Int]);

    let refused = edge.step(HashMap::from([(edge.callee, BackendBoundValue::Absent)]));

    assert!(
        matches!(&refused, Err(error) if error.contains("carries no capture 0")),
        "a declared capture the callee does not carry is a refusal, not an invented zero: {:?}",
        refused.err()
    );
}

/// The capture types a target may declare in these tests. Only the count and
/// the lane form matter here, so one type is enough to say "a capture".
#[derive(Clone, Copy)]
enum Capture {
    Int,
}

/// One executable entry whose tail is a direct closure call naming a target
/// that declares `captures`, with an interpreter ready to step it.
struct DirectClosureEdge {
    world: World,
    runtime: IrInterpRuntime,
    transport: TransportStore,
    tel: ConfiguredTelemetry,
    program: BackendProgram,
    executable: Rc<BackendExecutable>,
    entries: [BackendEntry; 1],
    key: ExecutableKey,
    callee: ValueId,
}

impl DirectClosureEdge {
    fn new(captures: &[Capture]) -> Self {
        let mut world = World::new();
        let int = world.types_mut().int();
        let capture_tys = captures
            .iter()
            .map(|capture| match capture {
                Capture::Int => int,
            })
            .collect::<Vec<Ty>>();
        let function = world.reference_function(ModuleId::GLOBAL, "target", 0);
        let key = ExecutableKey {
            activation: ActivationKey::from_inputs(RootId::for_test(0), function, &capture_tys, world.types_mut()),
            need: ExecutableNeed::Value,
        };
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let mut executable = BackendExecutable::for_test(key.clone(), int, nothing);
        Rc::make_mut(&mut executable.abi).semantic_inputs = capture_tys
            .iter()
            .enumerate()
            .map(|(semantic_index, ty)| {
                let lane = world.intern_lane(LaneDescr {
                    ty: *ty,
                    class: TransportClass::Value,
                });
                BackendSemanticInputLayout {
                    semantic_index,
                    layout: BackendValueLayout {
                        structural: world.intern_shape(ShapeDescr::Lane(lane)),
                        carrier: TransportCarrier::Absent,
                        tys: Box::new([*ty]),
                        reprs: Box::new([AbiValueRepr::RawInt]),
                    },
                }
            })
            .collect();
        let executable = Rc::new(executable);
        let mut program = BackendProgram::empty(key.clone());
        program.add_executable(executable.clone(), world.types());

        let callee = ValueId::from_u32(0);
        let entries = [BackendEntry {
            span: Span::DUMMY,
            origin: BackendEntryOrigin::Branch,
            params: Vec::new(),
            captures: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps: Vec::new(),
            tail: BackendTail::ClosureCall {
                value: ValueId::from_u32(1),
                callsite: CallSiteId::from_u32(0),
                callee,
                edge: ClosureCallEdge::Direct {
                    target: key.clone(),
                    capture_count: capture_tys.len(),
                },
                args: Vec::new(),
                dest: ControlDestination::Return,
                return_flow: None,
            },
        }];
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        runtime.current_proc = runtime.process_ptr(1).unwrap();
        Self {
            world,
            runtime,
            transport: TransportStore::new(),
            tel: ConfiguredTelemetry::new(),
            program,
            executable,
            entries,
            key,
            callee,
        }
    }

    fn step(&mut self, env: HashMap<ValueId, BackendBoundValue>) -> Result<BackendEvalTransition, String> {
        step_eval_entry(
            &mut self.runtime,
            self.world.types_mut(),
            &self.transport,
            &self.tel,
            &self.program,
            &Module::default(),
            &self.executable,
            &self.entries,
            ControlEntryId::from_u32(0),
            env,
            Vec::new(),
        )
    }
}
