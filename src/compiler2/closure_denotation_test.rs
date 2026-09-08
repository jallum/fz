use std::cell::RefCell;
use std::rc::Rc;

use fz_runtime::any_value::{AnyValueRef, ClosureDenotationId, closure_denotation};
use fz_runtime::process::Process;

use super::{CodeSubmission, Compiler2, ExecutableNeed, RootId, RootSubmission};
use crate::ir_interp::{AnyValue, IrInterpRuntime, run_backend_entry_on_process};
use crate::telemetry::ConfiguredTelemetry;

fn submit_root(compiler: &mut Compiler2<ConfiguredTelemetry>, name: &str) -> RootId {
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: name.into(),
        arity: 0,
        need: ExecutableNeed::Value,
    })
}

fn tuple_denotations(process: &Process, tuple: AnyValueRef, count: usize) -> Vec<ClosureDenotationId> {
    (0..count)
        .map(|index| {
            let closure = process.heap.read_struct_field_ref(tuple, (index * 8) as u32).unwrap();
            unsafe { closure_denotation(closure.closure_addr().unwrap()) }
        })
        .collect()
}

#[test]
fn closure_denotation_survives_repeated_allocation_and_specialization_in_interp_and_jit() {
    for jit in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let observed = Rc::new(RefCell::new(Vec::new()));
        let captured = Rc::clone(&observed);
        tel.attach_raw_event2::<crate::ir_codegen::PidId, Process, _>(
            &["fz", "runtime", "process_exited"],
            move |_, _, _, _, process| {
                let tuple = *process.mailbox.front().expect("root sent its closures to itself");
                assert_ne!(
                    process
                        .heap
                        .read_struct_field_ref(tuple, 0)
                        .unwrap()
                        .closure_addr()
                        .unwrap(),
                    process
                        .heap
                        .read_struct_field_ref(tuple, 8)
                        .unwrap()
                        .closure_addr()
                        .unwrap(),
                    "the witness must exercise separate runtime closure allocations",
                );
                captured.borrow_mut().push(tuple_denotations(process, tuple, 4));
            },
        );
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("closure_denotation_specialization.fz".into()),
            text:
                "fn make(seed), do: fn () -> seed end\nfn main() do\n  send(self(), {make(self()), make(self()), make(:ok), fn () -> 42 end})\n  0\nend\n"
                    .into(),
        });
        let root = submit_root(&mut compiler, "main");
        if jit {
            compiler.run_root_jit(root).unwrap();
        } else {
            compiler.run_root_interp(root).unwrap();
        }
        let observed = observed.borrow();
        let [ids] = observed.as_slice() else {
            panic!("one root process must expose its sent closures: {observed:?}");
        };
        assert_eq!(ids[0], ids[1], "allocation cannot change a source lambda's denotation");
        assert_eq!(
            ids[0], ids[2],
            "capture specialization cannot change a source lambda's denotation"
        );
        assert_ne!(ids[0], ids[3], "a distinct lambda must retain a distinct denotation");
        let program = compiler.retained_backend_program(root);
        let make_executables = program
            .executables()
            .iter()
            .filter(|executable| {
                compiler
                    .world()
                    .function_ref(executable.key.activation.function)
                    .is_named("make")
            })
            .count();
        assert!(
            make_executables >= 2,
            "the witness must actually exercise distinct specializations"
        );
        assert!(
            program
                .construction_wrappers()
                .iter()
                .any(|wrapper| wrapper.denotation == ids[0])
        );
    }
}

#[test]
fn separate_backend_programs_keep_distinct_closures_on_one_process() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("closure_denotation_first_program.fz".into()),
        text: "fn zeta(), do: {fn () -> 1 end}\n".into(),
    });
    let first_root = submit_root(&mut compiler, "zeta");
    compiler.drive_root_backend_work_starts(first_root).unwrap();
    let first_program = compiler.retained_backend_program(first_root);
    let mut process = IrInterpRuntime::fresh_with_atoms(Vec::new()).take_process(1).unwrap();
    let (types, transport) = compiler.world_mut().types_mut_and_transport();
    let (returned_process, first) = run_backend_entry_on_process(
        types,
        transport,
        &tel,
        &fz_runtime::output::STDOUT_OUTPUT,
        &first_program,
        process,
        Vec::new(),
    );
    process = returned_process;
    let AnyValue::Ref(first_tuple) = first.unwrap() else {
        panic!("tuple result")
    };
    let first_id = tuple_denotations(&process, first_tuple, 1)[0];
    process.mailbox.push_back(first_tuple);

    compiler.submit_code(CodeSubmission {
        name: Some("closure_denotation_second_program.fz".into()),
        text: "fn alpha(), do: {fn () -> 2 end}\n".into(),
    });
    let second_root = submit_root(&mut compiler, "alpha");
    compiler.drive_root_backend_work_starts(second_root).unwrap();
    let second_program = compiler.retained_backend_program(second_root);
    let (types, transport) = compiler.world_mut().types_mut_and_transport();
    let (process, second) = run_backend_entry_on_process(
        types,
        transport,
        &tel,
        &fz_runtime::output::STDOUT_OUTPUT,
        &second_program,
        process,
        Vec::new(),
    );
    let AnyValue::Ref(second_tuple) = second.unwrap() else {
        panic!("tuple result")
    };
    let second_id = tuple_denotations(&process, second_tuple, 1)[0];
    assert_ne!(
        first_id, second_id,
        "separately published programs cannot reuse package-local closure identities"
    );
    assert_eq!(
        tuple_denotations(&process, *process.mailbox.front().unwrap(), 1)[0],
        first_id,
        "publishing an earlier-sorting function cannot renumber a live closure"
    );
}
