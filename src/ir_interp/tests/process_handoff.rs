use crate::ir_interp::IrInterpRuntime;
use fz_runtime::exec_ctx::ExecCtx;
use fz_runtime::heap::SchemaRegistry;
use fz_runtime::process::Process;
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn take_process_detaches_scheduler_owned_pointers() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let process = Process::new(schemas);
    let mut runtime = IrInterpRuntime::with_process(process, &[]);
    let proc_ptr = runtime.process_ptr(1).expect("quoted-source runtime installs pid 1");
    let mut exec_ctx = ExecCtx::empty();
    unsafe {
        (*proc_ptr).ctx = &mut exec_ctx;
        (*proc_ptr).attach_heap_owner();
    }
    runtime.current_proc = proc_ptr;

    let process = runtime
        .take_process(1)
        .expect("runtime returns its quoted-source process");

    assert!(
        runtime.current_proc.is_null(),
        "runtime must drop the borrowed process pointer"
    );
    assert!(
        process.ctx.is_null(),
        "returned process must not keep a scheduler exec ctx"
    );
    assert!(
        !process.heap.has_owner(),
        "returned process must not keep an allocation-pressure owner backpointer"
    );
}
