use super::super::receive::receive_dispatch_signature;
use super::*;
use crate::ir_codegen::backend::{AotBackend, JitBackend};

/// The host reaches each of these bodies through an `extern "C"` fn
/// pointer, so each signature is built in the convention the target names
/// for C. Writing one convention by hand is right only on the targets
/// where it happens to agree with the module's.
fn assert_host_called_signatures<M: cranelift_module::Module>(m: &mut M) {
    let target_c_conv = m.make_signature().call_conv;
    let sigs = [
        ("a receive dispatch fn", receive_dispatch_signature(m)),
        ("fz_drain_dtor_entry", drain_dtor_entry_signature(m)),
        ("fz_resume", resume_signature(m)),
        (
            "a uniform trampoline body",
            build_fn_signature(m, &[], false, false, None),
        ),
    ];
    for (name, sig) in sigs {
        assert_eq!(
            sig.call_conv, target_c_conv,
            "{name} is entered through a C fn pointer, so it takes the target's C convention"
        );
    }
}

#[test]
fn signatures_the_host_calls_by_address_use_the_target_convention() {
    let mut jit = JitBackend::new();
    assert_host_called_signatures(jit.module_mut());
    let mut aot = AotBackend::new("host_called_signatures");
    assert_host_called_signatures(aot.module_mut());
}
