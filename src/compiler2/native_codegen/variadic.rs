//! Calling a C variadic function from generated code.
//!
//! A C function declared `int printf(const char *fmt, ...)` has two argument
//! lists at the machine level: the fixed prefix, passed exactly as any other
//! C call passes it, and the variadic tail, whose placement the platform ABI
//! describes separately so that `va_arg` inside the callee can walk it. The
//! two lists do not always live in the same place, which is why a variadic
//! call is not simply a call with more arguments.
//!
//! Cranelift has no way to say "this call is variadic": a `Signature` is a
//! flat list of parameters with no marker separating the fixed prefix from the
//! tail (bytecodealliance/wasmtime#1030). So the variadic placement has to be
//! produced by choosing the parameter list, and that is what this module does.
//!
//! # The rule per target
//!
//! With variadic arguments restricted to integer and pointer values:
//!
//! * **x86-64 SysV** and **Linux AArch64** place variadic arguments exactly
//!   where ordinary arguments of the same types would go — the next argument
//!   registers, then the stack. An ordinary call whose signature lists the
//!   variadic values as extra integer parameters is therefore already the
//!   correct call.
//! * **Apple AArch64** departs from AAPCS64 here: variadic arguments never use
//!   registers. They are passed on the stack, each in its own 8-byte slot,
//!   starting at the stack pointer, and `va_arg` reads them from there.
//!
//! The Apple layout is produced by padding: extra integer parameters are added
//! after the fixed prefix until all eight integer argument registers (x0..x7)
//! are spoken for, so every parameter that follows is assigned to the stack.
//! The variadic values are those following parameters. This is exact rather
//! than approximate because an Apple variadic slot is 8 bytes, an integer or a
//! pointer parameter on the stack is 8 bytes, and both areas begin at the
//! stack pointer: the overflow area the padded ordinary call builds is
//! byte-for-byte the variadic area the callee expects. Fixed parameters in the
//! float bank (v0..v7) do not consume an integer register, so they are not
//! counted when deciding how much padding is needed.
//!
//! # Why integers and pointers only
//!
//! A float variadic argument would additionally require the caller to set
//! `%al` on x86-64 SysV to the number of vector registers used, which a
//! generated ordinary call has no way to express. fz refuses a float variadic
//! argument where the marshal class is resolved, so every call reaching this
//! module carries integer words only, and the generated call is correct on all
//! three targets.
//!
//! The strategy, and the measurement that it is the right one, come from
//! rustc's own Cranelift backend:
//! <https://github.com/rust-lang/rustc_codegen_cranelift/pull/1500>.

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, Signature, types};
use cranelift_codegen::isa::TargetIsa;
use cranelift_frontend::FunctionBuilder;
use target_lexicon::{Architecture, OperatingSystem, Triple};

/// The integer registers AArch64 passes arguments in: x0 through x7.
const AARCH64_INTEGER_ARG_REGISTERS: usize = 8;

/// Emit a call to the C variadic function at `callee_addr`.
///
/// `fixed` is the declaration's fixed prefix, each value paired with the
/// register lane its wire type travels in. `variadic` is the tail, every value
/// an integer word. `ret` is the result lane, or `None` for a call that
/// produces no value; the result is returned when there is one.
pub(crate) fn emit_variadic_c_call(
    b: &mut FunctionBuilder<'_>,
    isa: &dyn TargetIsa,
    callee_addr: ir::Value,
    fixed: &[(ir::Value, ir::Type)],
    variadic: &[ir::Value],
    ret: Option<ir::Type>,
) -> Option<ir::Value> {
    let mut sig = Signature::new(isa.default_call_conv());
    let mut args = Vec::with_capacity(fixed.len() + variadic.len() + AARCH64_INTEGER_ARG_REGISTERS);
    for (value, lane) in fixed {
        sig.params.push(AbiParam::new(*lane));
        args.push(*value);
    }
    let padding = integer_register_padding(isa.triple(), fixed);
    if padding > 0 {
        let unused = b.ins().iconst(types::I64, 0);
        for _ in 0..padding {
            sig.params.push(AbiParam::new(types::I64));
            args.push(unused);
        }
    }
    for value in variadic {
        sig.params.push(AbiParam::new(types::I64));
        args.push(*value);
    }
    sig.returns.extend(ret.map(AbiParam::new));
    let sig_ref = b.import_signature(sig);
    let call = b.ins().call_indirect(sig_ref, callee_addr, &args);
    ret.map(|_| b.inst_results(call)[0])
}

/// How many parameters have to be added after the fixed prefix so that the
/// variadic values land where the target expects to find them.
fn integer_register_padding(triple: &Triple, fixed: &[(ir::Value, ir::Type)]) -> usize {
    if !passes_variadic_arguments_on_the_stack(triple) {
        return 0;
    }
    let integer_params = fixed.iter().filter(|(_, lane)| *lane != types::F64).count();
    AARCH64_INTEGER_ARG_REGISTERS.saturating_sub(integer_params)
}

/// Apple's AArch64 platforms pass every variadic argument on the stack.
/// Everywhere else a variadic argument is passed like an ordinary one.
fn passes_variadic_arguments_on_the_stack(triple: &Triple) -> bool {
    matches!(triple.architecture, Architecture::Aarch64(_))
        && matches!(
            triple.operating_system,
            OperatingSystem::Darwin(_) | OperatingSystem::MacOSX(_)
        )
}

#[cfg(test)]
#[path = "variadic_test.rs"]
mod variadic_test;
