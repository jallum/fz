//! ArgRepr (per-spec ABI shape), extern wire lanes, and signature builders.

use super::*;
use crate::fz_ir::ExternTy;
use cranelift_codegen::ir::{self, AbiParam, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;

/// How a fz arg/return rides the Cranelift ABI for a native fn.
/// `ValueRef` is one `AnyValueRef` word: the kind in its high bits, the
/// address or payload below. `RawInt` is an unshifted int payload as i64;
/// `RawF64` is a raw f64; `RawAtom` is an atom-id payload as i64. `Stored` is
/// two i64 words: the word a container stores for the value and the value's
/// kind, read when the value is used.
///
/// Per-spec param/return/block reprs are copied from compiler2's native
/// handoff. Codegen chooses Cranelift ABI types from those facts; it does not
/// re-derive transport representation from local type evidence.
/// `build_fn_signature` picks the AbiParam type from the repr; `compile_fn`
/// populates `raw_*_vars` to match; call sites coerce at the seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ArgRepr {
    ValueRef,
    RawInt,
    RawF64,
    RawAtom,
    Stored,
    /// A raw condition (`I8`) from a comparison or type test whose var is in
    /// `if_only_conds`: only branches read it, so the tagged form is never
    /// built. It is also the form of a block parameter that only branches
    /// read; such a block has one predecessor and is not the entry, so no
    /// call, frame or continuation supplies the parameter.
    Condition,
}

impl ArgRepr {
    pub(crate) fn cl_type(&self) -> types::Type {
        match self {
            ArgRepr::RawF64 => types::F64,
            ArgRepr::Condition => types::I8,
            _ => types::I64,
        }
    }

    pub(crate) fn abi_arity(&self) -> usize {
        match self {
            ArgRepr::ValueRef | ArgRepr::RawInt | ArgRepr::RawF64 | ArgRepr::RawAtom | ArgRepr::Condition => 1,
            ArgRepr::Stored => 2,
        }
    }

    /// Halt continuation kind. 0=ValueRef, 1=RawInt, 2=RawF64, 3=RawAtom,
    /// 4=Stored.
    pub(crate) fn halt_kind(&self) -> u32 {
        match self {
            ArgRepr::ValueRef => 0,
            ArgRepr::RawInt => 1,
            ArgRepr::RawF64 => 2,
            ArgRepr::RawAtom => 3,
            ArgRepr::Stored => 4,
            ArgRepr::Condition => unreachable!("Condition vars never reach halt-cont"),
        }
    }
}

/// The machine lane an extern wire type rides in.
///
/// `ExternTy` lives in `fz_ir`, which is free of cranelift, so the lane is an
/// extension trait here beside `ArgRepr::cl_type`, which answers the same
/// question for fz's own calling convention.
pub(crate) trait ExternLane {
    /// `F64` rides the float register; `I32` is a half-width value in the
    /// integer register; every other value-carrying wire type is one
    /// integer-width word. `Unit` and `Never` carry no value, so they have no
    /// lane. The match is exhaustive on purpose: a new wire type has to say
    /// which bank and width it travels in rather than defaulting into the
    /// full integer word.
    fn lane(self) -> Option<types::Type>;

    /// The lanes one parameter of this class occupies in a C signature: two
    /// integer words for a `stored_value`, and its one lane for any other.
    fn param_lanes(self) -> impl Iterator<Item = types::Type>;
}

impl ExternLane for ExternTy {
    fn lane(self) -> Option<types::Type> {
        match self {
            ExternTy::F64 => Some(types::F64),
            ExternTy::I32 => Some(types::I32),
            ExternTy::I64
            | ExternTy::Opaque(_)
            | ExternTy::Bool
            | ExternTy::Any
            | ExternTy::Binary
            | ExternTy::BinaryCursor
            | ExternTy::StoredValue
            | ExternTy::CString => Some(types::I64),
            ExternTy::Unit | ExternTy::Never => None,
        }
    }

    fn param_lanes(self) -> impl Iterator<Item = types::Type> {
        let words = if self == ExternTy::StoredValue { 2 } else { 1 };
        // A parameter that carries no value has no lane; its marshal refuses
        // it, so the word it would occupy is never reached.
        std::iter::repeat_n(self.lane().unwrap_or(types::I64), words)
    }
}

/// The form a block parameter arrives in. A parameter only branches read
/// (`if_only_conds`) arrives as the raw condition; a parameter the native body
/// does not name travels as a value reference.
pub(crate) fn block_param_repr(
    native_body: &crate::compiler2::NativeBody,
    if_only_conds: &crate::fast_hash::HashSet<u32>,
    param: &crate::fz_ir::Var,
) -> ArgRepr {
    if if_only_conds.contains(&param.0) {
        return ArgRepr::Condition;
    }
    native_body
        .block_param_reprs
        .get(param)
        .copied()
        .map(arg_repr_from_compiler2)
        .unwrap_or(ArgRepr::ValueRef)
}

pub(crate) fn arg_repr_from_compiler2(repr: crate::compiler2::AbiValueRepr) -> ArgRepr {
    match repr {
        crate::compiler2::AbiValueRepr::ValueRef => ArgRepr::ValueRef,
        crate::compiler2::AbiValueRepr::RawInt => ArgRepr::RawInt,
        crate::compiler2::AbiValueRepr::RawF64 => ArgRepr::RawF64,
        crate::compiler2::AbiValueRepr::RawAtom => ArgRepr::RawAtom,
        crate::compiler2::AbiValueRepr::Stored => ArgRepr::Stored,
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum MidFlightArgShape {
    Value(ArgRepr),
    HeapRef,
}

impl MidFlightArgShape {
    pub(crate) fn abi_arity(&self) -> usize {
        match self {
            MidFlightArgShape::Value(repr) => repr.abi_arity(),
            MidFlightArgShape::HeapRef => 1,
        }
    }

    pub(crate) fn push_param(&self, sig: &mut Signature) {
        match self {
            MidFlightArgShape::Value(repr) => push_repr_param(sig, *repr),
            MidFlightArgShape::HeapRef => sig.params.push(AbiParam::new(types::I64)),
        }
    }

    pub(crate) fn capture_from_args(&self, args: &[ir::Value], value_index: usize) -> CodegenValue {
        match self {
            MidFlightArgShape::Value(repr) => CodegenValue::from_abi_values(&args[value_index..], *repr),
            MidFlightArgShape::HeapRef => CodegenValue::AnyRef(args[value_index]),
        }
    }

    pub(crate) fn replay_from_capture<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        value: CodegenValue,
        out: &mut Vec<ir::Value>,
    ) {
        match self {
            MidFlightArgShape::Value(ArgRepr::RawF64) => {
                out.push(body.value_raw_float(value));
            }
            MidFlightArgShape::Value(ArgRepr::RawInt) => {
                out.push(body.value_raw_int(value));
            }
            MidFlightArgShape::Value(ArgRepr::RawAtom) => {
                out.push(body.value_raw_atom(value));
            }
            MidFlightArgShape::Value(ArgRepr::ValueRef) => out.push(value.value()),
            MidFlightArgShape::Value(ArgRepr::Stored) => {
                let [word, kind] = body.value_stored_words(value);
                out.extend([word, kind]);
            }
            MidFlightArgShape::Value(ArgRepr::Condition) => {
                unreachable!("condition mid-flight arg")
            }
            MidFlightArgShape::HeapRef => out.push(value.value()),
        }
    }
}

pub(crate) fn push_repr_param(sig: &mut Signature, repr: ArgRepr) {
    for _ in 0..repr.abi_arity() {
        sig.params.push(AbiParam::new(repr.cl_type()));
    }
}

pub(crate) fn append_block_param_for_repr(b: &mut FunctionBuilder<'_>, block: ir::Block, repr: ArgRepr) {
    for _ in 0..repr.abi_arity() {
        b.append_block_param(block, repr.cl_type());
    }
}

/// The binding the next parameters of `params` spell in `repr`, advancing the
/// cursor past every word of it.
pub(crate) fn take_param_binding(params: &[ir::Value], cursor: &mut usize, repr: ArgRepr) -> CodegenValue {
    let binding = CodegenValue::from_abi_values(&params[*cursor..], repr);
    *cursor += repr.abi_arity();
    binding
}

/// A machine function's signature: the typed args, and the result lanes it
/// returns in registers, in `Tail`. It takes no continuation.
pub(crate) fn build_machine_fn_signature(param_reprs: &[ArgRepr], return_reprs: &[ArgRepr]) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    for repr in param_reprs {
        push_repr_param(&mut sig, *repr);
    }
    for repr in return_reprs {
        for _ in 0..repr.abi_arity() {
            sig.returns.push(AbiParam::new(repr.cl_type()));
        }
    }
    sig
}

/// Per-fn Cranelift Signature: the typed args plus the trailing continuation
/// (or, for a continuation fn, its `self`), in `Tail`.
pub(crate) fn build_fn_signature(
    param_reprs: &[ArgRepr],
    is_cont_fn: bool,
    // When the cont fn is a ReceiveMatched clause body / guard, override
    // the default 1-input shape with bound_arity. After-bodies set this
    // to 0. `None` falls back to `(result, self)` for Call / CallClosure
    // continuations.
    cont_extras_override: Option<usize>,
) -> Signature {
    if is_cont_fn {
        return build_cont_sig(param_reprs, cont_extras_override);
    }
    build_plain_native_sig(param_reprs)
}

/// Cont fn signature: `(result, self:i64) tail`, return canonicalized to i64.
///
/// `result` uses param_reprs[0]'s cl_type. Producer's Term::Return sig
/// matches via return_reprs[producer_spec_id]; typer's effective_return
/// walk ensures producer and consumer agree at the seam.
///
/// ReceiveMatched body/guard fns take N typed bound args up front
/// (override default of 1). After-body fns set override to 0 — captures
/// only, read from self+32+i*8.
///
/// Uses the `Tail` calling convention so that recursive tail calls can
/// lower to `return_call` (which a C calling convention does not permit).
/// Without TCO, count_100k_stays_bounded blows the stack.
///
/// Native fn return canonicalized to i64 regardless of ret_repr.
/// Term::Return is `return_call_indirect sig(i64,i64)->i64 tail`;
/// coercion happens at the return site.
fn build_cont_sig(param_reprs: &[ArgRepr], cont_extras_override: Option<usize>) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    let extras = cont_extras_override.unwrap_or(1);
    for r in param_reprs.iter().take(extras) {
        push_repr_param(&mut sig, *r);
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

/// Plain native fn signature: `(args..., cont:i64) tail`,
/// return canonicalized to i64.
///
/// Uses the `Tail` calling convention so that recursive tail calls can
/// lower to `return_call` (which a C calling convention does not permit).
/// Without TCO, count_100k_stays_bounded blows the stack.
///
/// Native fn return canonicalized to i64 regardless of ret_repr.
/// Term::Return is `return_call_indirect sig(i64,i64)->i64 tail`;
/// coercion happens at the return site.
fn build_plain_native_sig(param_reprs: &[ArgRepr]) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    for r in param_reprs {
        push_repr_param(&mut sig, *r);
    }
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    sig
}
