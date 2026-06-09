//! ArgRepr (per-spec ABI shape) and signature builders.

use super::*;
use crate::fz_ir::FnIr;
use crate::ir_planner::SpecPlan;
use crate::ir_planner::fn_types::SpecKey;
use crate::types::{KeySlot, Ty, Types, key_slots_to_tys};
use cranelift_codegen::ir::{self, AbiParam, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;

/// How a fz arg/return rides the Cranelift ABI for a native fn.
/// `ValueRef` is the generic strict-parts ABI: raw payload plus side-band
/// kind. Heap pointers preserve their strict low-4 object tag when they
/// must cross a one-word runtime helper seam. `RawInt` is an unshifted
/// int payload as i64; `RawF64` is a raw f64; `RawAtom` is an atom-id
/// payload as i64.
///
/// Per-spec param/return reprs are derived from `ir_planner`'s types:
/// float-only -> `RawF64`, int-only -> `RawInt`, atom-only -> `RawAtom`,
/// else `ValueRef`.
/// `build_fn_signature` picks the AbiParam type from the repr; `compile_fn`
/// populates `raw_*_vars` to match; call sites coerce at the seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ArgRepr {
    ValueRef,
    RawInt,
    RawF64,
    RawAtom,
    /// Raw i1 from a comparison or TypeTest whose var is in `if_only_conds`
    /// — the tagged form is never materialised unless tagged_get is called,
    /// which emits bool_to_fz lazily at the use site.
    Condition,
}

impl ArgRepr {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            ArgRepr::ValueRef => "ValueRef",
            ArgRepr::RawInt => "RawInt",
            ArgRepr::RawF64 => "RawF64",
            ArgRepr::RawAtom => "RawAtom",
            ArgRepr::Condition => "Condition",
        }
    }

    pub(crate) fn from_ty<T: Types<Ty = Ty>>(t: &mut T, d: &Ty) -> ArgRepr {
        if t.is_floating(d) {
            ArgRepr::RawF64
        } else if t.is_integer(d) {
            ArgRepr::RawInt
        } else {
            let atom = t.atom();
            if t.is_subtype(d, &atom) {
                ArgRepr::RawAtom
            } else {
                ArgRepr::ValueRef
            }
        }
    }

    // CLIF block params are always declared as i64. RawF64 (an actual f64
    // CLIF value) cannot cross a block-param boundary without a type error.
    // At block edges, only integers benefit from repr narrowing; floats must
    // remain in the generic ValueRef word across block params.
    pub(crate) fn for_block_param_ty<T: Types<Ty = Ty>>(t: &mut T, d: &Ty) -> ArgRepr {
        match Self::from_ty(t, d) {
            r @ (ArgRepr::RawInt | ArgRepr::RawAtom) => r,
            _ => ArgRepr::ValueRef,
        }
    }
    pub(crate) fn cl_type(&self) -> types::Type {
        match self {
            ArgRepr::RawF64 => types::F64,
            ArgRepr::Condition => unreachable!("Condition vars are never block/fn params"),
            _ => types::I64,
        }
    }

    pub(crate) fn abi_arity(&self) -> usize {
        match self {
            ArgRepr::ValueRef | ArgRepr::RawInt | ArgRepr::RawF64 | ArgRepr::RawAtom | ArgRepr::Condition => 1,
        }
    }

    /// Halt-cont singleton kind. 0=ValueRef, 1=RawInt, 2=RawF64, 3=RawAtom.
    pub(crate) fn halt_kind(&self) -> u32 {
        match self {
            ArgRepr::ValueRef => 0,
            ArgRepr::RawInt => 1,
            ArgRepr::RawF64 => 2,
            ArgRepr::RawAtom => 3,
            ArgRepr::Condition => unreachable!("Condition vars never reach halt-cont"),
        }
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

    pub(crate) fn capture_from_args(
        &self,
        _b: &mut FunctionBuilder<'_>,
        args: &[ir::Value],
        value_index: usize,
    ) -> CodegenValue {
        match self {
            MidFlightArgShape::Value(repr) => CodegenValue::from_abi_value(args[value_index], *repr),
            MidFlightArgShape::HeapRef => CodegenValue::AnyRef(args[value_index]),
        }
    }

    pub(crate) fn replay_from_capture<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, '_, M>,
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
            MidFlightArgShape::Value(ArgRepr::Condition) => {
                unreachable!("condition mid-flight arg")
            }
            MidFlightArgShape::HeapRef => out.push(value.value()),
        }
    }
}

pub(crate) fn push_repr_param(sig: &mut Signature, repr: ArgRepr) {
    sig.params.push(AbiParam::new(repr.cl_type()));
}

pub(crate) fn append_block_param_for_repr(b: &mut FunctionBuilder<'_>, block: ir::Block, repr: ArgRepr) {
    b.append_block_param(block, repr.cl_type());
}

pub(crate) fn take_repr_param(params: &[ir::Value], cursor: &mut usize, repr: ArgRepr) -> ir::Value {
    let value = params[*cursor];
    *cursor += repr.abi_arity();
    value
}

pub(crate) fn take_param_binding(
    b: &mut FunctionBuilder<'_>,
    params: &[ir::Value],
    cursor: &mut usize,
    repr: ArgRepr,
) -> CodegenValue {
    if repr == ArgRepr::ValueRef {
        let _ = b;
        CodegenValue::any_ref(take_repr_param(params, cursor, repr))
    } else {
        CodegenValue::from_abi_value(take_repr_param(params, cursor, repr), repr)
    }
}

/// Per-spec entry-param ArgReprs. Length matches the spec's entry block's
/// param count.
pub(crate) fn build_param_reprs<T: Types<Ty = Ty>>(t: &mut T, f: &FnIr, ft: &SpecPlan) -> Vec<ArgRepr> {
    let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    entry
        .params
        .iter()
        .map(|p| {
            let ty = ft.vars.get(p).cloned().unwrap_or_else(|| t.any());
            ArgRepr::from_ty(t, &ty)
        })
        .collect()
}

pub(crate) fn build_param_reprs_for_spec<T: Types<Ty = Ty>>(
    t: &mut T,
    f: &FnIr,
    ft: &SpecPlan,
    spec_key: &SpecKey,
    is_cont_fn: bool,
) -> Vec<ArgRepr> {
    if is_cont_fn && let Some(arity) = DemandAbi::new(spec_key).tuple_field_arity() {
        let mut reprs = Vec::new();
        if let Some(Some(tuple_ty)) = spec_key.input.first() {
            reprs.extend(
                t.tuple_projections(tuple_ty, arity)
                    .iter()
                    .map(|ty| ArgRepr::from_ty(t, ty)),
            );
        } else {
            let any = t.any();
            reprs.extend((0..arity).map(|_| ArgRepr::from_ty(t, &any)));
        }
        let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        for p in entry.params.iter().skip(1) {
            let ty = ft.vars.get(p).cloned().unwrap_or_else(|| t.any());
            reprs.push(ArgRepr::from_ty(t, &ty));
        }
        reprs
    } else {
        let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        entry
            .params
            .iter()
            .enumerate()
            .map(|(idx, p)| {
                spec_key
                    .input
                    .get(idx)
                    .and_then(|slot| slot.as_ref())
                    .or_else(|| ft.vars.get(p))
                    .map(|ty| ArgRepr::from_ty(t, ty))
                    .unwrap_or(ArgRepr::ValueRef)
            })
            .collect()
    }
}

pub(crate) fn codegen_key_to_tys<T: Types<Ty = Ty>>(t: &mut T, key: &[KeySlot]) -> Vec<Ty> {
    key_slots_to_tys(t, key)
}

/// Per-fn Cranelift Signature.
///
/// `is_native = false` -> uniform `(frame_ptr: i64, host_ctx: i64) -> i64`,
/// matching the body shape produced by `compile_fn` for trampoline-driven
/// fns: frame slots for entry params, emit_return writes into the cont
/// frame and returns the cont frame ptr to the trampoline.
///
/// `is_native = true` -> typed-arity signature reflecting the fn's entry
/// params + return. Each entry param's AbiParam type derives from its
/// `ArgRepr` (RawF64 -> `f64`, RawInt/ValueRef -> `i64`); the return
/// derives from `return_descr` the same way.
pub(crate) fn build_fn_signature(
    param_reprs: &[ArgRepr],
    is_native: bool,
    is_cont_fn: bool,
    closure_target_n_caps: Option<usize>,
    // When the cont fn is a ReceiveMatched clause body / guard, override
    // the default 1-input shape with bound_arity. After-bodies set this
    // to 0. `None` falls back to `(result, self)` for Call / CallClosure
    // continuations.
    cont_extras_override: Option<usize>,
) -> Signature {
    if !is_native {
        return build_uniform_sig();
    }
    if is_cont_fn {
        return build_cont_sig(param_reprs, cont_extras_override);
    }
    if let Some(n_caps) = closure_target_n_caps {
        return build_closure_target_sig(param_reprs, n_caps);
    }
    build_plain_native_sig(param_reprs)
}

/// Uniform (trampoline) signature: `(frame_ptr: i64, host_ctx: i64) -> i64`.
///
/// Uniform fns always include host_ctx — the trampoline ABI is fixed at
/// `(frame_ptr, host_ctx) -> i64`. The body produced by `compile_fn`
/// allocates frame slots for entry params, emit_return writes into the
/// cont frame and returns the cont frame ptr to the trampoline.
fn build_uniform_sig() -> Signature {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // frame_ptr
    sig.params.push(AbiParam::new(types::I64)); // host_ctx
    sig.returns.push(AbiParam::new(types::I64)); // next frame_ptr
    sig
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
/// lower to `return_call` (which the SystemV ABI does not permit).
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

/// Closure-target fn signature: `(args..., self:i64, cont:i64) tail`.
///
/// Captures (param_reprs[0..n_caps]) are NOT Cranelift params; the body
/// projects them from `self`. Args are param_reprs[n_caps..].
///
/// Uses the `Tail` calling convention so that recursive tail calls can
/// lower to `return_call`.
///
/// Closure-target ABI is structurally uniform ValueRef. The
/// indirect-dispatch seam can't carry typed return info to its caller;
/// the body coerces its narrow return to ValueRef at Term::Return.
fn build_closure_target_sig(param_reprs: &[ArgRepr], n_caps: usize) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    for r in &param_reprs[n_caps..] {
        push_repr_param(&mut sig, *r);
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

/// Plain native fn signature: `(args..., cont:i64) tail`,
/// return canonicalized to i64.
///
/// Uses the `Tail` calling convention so that recursive tail calls can
/// lower to `return_call` (which the SystemV ABI does not permit).
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
