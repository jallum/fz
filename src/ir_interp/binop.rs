use super::*;
use crate::fz_ir::{BinOp, FnId, UnOp};
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind, closure_captured_count, closure_fn_ptr};
use fz_runtime::ir_runtime::{fz_closure_get_capture_ref, fz_value_cmp_ref, fz_value_eq_ref, fz_value_eq_widening_ref};
use fz_runtime::process::Process;
use std::ptr::null_mut;

pub(super) fn eval_binop(proc: *mut Process, op: BinOp, a: AnyValue, b: AnyValue) -> Result<AnyValue, String> {
    macro_rules! int_arith {
        ($op:tt) => {
            match (a.as_i64(), b.as_i64()) {
                (Some(x), Some(y)) => Ok(AnyValue::Int(x $op y)),
                _ => {
                    let af = a.as_float().ok_or_else(|| "lhs is not numeric".to_string())?;
                    let bf = b.as_float().ok_or_else(|| "rhs is not numeric".to_string())?;
                    Ok(AnyValue::Float(af $op bf))
                }
            }
        };
    }
    // fz-5xp.18 — ordering asks the same runtime function native asks, the way
    // equality already asks `fz_value_eq_ref`. Two hand-rolled implementations
    // of one question is why the doors disagreed on `2 >= 1.0`.
    macro_rules! float_cmp {
        ($op:tt) => {{
            let ordering = interp_cmp(proc, a, b)?;
            Ok(interp_bool_value(ordering $op 0))
        }};
    }
    match op {
        BinOp::Add => int_arith!(+),
        BinOp::Sub => int_arith!(-),
        BinOp::Mul => int_arith!(*),
        BinOp::Div => int_arith!(/),
        BinOp::Mod => int_arith!(%),
        // `==` widens numerics; `===` does not. Two questions, two ops -- they
        // shared one op until fz-5xp.24, and a guard asked the wrong one.
        BinOp::Eq => Ok(interp_bool_value(interp_operator_eq(proc, a, b)?)),
        BinOp::Neq => Ok(interp_bool_value(!interp_operator_eq(proc, a, b)?)),
        BinOp::Identical => Ok(interp_bool_value(interp_value_eq(proc, a, b)?)),
        BinOp::NotIdentical => Ok(interp_bool_value(!interp_value_eq(proc, a, b)?)),
        BinOp::Lt => float_cmp!(<),
        BinOp::Le => float_cmp!(<=),
        BinOp::Gt => float_cmp!(>),
        BinOp::Ge => float_cmp!(>=),
    }
}

pub(super) fn eval_unop(op: UnOp, a: AnyValue) -> Result<AnyValue, String> {
    match op {
        UnOp::Neg => match a {
            AnyValue::Int(value) => Ok(AnyValue::Int(-value)),
            AnyValue::Float(value) => Ok(AnyValue::Float(-value)),
            _ => Err(format!("`-` on {}", a.render(null_mut()))),
        },
        UnOp::Not => Ok(interp_bool_value(!a.is_truthy())),
    }
}

/// The `==` OPERATOR: numbers compare by value, so `1 == 1.0` is true, and so
/// are `[1] == [1.0]` and `%{a: 1} == %{a: 1.0}`.
///
/// One implementation, shared by the equality intrinsics and by
/// `BinOp::Eq` -- which is what a GUARD lowers to. Two unboxed numbers skip the
/// boxing that forming a ref would cost; everything else recurses through the
/// runtime's widening comparator.
pub(super) fn interp_operator_eq(proc: *mut Process, a: AnyValue, b: AnyValue) -> Result<bool, String> {
    Ok(match (a, b) {
        (AnyValue::Int(left), AnyValue::Int(right)) => left == right,
        (AnyValue::Float(left), AnyValue::Float(right)) => left == right,
        (AnyValue::Int(integer), AnyValue::Float(float)) | (AnyValue::Float(float), AnyValue::Int(integer)) => {
            fz_runtime::term::compare_int_float(integer, float).is_eq()
        }
        _ => fz_value_eq_widening_ref(proc, a.as_ref_word(proc)?, b.as_ref_word(proc)?) != 0,
    })
}

/// Compare unboxed numeric lanes without allocating scalar adapters.
pub(super) fn interp_cmp(proc: *mut Process, a: AnyValue, b: AnyValue) -> Result<i64, String> {
    Ok(match (a, b) {
        (AnyValue::Int(left), AnyValue::Int(right)) => left.cmp(&right) as i64,
        (AnyValue::Float(left), AnyValue::Float(right)) => {
            left.partial_cmp(&right)
                .ok_or_else(|| "nonfinite float is not a language value".to_string())? as i64
        }
        (AnyValue::Int(left), AnyValue::Float(right)) => fz_runtime::term::compare_int_float(left, right) as i64,
        (AnyValue::Float(left), AnyValue::Int(right)) => {
            fz_runtime::term::compare_int_float(right, left).reverse() as i64
        }
        _ => fz_value_cmp_ref(proc, a.as_ref_word(proc)?, b.as_ref_word(proc)?),
    })
}

pub(super) fn interp_value_eq(proc: *mut Process, a: AnyValue, b: AnyValue) -> Result<bool, String> {
    match (a, b) {
        (AnyValue::Null, AnyValue::Null) => Ok(true),
        (AnyValue::Int(a), AnyValue::Int(b)) => Ok(a == b),
        // Structural identity, not `==`: a pinned match, `Enum.member?/2`, `--`
        // and a container element all ask whether two values are the SAME
        // value, and `1` is not `1.0`. The `==` operator widens elsewhere.
        (AnyValue::Int(_), AnyValue::Float(_)) | (AnyValue::Float(_), AnyValue::Int(_)) => Ok(false),
        // Identity, not `==`: `0.0` and `-0.0` are equal numbers but different
        // values, and `===` must say so.
        (AnyValue::Float(a), AnyValue::Float(b)) => Ok(a.to_bits() == b.to_bits()),
        (AnyValue::Atom(a), AnyValue::Atom(b)) => Ok(a == b),
        (AnyValue::EmptyList, AnyValue::EmptyList) => Ok(true),
        (AnyValue::Ref(a), AnyValue::Ref(b)) => Ok(fz_value_eq_ref(proc, a.raw_word(), b.raw_word()) != 0),
        (a, b) => Ok(fz_value_eq_ref(proc, a.as_ref_word(proc)?, b.as_ref_word(proc)?) != 0),
    }
}

/// Read an interp-side closure value. The interpreter stores the body FnId
/// in the closure code-pointer word; captures are normal env fields.
pub(super) fn unpack_closure(v: RuntimeAnyValue) -> Result<(FnId, Vec<AnyValue>), String> {
    let p = (v.kind() == ValueKind::CLOSURE)
        .then(|| v.heap_addr())
        .flatten()
        .ok_or_else(|| format!("call_closure on non-closure value: {:?}", v))?;
    let fn_id = FnId(unsafe { closure_fn_ptr(p) } as u32);
    let cap_count = unsafe { closure_captured_count(p) };
    let closure_ref = v.ref_word().raw_word();
    let captured: Vec<AnyValue> = (0..cap_count)
        .map(|i| {
            let value = fz_closure_get_capture_ref(closure_ref, i as u64);
            interp_value_from_ref_word(value, "call_closure capture")
        })
        .collect::<Result<_, _>>()?;
    Ok((fn_id, captured))
}

pub(super) fn unpack_callable(v: AnyValue, proc: *mut Process) -> Result<(FnId, Vec<AnyValue>), String> {
    match v {
        AnyValue::FnRef(fn_id, _, _) => Ok((fn_id, Vec::new())),
        other => unpack_closure(other.value(proc)?),
    }
}
