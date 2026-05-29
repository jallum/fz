use super::*;
use crate::fz_ir::{BinOp, Const, FnId, UnOp};
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind};

pub(super) fn const_to_interp(c: &Const) -> AnyValue {
    match c {
        Const::Int(n) => AnyValue::Int(*n),
        Const::Atom(id) => AnyValue::Atom(*id),
        Const::Nil => interp_nil_value(),
        Const::True => interp_bool_value(true),
        Const::False => interp_bool_value(false),
        Const::Float(f) => AnyValue::Float(*f),
    }
}

pub(super) fn eval_binop(op: BinOp, a: AnyValue, b: AnyValue) -> Result<AnyValue, String> {
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
    macro_rules! float_cmp {
        ($op:tt) => {{
            let af = a.as_float().ok_or_else(|| "lhs is not numeric".to_string())?;
            let bf = b.as_float().ok_or_else(|| "rhs is not numeric".to_string())?;
            Ok(interp_bool_value(af $op bf))
        }};
    }
    match op {
        BinOp::Add => int_arith!(+),
        BinOp::Sub => int_arith!(-),
        BinOp::Mul => int_arith!(*),
        BinOp::Div => int_arith!(/),
        BinOp::Mod => int_arith!(%),
        BinOp::Eq => Ok(interp_bool_value(interp_value_eq(a, b)?)),
        BinOp::Neq => Ok(interp_bool_value(!interp_value_eq(a, b)?)),
        BinOp::Lt => float_cmp!(<),
        BinOp::Le => float_cmp!(<=),
        BinOp::Gt => float_cmp!(>),
        BinOp::Ge => float_cmp!(>=),
        BinOp::And => Ok(if !is_truthy(a) { a } else { b }),
        BinOp::Or => Ok(if is_truthy(a) { a } else { b }),
    }
}

pub(super) fn eval_unop(op: UnOp, a: AnyValue) -> Result<AnyValue, String> {
    match op {
        UnOp::Neg => match a {
            AnyValue::Int(value) => Ok(AnyValue::Int(-value)),
            AnyValue::Float(value) => Ok(AnyValue::Float(-value)),
            _ => Err(format!("`-` on {}", a.render(std::ptr::null_mut()))),
        },
        UnOp::Not => Ok(interp_bool_value(!is_truthy(a))),
    }
}

pub(super) fn interp_value_eq(a: AnyValue, b: AnyValue) -> Result<bool, String> {
    match (a, b) {
        (AnyValue::Null, AnyValue::Null) => Ok(true),
        (AnyValue::Int(a), AnyValue::Int(b)) => Ok(a == b),
        (AnyValue::Int(_), AnyValue::Float(_)) | (AnyValue::Float(_), AnyValue::Int(_)) => {
            Ok(false)
        }
        (AnyValue::Float(a), AnyValue::Float(b)) => Ok(a == b),
        (AnyValue::Atom(a), AnyValue::Atom(b)) => Ok(a == b),
        (AnyValue::EmptyList, AnyValue::EmptyList) => Ok(true),
        (AnyValue::Ref(a), AnyValue::Ref(b)) => {
            Ok(fz_runtime::ir_runtime::fz_value_eq_ref(a.raw_word(), b.raw_word()) != 0)
        }
        (a, b) => {
            Ok(fz_runtime::ir_runtime::fz_value_eq_ref(a.as_ref_word()?, b.as_ref_word()?) != 0)
        }
    }
}

/// Read an interp-side closure value. The interpreter stores the body FnId
/// in the closure code-pointer word; captures are normal env fields.
pub(super) fn unpack_closure(v: RuntimeAnyValue) -> Result<(FnId, Vec<AnyValue>), String> {
    let p = (v.kind() == ValueKind::CLOSURE)
        .then(|| v.heap_addr())
        .flatten()
        .ok_or_else(|| format!("call_closure on non-closure value: {:?}", v))?;
    let fn_id = FnId(unsafe { fz_runtime::any_value::closure_fn_ptr(p) } as u32);
    let cap_count = unsafe { fz_runtime::any_value::closure_captured_count(p) };
    let closure_ref = v.ref_word().raw_word();
    let captured: Vec<AnyValue> = (0..cap_count)
        .map(|i| {
            let value = fz_runtime::ir_runtime::fz_closure_get_capture_ref(closure_ref, i as u64);
            interp_value_from_ref_word(value, "call_closure capture")
        })
        .collect::<Result<_, _>>()?;
    Ok((fn_id, captured))
}
