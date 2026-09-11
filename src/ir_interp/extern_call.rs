use super::*;
use crate::compiler2::LoweredExtern;
use crate::extern_contract::runtime_symbol_abi;
use crate::fz_ir::{ExternAbi, ExternTy, Module};
use crate::telemetry::Telemetry;
use fz_runtime::extern_binary::{fz_binary_as_cstring, fz_binary_as_ptr};
use fz_runtime::extern_variadic::{
    fz_call_var_i64_cstring_i64_i64_to_i64, fz_call_var_i64_cstring_i64_to_i64, fz_extern_symbol_addr,
};
use fz_runtime::ir_runtime::{
    fz_atom_to_binary, fz_binary_concat, fz_binary_downcase, fz_binary_to_atom, fz_binary_upcase,
    fz_bitstring_byte_size, fz_bitstring_is_binary, fz_bitstring_utf8_prefix, fz_bitstring_valid_utf8,
    fz_brand_bitstring_as_utf8, fz_dbg_value, fz_float_to_binary, fz_integer_to_binary, fz_make_ref_raw, fz_map_count,
    fz_map_delete, fz_map_entry_key, fz_map_entry_value, fz_map_from_kv, fz_map_put_atom, fz_map_put_atom_ref,
    fz_map_put_float, fz_map_put_int, fz_map_put_ref, fz_op_div_ii_to_float, fz_op_neg_f, fz_op_neg_i,
    fz_process_heap_alloc_stats, fz_value_cmp_ref,
};
use fz_runtime::resource::fz_resource_test_print_dtor;
#[cfg(not(unix))]
use std::ffi::c_void;
use std::ffi::{CString, c_char};
use std::mem::transmute;
#[cfg(not(unix))]
use std::ptr::null_mut;
#[cfg(test)]
use std::sync::Mutex;
#[cfg(test)]
use std::sync::atomic::Ordering;

/// fz-5xp.18 — the typed comparison intrinsics `Kernel` selects once it knows
/// both operand kinds. Numeric lanes use the shared exact comparison without
/// boxing; composite values use the borrowed runtime term comparator.
///
/// Only ORDERING has typed intrinsics. Equality is total, so `Kernel` keeps a
/// single `fz_op_eq`/`fz_op_neq` and a single `===`/`!==`, handled above.
fn interp_typed_cmp_extern(symbol: &str) -> Option<crate::fz_ir::BinOp> {
    let (op, suffix) = symbol.strip_prefix("fz_op_")?.rsplit_once('_')?;
    if !matches!(suffix, "ii" | "ff" | "if" | "fi" | "bb") {
        return None;
    }
    match op {
        "lt" => Some(crate::fz_ir::BinOp::Lt),
        "lte" => Some(crate::fz_ir::BinOp::Le),
        "gt" => Some(crate::fz_ir::BinOp::Gt),
        "gte" => Some(crate::fz_ir::BinOp::Ge),
        _ => None,
    }
}

fn eval_interp_operator_extern(
    runtime: &mut IrInterpRuntime,
    symbol: &str,
    args: &[AnyValue],
) -> Result<Option<AnyValue>, String> {
    if let Some(op) = interp_typed_cmp_extern(symbol) {
        if args.len() != 2 {
            return Err(format!("{symbol}/2 got {} args", args.len()));
        }
        let proc = runtime.cur_proc();
        let ordering = interp_cmp(proc, args[0], args[1])?;
        let answer = match op {
            crate::fz_ir::BinOp::Lt => ordering < 0,
            crate::fz_ir::BinOp::Le => ordering <= 0,
            crate::fz_ir::BinOp::Gt => ordering > 0,
            crate::fz_ir::BinOp::Ge => ordering >= 0,
            other => return Err(format!("{symbol} is not a comparison: {other:?}")),
        };
        return Ok(Some(super::value::interp_bool_value(answer)));
    }
    // Operator equality widens numeric values; structural identity stays strict.
    if matches!(symbol, "fz_op_identical" | "fz_op_not_identical") {
        if args.len() != 2 {
            return Err(format!("{symbol}/2 got {} args", args.len()));
        }
        let same = super::binop::interp_value_eq(runtime.cur_proc(), args[0], args[1])?;
        let answer = if symbol == "fz_op_identical" { same } else { !same };
        return Ok(Some(super::value::interp_bool_value(answer)));
    }
    if matches!(symbol, "fz_op_eq" | "fz_op_neq") {
        if args.len() != 2 {
            return Err(format!("{symbol}/2 got {} args", args.len()));
        }
        let equal = super::binop::interp_operator_eq(runtime.cur_proc(), args[0], args[1])?;
        let answer = if symbol == "fz_op_eq" { equal } else { !equal };
        return Ok(Some(super::value::interp_bool_value(answer)));
    }
    Ok(None)
}

fn format_extern_shape(ret: ExternTy, fixed: &[ExternTy], variadic: &[ExternTy]) -> String {
    let fixed = fixed
        .iter()
        .map(|ty| format!("{:?}", ty))
        .collect::<Vec<_>>()
        .join(", ");
    let variadic = variadic
        .iter()
        .map(|ty| format!("{:?}", ty))
        .collect::<Vec<_>>()
        .join(", ");
    format!("ret={:?} fixed=[{}] variadic=[{}]", ret, fixed, variadic)
}

/// `fz_abi` selects what a declared parameter type MEANS, exactly as it does in
/// the backend: a C function taking `binary` wants a `*const u8` into the
/// bytes, an fz runtime helper wants the tagged value ref it works in.
fn marshal_arg(proc: *mut Process, value: AnyValue, ty: ExternTy, fz_abi: bool) -> Result<ArgWord, String> {
    Ok(match ty {
        ExternTy::I64 => ArgWord::Int(
            value
                .as_i64()
                .ok_or_else(|| "extern integer arg must be Int".to_string())? as u64,
        ),
        ExternTy::F64 => ArgWord::Float(
            value
                .as_float()
                .ok_or_else(|| "extern float arg must be Float".to_string())?,
        ),
        ExternTy::Binary | ExternTy::CString if fz_abi => ArgWord::Int(value.extern_arg_ref_word(proc)?),
        ExternTy::Binary => ArgWord::Int((unsafe { fz_binary_as_ptr(value.extern_arg_ref_word(proc)?) }) as u64),
        ExternTy::CString => ArgWord::Int((unsafe { fz_binary_as_cstring(value.extern_arg_ref_word(proc)?) }) as u64),
        ExternTy::Any => ArgWord::Int(value.extern_arg_ref_word(proc)?),
        ExternTy::Unit | ExternTy::Never => {
            return Err(format!("{:?} is not a valid extern argument marshal class", ty));
        }
    })
}

// The typed arithmetic `Kernel` selects once it knows both operand kinds.
//
// Each one's Rust signature is EXACTLY its declared wire types, because that is
// what the C ABI reads: a `float` parameter arrives in the float register bank.
// These used to take and return `u64` and bit-pun the floats, which worked only
// while the interpreter's dispatcher bit-punned them too -- two disagreements
// that cancelled. Once the dispatcher started passing a float as a float, a
// shim still reading the integer bank got garbage.
unsafe extern "C" fn fz_op_add_ii(a: u64, b: u64) -> u64 {
    ((a as i64) + (b as i64)) as u64
}

unsafe extern "C" fn fz_op_add_if(a: u64, b: f64) -> f64 {
    ((a as i64) as f64) + b
}

unsafe extern "C" fn fz_op_add_ff(a: f64, b: f64) -> f64 {
    a + b
}

unsafe extern "C" fn fz_op_sub_ii(a: u64, b: u64) -> u64 {
    ((a as i64) - (b as i64)) as u64
}

unsafe extern "C" fn fz_op_sub_if(a: u64, b: f64) -> f64 {
    ((a as i64) as f64) - b
}

unsafe extern "C" fn fz_op_sub_fi(a: f64, b: u64) -> f64 {
    a - ((b as i64) as f64)
}

unsafe extern "C" fn fz_op_sub_ff(a: f64, b: f64) -> f64 {
    a - b
}

unsafe extern "C" fn fz_op_mul_ii(a: u64, b: u64) -> u64 {
    ((a as i64) * (b as i64)) as u64
}

unsafe extern "C" fn fz_op_mul_if(a: u64, b: f64) -> f64 {
    ((a as i64) as f64) * b
}

unsafe extern "C" fn fz_op_mul_ff(a: f64, b: f64) -> f64 {
    a * b
}

unsafe extern "C" fn fz_op_div_ii(a: u64, b: u64) -> u64 {
    ((a as i64) / (b as i64)) as u64
}

unsafe extern "C" fn fz_op_div_if(a: u64, b: f64) -> f64 {
    ((a as i64) as f64) / b
}

unsafe extern "C" fn fz_op_div_fi(a: f64, b: u64) -> f64 {
    a / ((b as i64) as f64)
}

unsafe extern "C" fn fz_op_div_ff(a: f64, b: f64) -> f64 {
    a / b
}

unsafe extern "C" fn fz_op_rem_ii(a: u64, b: u64) -> u64 {
    ((a as i64) % (b as i64)) as u64
}

unsafe extern "C" fn fz_op_rem_if(a: u64, b: f64) -> f64 {
    ((a as i64) as f64) % b
}

unsafe extern "C" fn fz_op_rem_fi(a: f64, b: u64) -> f64 {
    a % ((b as i64) as f64)
}

unsafe extern "C" fn fz_op_rem_ff(a: f64, b: f64) -> f64 {
    a % b
}

pub(super) fn call_lowered_extern<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &crate::compiler2::transport::TransportStore,
    tel: &T,
    program: &crate::compiler2::BackendProgram,
    module: &Module,
    signature: &LoweredExtern,
    marshals: Option<&[ExternTy]>,
    args: &[AnyValue],
) -> Result<AnyValue, String> {
    if let Some(value) = eval_interp_operator_extern(runtime, signature.symbol.as_str(), args)? {
        return Ok(value);
    }
    match signature.symbol.as_str() {
        "fz_panic" => {
            if args.len() != 1 {
                return Err(format!("fz_panic/1 got {} args", args.len()));
            }
            return Err(format!("fz panic: {}", args[0].render(runtime.cur_proc())));
        }
        "fz_map_count" => {
            if args.len() != 1 {
                return Err(format!("fz_map_count/1 got {} args", args.len()));
            }
            let ref_word = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            return Ok(AnyValue::Int(fz_map_count(ref_word)));
        }
        "fz_map_entry_key" => {
            if args.len() != 2 {
                return Err(format!("fz_map_entry_key/2 got {} args", args.len()));
            }
            let map_ref = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            let index = args[1]
                .as_i64()
                .ok_or_else(|| "fz_map_entry_key/2 index must be integer".to_string())?;
            return interp_value_from_extern_ref_word(fz_map_entry_key(map_ref, index));
        }
        "fz_map_entry_value" => {
            if args.len() != 2 {
                return Err(format!("fz_map_entry_value/2 got {} args", args.len()));
            }
            let map_ref = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            let index = args[1]
                .as_i64()
                .ok_or_else(|| "fz_map_entry_value/2 index must be integer".to_string())?;
            return interp_value_from_extern_ref_word(fz_map_entry_value(map_ref, index));
        }
        "fz_spawn" | "fz_spawn_opt" => {
            if args.is_empty() {
                return Err(format!("{}/1+ got 0 args", signature.symbol));
            }
            let (fn_id, captured) = super::binop::unpack_callable(args[0], runtime.cur_proc())?;
            let (target, inputs) = super::backend::construction_wrapper_invocation(
                runtime,
                types,
                transport,
                program,
                module,
                fn_id,
                &captured,
                &[],
            )?;
            let pid = runtime.spawn_backend(target, inputs)?;
            return Ok(AnyValue::Int(pid as i64));
        }
        "fz_self" => {
            return Ok(AnyValue::Int(unsafe { &*runtime.cur_proc() }.pid as i64));
        }
        "fz_make_ref" => {
            let id = fz_make_ref_raw();
            return Ok(AnyValue::Int(id as i64));
        }
        "fz_send" => {
            if args.len() != 2 {
                return Err(format!("fz_send/2 got {} args", args.len()));
            }
            let receiver = args[0].as_i64().ok_or_else(|| "send/2: pid must be Int".to_string())? as u32;
            runtime.send_opaque(types, transport, tel, program, module, &receiver, args[1])?;
            return Ok(args[1]);
        }
        "fz_make_resource" => {
            if args.len() != 2 {
                return Err(format!("fz_make_resource/2 got {} args", args.len()));
            }
            let payload = args[0]
                .as_i64()
                .ok_or_else(|| "make_resource/2: payload must be integer".to_string())?;
            return super::make_resource_in_current_process(
                runtime.cur_proc(),
                module,
                payload,
                args[1].value(runtime.cur_proc())?,
            )
            .map(interp_value_from_slot);
        }
        _ => {}
    }

    if signature.variadic {
        let arg_tys = marshals.ok_or_else(|| {
            format!(
                "variadic extern `{}` has unresolved marshal metadata in backend execution",
                signature.symbol
            )
        })?;
        if arg_tys.len() != args.len() {
            return Err(format!(
                "variadic extern `{}` expected {} marshal classes but saw {} args",
                signature.symbol,
                arg_tys.len(),
                args.len()
            ));
        }
        let fixed_count = signature.params.len();
        let fixed = &arg_tys[..fixed_count];
        let variadic = &arg_tys[fixed_count..];
        let cname = CString::new(signature.symbol.as_str()).map_err(|e| format!("bad symbol name: {e}"))?;
        let fp = unsafe { fz_extern_symbol_addr(cname.as_ptr()) };
        if fp == 0 {
            return Err(format!("dlsym: symbol `{}` not found", signature.symbol));
        }
        // Every dispatcher below is an all-integer shape (`cstring` and `i64`),
        // which is what makes indexing these as words correct here.
        let raw_args: Vec<u64> = args
            .iter()
            .zip(arg_tys.iter().copied())
            .map(|(value, ty)| marshal_arg(runtime.cur_proc(), *value, ty, false).map(ArgWord::int))
            .collect::<Result<_, _>>()?;
        let ret = match (signature.ret, fixed, variadic) {
            (ExternTy::I64, [ExternTy::CString, ExternTy::I64], [ExternTy::I64]) => unsafe {
                fz_call_var_i64_cstring_i64_i64_to_i64(
                    fp,
                    raw_args[0] as *const c_char,
                    raw_args[1] as i64,
                    raw_args[2] as i64,
                ) as u64
            },
            (ExternTy::I64, [ExternTy::CString], [ExternTy::I64]) => unsafe {
                fz_call_var_i64_cstring_i64_to_i64(fp, raw_args[0] as *const c_char, raw_args[1] as i64) as u64
            },
            _ => {
                return Err(format!(
                    "unsupported variadic extern shape: {}",
                    format_extern_shape(signature.ret, fixed, variadic)
                ));
            }
        };
        return match signature.ret {
            ExternTy::I64 => Ok(AnyValue::Int(ret as i64)),
            ExternTy::Any | ExternTy::Binary | ExternTy::CString => interp_value_from_extern_ref_word(ret),
            ExternTy::Unit | ExternTy::Never => Ok(interp_nil_value()),
            // Every dispatcher above returns `I64`; a float-returning variadic
            // is refused as an unsupported shape before reaching here. Reading
            // `ret` as float bits would be exactly the integer-bank mistake the
            // fixed-arity path was just fixed for, so it is refused rather than
            // written out and left to look correct.
            ExternTy::F64 => Err(format!(
                "variadic extern `{}` returns a float, which no dispatcher provides",
                signature.symbol
            )),
        };
    }

    let fp = resolve_symbol(&signature.symbol, signature.abi)?;
    // An `extern "fz"` helper receives the current process as an implicit first
    // argument, declared rather than matched by name.
    let fz_abi = signature.abi.takes_process();
    let mut raw_args: Vec<ArgWord> = Vec::with_capacity(args.len() + 1);
    if fz_abi {
        raw_args.push(ArgWord::Int(runtime.cur_proc() as u64));
    }
    for (value, ty) in args.iter().zip(signature.params.iter().copied()) {
        raw_args.push(marshal_arg(runtime.cur_proc(), *value, ty, fz_abi)?);
    }
    // `dispatch_fn_*` transmute to a concrete fn type, so the interpreter has a
    // ceiling the backend does not. Reported here, where the declaration is
    // still in hand, rather than panicking inside the dispatch:
    // the process word spends one of the slots, so an `extern "fz"` reaches the
    // ceiling one declared parameter sooner and the count alone would mislead.
    if raw_args.len() > MAX_INTERP_EXTERN_ARGS {
        return Err(format!(
            "extern `{}` passes {} argument(s){} to the interpreter, which supports at most {}",
            signature.symbol,
            raw_args.len(),
            if fz_abi { " including the implicit process" } else { "" },
            MAX_INTERP_EXTERN_ARGS,
        ));
    }
    // The declared RETURN picks the lane the answer comes back in. A float is
    // returned in the float bank, so reading the integer return register gave
    // back whatever happened to be there -- for `libc::sqrt` that was the
    // argument's own bits, which looked exactly like a plausible answer.
    match signature.ret {
        ExternTy::F64 => Ok(AnyValue::Float(unsafe { dispatch_fn_returning_float(fp, &raw_args) })),
        ExternTy::Unit | ExternTy::Never => {
            unsafe { dispatch_fn_void(fp, &raw_args) };
            Ok(interp_nil_value())
        }
        ExternTy::I64 => Ok(AnyValue::Int(unsafe { dispatch_fn_returning_int(fp, &raw_args) } as i64)),
        ExternTy::Any | ExternTy::Binary | ExternTy::CString => {
            interp_value_from_extern_ref_word(unsafe { dispatch_fn_returning_int(fp, &raw_args) })
        }
    }
}

/// How many machine words the `dispatch_fn_*` family can forward. They
/// transmute to a concrete `extern "C" fn` type, so the enumerated shapes are
/// the limit -- and a shape is an arity TIMES an assignment of its parameters
/// to the integer and float register banks. An `extern "fz"` spends one slot on
/// the implicit process word.
const MAX_INTERP_EXTERN_ARGS: usize = 4;

fn abi_mismatch(name: &str, declared: ExternAbi, provided: ExternAbi) -> String {
    format!(
        "extern `{name}` is declared `extern \"{declared}\"` but the fz runtime provides it \
         with the `{provided}` ABI; the two disagree about the implicit process argument \
         and about how a binary is passed"
    )
}

/// Every symbol the runtime declares a convention for must be one the
/// interpreter can actually reach. The convention and the address are separate
/// structures -- one is pure data the front end reads, the other needs the
/// linked Rust items -- so this is where they are held together. Drift becomes
/// a test failure instead of a `dlsym: symbol not found` at run time.
#[cfg(test)]
mod address_book_test {
    use super::*;
    use crate::extern_contract::RUNTIME_SYMBOLS;

    #[test]
    fn every_declared_runtime_symbol_resolves() {
        let missing: Vec<&str> = RUNTIME_SYMBOLS
            .iter()
            .filter(|(name, abi)| resolve_symbol(name, *abi).is_err())
            .map(|(name, _)| *name)
            .collect();
        assert!(
            missing.is_empty(),
            "the runtime declares a convention for these symbols but the interpreter cannot \
             resolve them, so the two structures have drifted: {missing:?}",
        );
    }

    #[test]
    fn a_declaration_that_contradicts_the_runtime_is_refused() {
        for (name, provided) in RUNTIME_SYMBOLS {
            let lie = match provided {
                ExternAbi::C => ExternAbi::Fz,
                ExternAbi::Fz => ExternAbi::C,
            };
            let error = resolve_symbol(name, lie)
                .err()
                .unwrap_or_else(|| panic!("`{name}` declared `{lie}` should not resolve"));
            // Specifically the mismatch, not some other refusal that happens to
            // fire first -- otherwise a `Fz` lie could pass on the dlsym guard's
            // "runtime provides no such symbol" message and leave the mismatch
            // check itself untested.
            assert!(
                error.contains(name) && error.contains("provides it with"),
                "`{name}` declared `{lie}` should be refused AS A MISMATCH: {error}",
            );
        }
    }

    /// The reverse direction -- an address present with no declared convention
    /// -- is refused rather than transmuted. It is unreachable while the two
    /// structures agree, which is what the tests above hold. This pins the
    /// premise: a symbol fz owns but does NOT claim gets no check at all, which
    /// is fz-5xp.32.
    #[test]
    fn a_runtime_symbol_outside_the_table_is_unclaimed() {
        assert!(
            runtime_symbol_abi("fz_alloc_frame").is_none(),
            "fz-5xp.32: the claim set is deliberately not yet closed; if this now \
             resolves, the table grew and the foreign-declaration hole may be closed",
        );
    }
}

/// The address to call for a declared extern symbol.
///
/// Checks the built-in address book first: the runtime's own symbols are
/// registered there so the interpreter finds them even when the runtime is
/// statically linked and `dlsym(RTLD_DEFAULT)` cannot reach them. Falls back
/// to dlsym only for the C ABI -- an address found by name says nothing about
/// whether the function wants a process word.
pub(super) fn resolve_symbol(name: &str, abi: ExternAbi) -> Result<*const (), String> {
    // Address book: the runtime symbols the interpreter must be able to reach.
    // These Rust functions are linked into the binary; using their address
    // directly avoids relying on dlsym visibility, which is unreliable for
    // statically-linked rlibs. Their CONVENTIONS live in `runtime_symbol_abi`,
    // which the front end consults too, so there is one answer per symbol.
    #[cfg(test)]
    if let Some(fp) = tests_support::lookup_test_symbol(name) {
        return match abi {
            ExternAbi::C => Ok(fp),
            ExternAbi::Fz => Err(abi_mismatch(name, abi, ExternAbi::C)),
        };
    }

    let native: Option<*const ()> = match name {
        // fz_panic never returns, so it stays special-cased in call_extern
        // above and must never be resolved as a plain symbol here. The process
        // intrinsics that DO return a value are declared `extern "fz"` and go
        // through the generic path, which supplies the leading process
        // argument from the declaration.
        "fz_dbg_value" => Some(fz_dbg_value as *const ()),
        "fz_process_heap_alloc_stats" => Some(fz_process_heap_alloc_stats as *const ()),
        // fz-swt.11 — fixture/test dtor exported from the runtime crate.
        // Bound here so interp-leg invocations of fixtures using this
        // symbol (e.g. when `fz interp` is run by hand on the AOT-only
        // fixture) reach the same Rust fn the AOT-linked binary uses.
        "fz_resource_test_print_dtor" => Some(fz_resource_test_print_dtor as *const ()),
        // fz-axu.14 (R1) — utf8 runtime support. Bound here so the
        // interp leg of the matrix can resolve them without relying on
        // dlsym; statically-linked rlibs don't expose these via
        // RTLD_DEFAULT on Linux.
        // fz-5xp.8 — the total term order, which the cross-type comparison
        // clauses in `Kernel` are written in terms of.
        "fz_value_cmp_ref" => Some(fz_value_cmp_ref as *const ()),
        "fz_binary_downcase" => Some(fz_binary_downcase as *const ()),
        "fz_binary_to_atom" => Some(fz_binary_to_atom as *const ()),
        "fz_binary_upcase" => Some(fz_binary_upcase as *const ()),
        "fz_bitstring_byte_size" => Some(fz_bitstring_byte_size as *const ()),
        "fz_bitstring_is_binary" => Some(fz_bitstring_is_binary as *const ()),
        "fz_bitstring_valid_utf8" => Some(fz_bitstring_valid_utf8 as *const ()),
        "fz_bitstring_utf8_prefix" => Some(fz_bitstring_utf8_prefix as *const ()),
        "fz_brand_bitstring_as_utf8" => Some(fz_brand_bitstring_as_utf8 as *const ()),
        "fz_binary_concat" => Some(fz_binary_concat as *const ()),
        "fz_atom_to_binary" => Some(fz_atom_to_binary as *const ()),
        "fz_integer_to_binary" => Some(fz_integer_to_binary as *const ()),
        "fz_float_to_binary" => Some(fz_float_to_binary as *const ()),
        "fz_op_add_ii" => Some(fz_op_add_ii as *const ()),
        "fz_op_add_if" => Some(fz_op_add_if as *const ()),
        "fz_op_add_ff" => Some(fz_op_add_ff as *const ()),
        "fz_op_sub_ii" => Some(fz_op_sub_ii as *const ()),
        "fz_op_sub_if" => Some(fz_op_sub_if as *const ()),
        "fz_op_sub_fi" => Some(fz_op_sub_fi as *const ()),
        "fz_op_sub_ff" => Some(fz_op_sub_ff as *const ()),
        "fz_op_neg_i" => Some(fz_op_neg_i as *const ()),
        "fz_op_neg_f" => Some(fz_op_neg_f as *const ()),
        "fz_op_mul_ii" => Some(fz_op_mul_ii as *const ()),
        "fz_op_mul_if" => Some(fz_op_mul_if as *const ()),
        "fz_op_mul_ff" => Some(fz_op_mul_ff as *const ()),
        "fz_op_div_ii" => Some(fz_op_div_ii as *const ()),
        "fz_op_div_ii_to_float" => Some(fz_op_div_ii_to_float as *const ()),
        "fz_op_div_if" => Some(fz_op_div_if as *const ()),
        "fz_op_div_fi" => Some(fz_op_div_fi as *const ()),
        "fz_op_div_ff" => Some(fz_op_div_ff as *const ()),
        "fz_op_rem_ii" => Some(fz_op_rem_ii as *const ()),
        "fz_op_rem_if" => Some(fz_op_rem_if as *const ()),
        "fz_op_rem_fi" => Some(fz_op_rem_fi as *const ()),
        "fz_op_rem_ff" => Some(fz_op_rem_ff as *const ()),
        "fz_map_delete" => Some(fz_map_delete as *const ()),
        "fz_map_from_kv" => Some(fz_map_from_kv as *const ()),
        "fz_map_put_ref" => Some(fz_map_put_ref as *const ()),
        "fz_map_put_int" => Some(fz_map_put_int as *const ()),
        "fz_map_put_float" => Some(fz_map_put_float as *const ()),
        "fz_map_put_atom" => Some(fz_map_put_atom as *const ()),
        "fz_map_put_atom_ref" => Some(fz_map_put_atom_ref as *const ()),
        "fz_map_count" => Some(fz_map_count as *const ()),
        "fz_map_entry_key" => Some(fz_map_entry_key as *const ()),
        "fz_map_entry_value" => Some(fz_map_entry_value as *const ()),
        _ => None,
    };
    if let Some(fp) = native {
        // Defence-in-depth around the transmute below. `resolve_extern_abi`
        // already refused a declaration that disagrees with the runtime, in
        // the shared front end so that every door refuses it; this is the last
        // gate before an address becomes a concrete fn type.
        match runtime_symbol_abi(name) {
            Some(provided) if provided != abi => return Err(abi_mismatch(name, abi, provided)),
            Some(_) => {}
            None => {
                return Err(format!(
                    "extern `{name}` is in the interpreter's address table but the runtime \
                     declares no convention for it"
                ));
            }
        }
        return Ok(fp);
    }
    // Fallback: dlsym for user-declared externs not in the native table. Only
    // the C ABI can be satisfied this way -- an address found by name says
    // nothing about whether the function wants a process word, and the `fz`
    // ABI is reserved to the runtime library, whose symbols are all in the
    // table above.
    if abi.takes_process() {
        return Err(format!(
            "extern `{}` declares the `fz` ABI, but the fz runtime provides no such symbol",
            name
        ));
    }
    // Through `fz_extern_symbol_addr`, not a raw dlsym: it is the ONE place
    // that knows where a foreign symbol can live, including the standard C
    // libraries it opens when the loaded scope does not already have them.
    // A raw `dlsym(RTLD_DEFAULT, ..)` here made this door the odd one out --
    // `libc::sqrt` resolved on the JIT and failed on interp (fz-5xp.59).
    let cname = CString::new(name).map_err(|e| format!("bad symbol name: {}", e))?;
    let addr = unsafe { fz_extern_symbol_addr(cname.as_ptr()) };
    if addr == 0 {
        return Err(format!("dlsym: symbol `{}` not found", name));
    }
    Ok(addr as *const ())
}

/// One extern argument, in the register bank the C ABI passes it in.
///
/// Integers and floats travel in DIFFERENT banks, so the fn type the address is
/// transmuted to has to name each parameter's bank exactly. Handing an `f64`'s
/// bits across as a `u64` puts them in the integer bank, where a callee reading
/// `xmm0`/`d0` never looks -- which is why `libc::sqrt(9.0)` used to answer
/// `9.0`: the argument never arrived, and the caller read its own bits back out
/// of the integer return register.
#[derive(Clone, Copy, Debug)]
enum ArgWord {
    Int(u64),
    Float(f64),
}

impl ArgWord {
    /// Total, though the cross cases cannot arise: the shape dispatched on is
    /// derived from these same values by `lane_mask`.
    fn int(self) -> u64 {
        match self {
            Self::Int(word) => word,
            Self::Float(value) => value.to_bits(),
        }
    }

    fn float(self) -> f64 {
        match self {
            Self::Float(value) => value,
            Self::Int(word) => f64::from_bits(word),
        }
    }
}

/// Bit `i` is set when argument `i` travels in the float bank.
fn lane_mask(args: &[ArgWord]) -> u32 {
    args.iter().enumerate().fold(0, |mask, (index, arg)| match arg {
        ArgWord::Float(_) => mask | (1 << index),
        ArgWord::Int(_) => mask,
    })
}

macro_rules! lane_ty {
    (I) => {
        u64
    };
    (F) => {
        f64
    };
}

macro_rules! lane_get {
    (I, $arg:expr) => {
        $arg.int()
    };
    (F, $arg:expr) => {
        $arg.float()
    };
}

macro_rules! extern_call {
    ($fp:expr, $args:expr, $ret:ty $(, $lane:ident @ $index:tt)*) => {{
        let call: unsafe extern "C" fn($(lane_ty!($lane)),*) -> $ret = unsafe { transmute($fp) };
        unsafe { call($(lane_get!($lane, $args[$index])),*) }
    }};
}

/// Every argument shape the interpreter can forward: each arity up to
/// `MAX_INTERP_EXTERN_ARGS`, times each assignment of its parameters to the two
/// register banks. Written once and instantiated per return lane, so a return
/// lane cannot be given a different set of argument shapes than another.
macro_rules! dispatch_shapes {
    ($fp:expr, $args:expr, $ret:ty) => {
        match ($args.len(), lane_mask($args)) {
            (0, _) => extern_call!($fp, $args, $ret),
            (1, 0b0) => extern_call!($fp, $args, $ret, I @ 0),
            (1, 0b1) => extern_call!($fp, $args, $ret, F @ 0),
            (2, 0b00) => extern_call!($fp, $args, $ret, I @ 0, I @ 1),
            (2, 0b01) => extern_call!($fp, $args, $ret, F @ 0, I @ 1),
            (2, 0b10) => extern_call!($fp, $args, $ret, I @ 0, F @ 1),
            (2, 0b11) => extern_call!($fp, $args, $ret, F @ 0, F @ 1),
            (3, 0b000) => extern_call!($fp, $args, $ret, I @ 0, I @ 1, I @ 2),
            (3, 0b001) => extern_call!($fp, $args, $ret, F @ 0, I @ 1, I @ 2),
            (3, 0b010) => extern_call!($fp, $args, $ret, I @ 0, F @ 1, I @ 2),
            (3, 0b011) => extern_call!($fp, $args, $ret, F @ 0, F @ 1, I @ 2),
            (3, 0b100) => extern_call!($fp, $args, $ret, I @ 0, I @ 1, F @ 2),
            (3, 0b101) => extern_call!($fp, $args, $ret, F @ 0, I @ 1, F @ 2),
            (3, 0b110) => extern_call!($fp, $args, $ret, I @ 0, F @ 1, F @ 2),
            (3, 0b111) => extern_call!($fp, $args, $ret, F @ 0, F @ 1, F @ 2),
            (4, 0b0000) => extern_call!($fp, $args, $ret, I @ 0, I @ 1, I @ 2, I @ 3),
            (4, 0b0001) => extern_call!($fp, $args, $ret, F @ 0, I @ 1, I @ 2, I @ 3),
            (4, 0b0010) => extern_call!($fp, $args, $ret, I @ 0, F @ 1, I @ 2, I @ 3),
            (4, 0b0011) => extern_call!($fp, $args, $ret, F @ 0, F @ 1, I @ 2, I @ 3),
            (4, 0b0100) => extern_call!($fp, $args, $ret, I @ 0, I @ 1, F @ 2, I @ 3),
            (4, 0b0101) => extern_call!($fp, $args, $ret, F @ 0, I @ 1, F @ 2, I @ 3),
            (4, 0b0110) => extern_call!($fp, $args, $ret, I @ 0, F @ 1, F @ 2, I @ 3),
            (4, 0b0111) => extern_call!($fp, $args, $ret, F @ 0, F @ 1, F @ 2, I @ 3),
            (4, 0b1000) => extern_call!($fp, $args, $ret, I @ 0, I @ 1, I @ 2, F @ 3),
            (4, 0b1001) => extern_call!($fp, $args, $ret, F @ 0, I @ 1, I @ 2, F @ 3),
            (4, 0b1010) => extern_call!($fp, $args, $ret, I @ 0, F @ 1, I @ 2, F @ 3),
            (4, 0b1011) => extern_call!($fp, $args, $ret, F @ 0, F @ 1, I @ 2, F @ 3),
            (4, 0b1100) => extern_call!($fp, $args, $ret, I @ 0, I @ 1, F @ 2, F @ 3),
            (4, 0b1101) => extern_call!($fp, $args, $ret, F @ 0, I @ 1, F @ 2, F @ 3),
            (4, 0b1110) => extern_call!($fp, $args, $ret, I @ 0, F @ 1, F @ 2, F @ 3),
            (4, 0b1111) => extern_call!($fp, $args, $ret, F @ 0, F @ 1, F @ 2, F @ 3),
            (n, _) => unreachable!("arity {n} is refused before dispatch (max {MAX_INTERP_EXTERN_ARGS})"),
        }
    };
}

unsafe fn dispatch_fn_returning_int(fp: *const (), args: &[ArgWord]) -> u64 {
    dispatch_shapes!(fp, args, u64)
}

unsafe fn dispatch_fn_returning_float(fp: *const (), args: &[ArgWord]) -> f64 {
    dispatch_shapes!(fp, args, f64)
}

unsafe fn dispatch_fn_void(fp: *const (), args: &[ArgWord]) {
    dispatch_shapes!(fp, args, ())
}

// ===== Test-only symbol registry (fz-swt.7) ================================

/// fz-swt.10 — expose the test counter dtor's raw address so JIT-leg
/// fixture tests can register it with the `JITBuilder`. Lives in this
/// module to share the `DTOR_FIRED` / `DTOR_LAST_PAYLOAD` statics with
/// the interp-leg tests below.
#[cfg(test)]
pub(crate) fn tests_support_test_dtor_addr() -> *const u8 {
    tests_support::_resource_test_dtor as *const u8
}

/// fz-swt.10 — accessors for the test dtor counters, used by both the
/// interp-leg tests in this file and native backend tests.
#[cfg(test)]
pub(crate) fn tests_support_dtor_reset() {
    tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
    tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_fired() -> usize {
    tests_support::DTOR_FIRED.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_last_payload() -> u64 {
    tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed)
}

/// fz-swt.10 — shared lock so JIT-leg and interp-leg resource tests
/// don't race on the static `DTOR_*` counters.
#[cfg(test)]
pub(crate) fn tests_support_lock() -> &'static Mutex<()> {
    static LOCK: Mutex<()> = Mutex::new(());
    &LOCK
}

#[cfg(test)]
pub(crate) mod tests_support {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    pub static DTOR_FIRED: AtomicUsize = AtomicUsize::new(0);
    pub static DTOR_LAST_PAYLOAD: AtomicU64 = AtomicU64::new(0);

    /// Counter-bumping dtor. Used by the fz-side test as the
    /// `&_resource_test_dtor/1` wrapped extern: bumps a global counter
    /// and records the payload it received. Verifies that the BIF stored
    /// the right C-ABI fn ptr and that MSO sweep invoked it on the right
    /// payload.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn _resource_test_dtor(payload: u64) {
        DTOR_FIRED.fetch_add(1, Ordering::Relaxed);
        DTOR_LAST_PAYLOAD.store(payload, Ordering::Relaxed);
    }

    pub fn lookup_test_symbol(name: &str) -> Option<*const ()> {
        match name {
            "_resource_test_dtor" => Some(_resource_test_dtor as *const ()),
            _ => None,
        }
    }
}
