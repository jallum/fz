use super::*;
use crate::fz_ir::{ExternArg, ExternId, ExternMarshalSite, ExternTy, Module};
use crate::types::Types;

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

fn marshal_arg(
    proc: *mut fz_runtime::process::Process,
    value: AnyValue,
    ty: ExternTy,
) -> Result<u64, String> {
    Ok(match ty {
        ExternTy::I64 => value
            .as_i64()
            .ok_or_else(|| "extern integer arg must be Int".to_string())?
            as u64,
        ExternTy::F64 => value
            .as_float()
            .ok_or_else(|| "extern float arg must be Float".to_string())?
            .to_bits(),
        ExternTy::Binary => {
            (unsafe {
                fz_runtime::extern_binary::fz_binary_as_ptr(value.extern_arg_ref_word(proc)?)
            }) as u64
        }
        ExternTy::CString => {
            (unsafe {
                fz_runtime::extern_binary::fz_binary_as_cstring(value.extern_arg_ref_word(proc)?)
            }) as u64
        }
        ExternTy::Any => value.extern_arg_ref_word(proc)?,
        ExternTy::Unit | ExternTy::Never => {
            return Err(format!(
                "{:?} is not a valid extern argument marshal class",
                ty
            ));
        }
    })
}

fn call_variadic_extern(
    proc: *mut fz_runtime::process::Process,
    module: &Module,
    fn_types: &crate::ir_planner::SpecPlan,
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
    eid: ExternId,
    extern_args: &[ExternArg],
    values: &[AnyValue],
) -> Result<u64, String> {
    let decl = module.extern_by_id(eid);
    let mut arg_tys = Vec::with_capacity(extern_args.len());
    for arg_idx in 0..extern_args.len() {
        let site = ExternMarshalSite {
            block: block_id,
            stmt_idx,
            arg_idx,
        };
        let Some(&ty) = fn_types.extern_marshals.get(&site) else {
            return Err(format!(
                "variadic extern `{}` has unresolved marshal metadata at {:?}",
                decl.symbol, site
            ));
        };
        arg_tys.push(ty);
    }
    let fixed_count = decl.params.len();
    let fixed = &arg_tys[..fixed_count];
    let variadic = &arg_tys[fixed_count..];

    let cname = std::ffi::CString::new(decl.symbol.as_str())
        .map_err(|e| format!("bad symbol name: {e}"))?;
    let fp = unsafe { fz_runtime::extern_variadic::fz_extern_symbol_addr(cname.as_ptr()) };
    if fp == 0 {
        return Err(format!("dlsym: symbol `{}` not found", decl.symbol));
    }

    let raw_args: Vec<u64> = values
        .iter()
        .zip(arg_tys.iter().copied())
        .map(|(value, ty)| marshal_arg(proc, *value, ty))
        .collect::<Result<_, _>>()?;

    match (decl.ret, fixed, variadic) {
        (ExternTy::I64, [ExternTy::CString, ExternTy::I64], [ExternTy::I64]) => Ok(unsafe {
            fz_runtime::extern_variadic::fz_call_var_i64_cstring_i64_i64_to_i64(
                fp,
                raw_args[0] as *const std::ffi::c_char,
                raw_args[1] as i64,
                raw_args[2] as i64,
            ) as u64
        }),
        (ExternTy::I64, [ExternTy::CString], [ExternTy::I64]) => Ok(unsafe {
            fz_runtime::extern_variadic::fz_call_var_i64_cstring_i64_to_i64(
                fp,
                raw_args[0] as *const std::ffi::c_char,
                raw_args[1] as i64,
            ) as u64
        }),
        _ => Err(format!(
            "unsupported variadic extern shape: {}",
            format_extern_shape(decl.ret, fixed, variadic)
        )),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn call_extern<T: Types<Ty = crate::types::Ty>>(
    runtime: &mut IrInterpRuntime,
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    fn_types: &crate::ir_planner::SpecPlan,
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
    eid: ExternId,
    extern_args: &[ExternArg],
    args: &[AnyValue],
) -> Result<AnyValue, String> {
    let decl = module.extern_by_id(eid);
    match decl.symbol.as_str() {
        "fz_panic" => {
            if args.len() != 1 {
                return Err(format!("fz_panic/1 got {} args", args.len()));
            }
            return Err(format!("fz panic: {}", args[0].render(runtime.cur_proc())));
        }
        "fz_process_heap_alloc_stats" => {
            if !args.is_empty() {
                return Err(format!(
                    "fz_process_heap_alloc_stats/0 got {} args",
                    args.len()
                ));
            }
            return interp_value_from_extern_ref_word(
                fz_runtime::ir_runtime::fz_process_heap_alloc_stats(runtime.cur_proc()),
            );
        }
        // Spawn/send/self need the interpreter's own scheduler — the C
        // implementations require a Runtime spawn hook which is only
        // installed on the JIT/AOT path.
        "fz_spawn" | "fz_spawn_opt" => {
            if args.is_empty() {
                return Err(format!("{}/1+ got 0 args", &decl.symbol));
            }
            // args[0] is the zero-arg closure to run in the child task;
            // args[1] (fz_spawn_opt) is a min_heap_size hint — ignored here.
            let (fn_id, captured) = unpack_closure(args[0].value()?)?;
            let pid = runtime.spawn(module, fn_id, captured)?;
            return Ok(AnyValue::Int(pid as i64));
        }
        "fz_self" => {
            return Ok(AnyValue::Int(unsafe { &*runtime.cur_proc() }.pid as i64));
        }
        "fz_make_ref" => {
            // fz-ht5 — route through the runtime FFI so interp and JIT
            // share the same counter; otherwise an interp run followed
            // by a JIT run in the same process could collide.
            let id = fz_runtime::ir_runtime::fz_make_ref_raw();
            return Ok(AnyValue::Int(id as i64));
        }
        "fz_send" => {
            if args.len() != 2 {
                return Err(format!("fz_send/2 got {} args", args.len()));
            }
            let receiver = args[0]
                .as_i64()
                .ok_or_else(|| "send/2: pid must be Int".to_string())?
                as u32;
            runtime.send(t, module, tel, receiver, args[1])?;
            return Ok(args[1]);
        }
        "fz_make_resource" => {
            // fz-swt.7 / fz-swt.10 — interp BIF: routes through the same
            // shared helper used by the runtime's `MakeResourceHook` for
            // the JIT/AOT legs, so dtor-resolution semantics are uniform
            // across paths.
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
                args[1].value()?,
            )
            .map(interp_value_from_slot);
        }
        "fz_brand_bitstring_as_utf8" => {
            if args.len() != 1 {
                return Err(format!(
                    "fz_brand_bitstring_as_utf8/1 got {} args",
                    args.len()
                ));
            }
            return Ok(args[0]);
        }
        // dbg/print is a process intrinsic: the runtime BIF renders atom
        // names off the process and routes output through the process's
        // ExecCtx telemetry sink, so the interp calls it with its own
        // running process rather than through the generic 1-arg FFI path
        // (whose arity no longer matches the widened BIF ABI).
        "fz_dbg_value" => {
            if args.len() != 1 {
                return Err(format!("fz_dbg_value/1 got {} args", args.len()));
            }
            let ref_word = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            let out = fz_runtime::ir_runtime::fz_dbg_value(runtime.cur_proc(), ref_word);
            return interp_value_from_extern_ref_word(out);
        }
        "fz_binary_concat" => {
            if args.len() != 2 {
                return Err(format!("fz_binary_concat/2 got {} args", args.len()));
            }
            let left_ref = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            let right_ref = args[1].extern_arg_ref_word(runtime.cur_proc())?;
            return interp_value_from_extern_ref_word(fz_runtime::ir_runtime::fz_binary_concat(
                runtime.cur_proc(),
                left_ref,
                right_ref,
            ));
        }
        "fz_map_count" => {
            if args.len() != 1 {
                return Err(format!("fz_map_count/1 got {} args", args.len()));
            }
            let ref_word = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            return Ok(AnyValue::Int(fz_runtime::ir_runtime::fz_map_count(
                ref_word,
            )));
        }
        "fz_map_entry_key" => {
            if args.len() != 2 {
                return Err(format!("fz_map_entry_key/2 got {} args", args.len()));
            }
            let map_ref = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            let index = args[1]
                .as_i64()
                .ok_or_else(|| "fz_map_entry_key/2 index must be integer".to_string())?;
            return interp_value_from_extern_ref_word(fz_runtime::ir_runtime::fz_map_entry_key(
                map_ref, index,
            ));
        }
        "fz_map_entry_value" => {
            if args.len() != 2 {
                return Err(format!("fz_map_entry_value/2 got {} args", args.len()));
            }
            let map_ref = args[0].extern_arg_ref_word(runtime.cur_proc())?;
            let index = args[1]
                .as_i64()
                .ok_or_else(|| "fz_map_entry_value/2 index must be integer".to_string())?;
            return interp_value_from_extern_ref_word(fz_runtime::ir_runtime::fz_map_entry_value(
                map_ref, index,
            ));
        }
        _ => {}
    }
    if decl.variadic {
        let ret = call_variadic_extern(
            runtime.cur_proc(),
            module,
            fn_types,
            block_id,
            stmt_idx,
            eid,
            extern_args,
            args,
        )?;
        return match decl.ret {
            ExternTy::I64 => Ok(AnyValue::Int(ret as i64)),
            ExternTy::F64 => Ok(AnyValue::Float(f64::from_bits(ret))),
            ExternTy::Any | ExternTy::Binary | ExternTy::CString => {
                interp_value_from_extern_ref_word(ret)
            }
            ExternTy::Unit | ExternTy::Never => Ok(interp_nil_value()),
        };
    }
    let fp = resolve_symbol(&decl.symbol)?;
    let raw_args: Vec<u64> = args
        .iter()
        .zip(decl.params.iter())
        .map(|(v, ty)| marshal_arg(runtime.cur_proc(), *v, *ty))
        .collect::<Result<_, _>>()?;
    let returns_value = !matches!(decl.ret, ExternTy::Unit | ExternTy::Never);
    let ret = if returns_value {
        unsafe { dispatch_fn_returning(fp, &raw_args) }
    } else {
        unsafe { dispatch_fn_void(fp, &raw_args) };
        0
    };
    // fz-rb8 — `:: integer` returns a raw signed 64-bit value from C.
    // The interpreter keeps it raw; opaque `Any` results must be tagged
    // heap bits because a one-word C return has no side-band kind.
    match decl.ret {
        ExternTy::I64 => Ok(AnyValue::Int(ret as i64)),
        ExternTy::F64 => Ok(AnyValue::Float(f64::from_bits(ret))),
        ExternTy::Any | ExternTy::Binary | ExternTy::CString => {
            interp_value_from_extern_ref_word(ret)
        }
        ExternTy::Unit | ExternTy::Never => Ok(interp_nil_value()),
    }
}

/// Return the function pointer for a named C symbol.
///
/// Checks the built-in native table first (all symbols declared in runtime.fz
/// are registered here so that the interpreter finds them even when the runtime
/// is statically linked and dlsym(RTLD_DEFAULT) cannot reach the symbols).
/// Falls back to dlsym for any name not in the table.
pub(super) fn resolve_symbol(name: &str) -> Result<*const (), String> {
    // Native table: every symbol declared in runtime.fz. These Rust functions
    // are linked into the binary; using their address directly avoids relying
    // on dlsym visibility, which is unreliable for statically-linked rlibs.
    #[cfg(test)]
    if let Some(fp) = tests_support::lookup_test_symbol(name) {
        return Ok(fp);
    }
    let native: Option<*const ()> = match name {
        // fz_dbg_value / fz_panic / fz_process_heap_alloc_stats are process
        // intrinsics special-cased in call_extern above; their widened BIF ABI
        // (leading process arg) no longer matches the generic FFI path, so they
        // must never be resolved as plain symbols here.
        // fz-swt.11 — fixture/test dtor exported from the runtime crate.
        // Bound here so interp-leg invocations of fixtures using this
        // symbol (e.g. when `fz interp` is run by hand on the AOT-only
        // fixture) reach the same Rust fn the AOT-linked binary uses.
        "fz_resource_test_print_dtor" => {
            Some(fz_runtime::resource::fz_resource_test_print_dtor as *const ())
        }
        // fz-axu.14 (R1) — utf8 runtime support. Bound here so the
        // interp leg of the matrix can resolve them without relying on
        // dlsym; statically-linked rlibs don't expose these via
        // RTLD_DEFAULT on Linux.
        "fz_bitstring_valid_utf8" => {
            Some(fz_runtime::ir_runtime::fz_bitstring_valid_utf8 as *const ())
        }
        "fz_brand_bitstring_as_utf8" => {
            Some(fz_runtime::ir_runtime::fz_brand_bitstring_as_utf8 as *const ())
        }
        "fz_binary_concat" => Some(fz_runtime::ir_runtime::fz_binary_concat as *const ()),
        "fz_map_count" => Some(fz_runtime::ir_runtime::fz_map_count as *const ()),
        "fz_map_entry_key" => Some(fz_runtime::ir_runtime::fz_map_entry_key as *const ()),
        "fz_map_entry_value" => Some(fz_runtime::ir_runtime::fz_map_entry_value as *const ()),
        _ => None,
    };
    if let Some(fp) = native {
        return Ok(fp);
    }
    // Fallback: dlsym for user-declared externs not in the native table.
    use std::ffi::CString;
    let cname = CString::new(name).map_err(|e| format!("bad symbol name: {}", e))?;
    #[cfg(unix)]
    let ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, cname.as_ptr()) };
    #[cfg(not(unix))]
    let ptr: *mut std::ffi::c_void = std::ptr::null_mut();
    if ptr.is_null() {
        return Err(format!("dlsym: symbol `{}` not found", name));
    }
    Ok(ptr as *const ())
}

unsafe fn dispatch_fn_returning(fp: *const (), args: &[u64]) -> u64 {
    match args.len() {
        0 => unsafe {
            let f: unsafe extern "C" fn() -> u64 = std::mem::transmute(fp);
            f()
        },
        1 => unsafe {
            let f: unsafe extern "C" fn(u64) -> u64 = std::mem::transmute(fp);
            f(args[0])
        },
        2 => unsafe {
            let f: unsafe extern "C" fn(u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1])
        },
        3 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1], args[2])
        },
        4 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1], args[2], args[3])
        },
        n => panic!("extern arity {} not supported (max 4)", n),
    }
}

unsafe fn dispatch_fn_void(fp: *const (), args: &[u64]) {
    match args.len() {
        0 => unsafe {
            let f: unsafe extern "C" fn() = std::mem::transmute(fp);
            f()
        },
        1 => unsafe {
            let f: unsafe extern "C" fn(u64) = std::mem::transmute(fp);
            f(args[0])
        },
        2 => unsafe {
            let f: unsafe extern "C" fn(u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1])
        },
        3 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1], args[2])
        },
        4 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1], args[2], args[3])
        },
        n => panic!("extern arity {} not supported (max 4)", n),
    }
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
/// interp-leg tests in this file and the JIT-leg tests in
/// `ir_codegen::tests`.
#[cfg(test)]
pub(crate) fn tests_support_dtor_reset() {
    use std::sync::atomic::Ordering;
    tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
    tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_fired() -> usize {
    tests_support::DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed)
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_last_payload() -> u64 {
    tests_support::DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed)
}

/// fz-swt.10 — shared lock so JIT-leg and interp-leg resource tests
/// don't race on the static `DTOR_*` counters.
#[cfg(test)]
pub(crate) fn tests_support_lock() -> &'static std::sync::Mutex<()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
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
