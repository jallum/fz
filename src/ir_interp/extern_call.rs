use super::*;
use crate::compiler2::LoweredExtern;
use crate::compiler2::native_codegen::{ExternLane, emit_fn_body, emit_variadic_c_call, host_isa};
use crate::fz_ir::{ExternReturn, ExternTy};
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, MemFlags, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module, default_libcall_names};
use fz_runtime::extern_binary::{fz_binary_as_cstring, fz_binary_as_ptr};
use fz_runtime::symbol_lookup::fz_extern_symbol_addr;
use std::collections::HashMap;
use std::ffi::CString;
#[cfg(not(unix))]
use std::ffi::c_void;
use std::mem::transmute;
#[cfg(not(unix))]
use std::ptr::null_mut;
#[cfg(test)]
use std::sync::Mutex;
#[cfg(test)]
use std::sync::atomic::Ordering;

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
        // A C `int` parameter is the low half of the fz integer. The word is
        // still handed over whole -- a callee reading an `int` reads the low
        // 32 bits of the register -- so narrowing here is what makes the
        // variadic tail, which promotes the same word back, agree.
        ExternTy::I32 => ArgWord::Int(
            value
                .as_i64()
                .ok_or_else(|| "extern integer arg must be Int".to_string())? as i32 as i64 as u64,
        ),
        ExternTy::F64 => ArgWord::Float(
            value
                .as_float()
                .ok_or_else(|| "extern float arg must be Float".to_string())?,
        ),
        ExternTy::Bool => ArgWord::Int(match value {
            AnyValue::Atom(id) if id == fz_runtime::any_value::FALSE_ATOM_ID => 0,
            AnyValue::Atom(id) if id == fz_runtime::any_value::TRUE_ATOM_ID => 1,
            _ => return Err("extern boolean arg must be false or true".to_string()),
        }),
        ExternTy::Binary | ExternTy::CString if fz_abi => ArgWord::Int(value.extern_arg_ref_word(proc)?),
        ExternTy::Binary => ArgWord::Int((unsafe { fz_binary_as_ptr(value.extern_arg_ref_word(proc)?) }) as u64),
        ExternTy::CString => ArgWord::Int((unsafe { fz_binary_as_cstring(value.extern_arg_ref_word(proc)?) }) as u64),
        ExternTy::Any => ArgWord::Int(value.extern_arg_ref_word(proc)?),
        ExternTy::Unit | ExternTy::Never => {
            return Err(format!("{:?} is not a valid extern argument marshal class", ty));
        }
    })
}

#[derive(Debug)]
pub(super) enum ExternCallValue {
    Scalar(AnyValue),
    Pair([AnyValue; 2]),
}

pub(super) fn call_lowered_extern(
    runtime: &mut IrInterpRuntime,
    signature: &LoweredExtern,
    marshals: Option<&[ExternTy]>,
    args: &[AnyValue],
) -> Result<ExternCallValue, String> {
    if signature.variadic {
        return call_variadic_extern(runtime, signature, marshals, args);
    }

    // Arity is enforced where the call is lowered; this guards the transmute
    // below against a caller that bypassed lowering, where `zip` would
    // silently truncate.
    if args.len() != signature.params.len() {
        return Err(format!(
            "extern `{}` declares {} parameter(s) but was called with {} argument(s)",
            signature.symbol,
            signature.params.len(),
            args.len()
        ));
    }
    let fp = resolve_symbol(&signature.symbol)?;
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
    let result = unsafe { call_declared_return(fp, &raw_args, signature) };
    // A helper that reports through the execution context, such as
    // `fz_panic`, leaves its error pending; that error is the answer whatever
    // lane the call came back in.
    if let Some(error) = runtime.take_callback_error() {
        return Err(error);
    }
    result
}

/// A C variadic call, made through a generated trampoline.
///
/// The interpreter has no linker, so it resolves the foreign address by name
/// and then needs a machine that can call it. That machine is one small JIT'd
/// function per call shape, which reads the marshalled argument words out of
/// an array and reaches `emit_variadic_c_call` — the same lowering compiled
/// code uses, so both doors make the identical machine call. Handing the words
/// over through a pointer keeps the trampoline at two parameters, so the
/// argument ceiling the fixed-arity path lives under never applies here.
fn call_variadic_extern(
    runtime: &mut IrInterpRuntime,
    signature: &LoweredExtern,
    marshals: Option<&[ExternTy]>,
    args: &[AnyValue],
) -> Result<ExternCallValue, String> {
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
    let ret_ty = signature
        .ret
        .scalar_ty()
        .ok_or_else(|| format!("variadic extern `{}` cannot return an aggregate", signature.symbol))?;
    if ret_ty == ExternTy::F64 {
        return Err(format!(
            "variadic extern `{}` returns a float, which the generated variadic call does not carry",
            signature.symbol
        ));
    }
    let cname = CString::new(signature.symbol.as_str()).map_err(|e| format!("bad symbol name: {e}"))?;
    let callee = unsafe { fz_extern_symbol_addr(cname.as_ptr()) };
    if callee == 0 {
        return Err(format!("dlsym: symbol `{}` not found", signature.symbol));
    }

    // Each argument is one machine word in the array the trampoline reads. A
    // fixed float parameter travels in the float bank, and the trampoline
    // loads its slot as an `f64` to put it there.
    let words: Vec<u64> = args
        .iter()
        .zip(arg_tys.iter().copied())
        .map(|(value, ty)| marshal_arg(runtime.cur_proc(), *value, ty, false).map(ArgWord::int))
        .collect::<Result<_, _>>()?;

    let fixed_count = signature.params.len();
    let shape = VariadicShape {
        // A parameter that carries no value has no lane; `marshal_arg` refuses
        // one above, so the word it would occupy is never reached.
        fixed: arg_tys[..fixed_count]
            .iter()
            .map(|ty| ty.lane().unwrap_or(types::I64))
            .collect(),
        variadic: arg_tys.len() - fixed_count,
        ret: ret_ty.lane(),
    };
    let trampoline = runtime.variadic_trampolines().get_or_generate(&shape)?;
    let ret = unsafe { trampoline(callee, words.as_ptr()) };

    // The trampoline sign extends a `c_int` result before returning it, so
    // every integer-lane answer arrives here as a full 64-bit word.
    match ret_ty {
        ExternTy::I64 | ExternTy::I32 => Ok(ExternCallValue::Scalar(AnyValue::Int(ret as i64))),
        ExternTy::Bool => Ok(ExternCallValue::Scalar(decode_bool_word(ret))),
        ExternTy::Any | ExternTy::Binary | ExternTy::CString => {
            interp_value_from_extern_ref_word(ret).map(ExternCallValue::Scalar)
        }
        ExternTy::Unit => Ok(ExternCallValue::Scalar(interp_nil_value())),
        ExternTy::Never => Err(format!("extern `{}` declared Never returned", signature.symbol)),
        ExternTy::F64 => unreachable!("a float-returning variadic extern is refused above"),
    }
}

/// Everything about a variadic call that decides the trampoline's code, and
/// nothing about the particular call: the fixed parameters' register lanes,
/// how many variadic words follow them, and the result lane.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct VariadicShape {
    fixed: Vec<ir::Type>,
    variadic: usize,
    ret: Option<ir::Type>,
}

/// `extern "C" fn(callee: usize, words: *const u64) -> u64`. A call with no
/// result answers zero.
type VariadicTrampoline = unsafe extern "C" fn(usize, *const u64) -> u64;

/// The generated variadic trampolines, and the JIT module holding their code.
///
/// The module owns the machine code its finalized pointers name, so the two
/// live together and the interpreter that hands out a pointer is the owner of
/// the module it points into.
pub(super) struct VariadicTrampolines {
    module: JITModule,
    fbctx: FunctionBuilderContext,
    generated: HashMap<VariadicShape, VariadicTrampoline>,
}

impl VariadicTrampolines {
    pub(super) fn new() -> Self {
        let builder = JITBuilder::with_isa(host_isa(), default_libcall_names());
        Self {
            module: JITModule::new(builder),
            fbctx: FunctionBuilderContext::new(),
            generated: HashMap::new(),
        }
    }

    fn get_or_generate(&mut self, shape: &VariadicShape) -> Result<VariadicTrampoline, String> {
        if let Some(&trampoline) = self.generated.get(shape) {
            return Ok(trampoline);
        }
        let trampoline = self.generate(shape)?;
        self.generated.insert(shape.clone(), trampoline);
        Ok(trampoline)
    }

    fn generate(&mut self, shape: &VariadicShape) -> Result<VariadicTrampoline, String> {
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let name = format!("fz_variadic_trampoline_{}", self.generated.len());
        let func_id = self
            .module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|error| format!("declare {name}: {error}"))?;
        emit_fn_body(&mut self.module, &mut self.fbctx, sig, func_id, |module, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let callee = b.block_params(entry)[0];
            let words = b.block_params(entry)[1];
            let fixed: Vec<(ir::Value, ir::Type)> = shape
                .fixed
                .iter()
                .enumerate()
                .map(|(index, &lane)| (load_word(b, words, index, lane), lane))
                .collect();
            let variadic: Vec<ir::Value> = (0..shape.variadic)
                .map(|index| load_word(b, words, shape.fixed.len() + index, types::I64))
                .collect();
            let result = emit_variadic_c_call(b, module.isa(), callee, &fixed, &variadic, shape.ret);
            // The trampoline hands one 64-bit word back, so a half-width C
            // result is widened here rather than by every caller.
            let answer = match result {
                Some(value) if shape.ret == Some(types::I32) => b.ins().sextend(types::I64, value),
                Some(value) => value,
                None => b.ins().iconst(types::I64, 0),
            };
            b.ins().return_(&[answer]);
        })
        .map_err(|error| format!("define {name}: {error}"))?;
        self.module
            .finalize_definitions()
            .map_err(|error| format!("finalize {name}: {error}"))?;
        let code = self.module.get_finalized_function(func_id);
        // Safety: the body just emitted has exactly this signature, and the
        // module that owns its code outlives this cache entry.
        Ok(unsafe { transmute::<*const u8, VariadicTrampoline>(code) })
    }
}

/// One argument word out of the array, in the register lane it travels in.
fn load_word(b: &mut FunctionBuilder<'_>, words: ir::Value, index: usize, lane: ir::Type) -> ir::Value {
    b.ins().load(lane, MemFlags::trusted(), words, (index * 8) as i32)
}

/// The declared RETURN picks the lane the answer comes back in. A float is
/// returned in the float bank, so reading the integer return register gave
/// back whatever happened to be there -- for `libc::sqrt` that was the
/// argument's own bits, which looked exactly like a plausible answer.
///
/// # Safety
/// `fp` must be a function whose parameters travel in the banks `raw_args`
/// names, in order, and whose return matches `signature.ret`.
unsafe fn call_declared_return(
    fp: *const (),
    raw_args: &[ArgWord],
    signature: &LoweredExtern,
) -> Result<ExternCallValue, String> {
    match signature.ret {
        ExternReturn::Scalar(ExternTy::F64) => {
            let value = unsafe { dispatch_fn_returning_float(fp, raw_args) };
            Ok(ExternCallValue::Scalar(AnyValue::Float(value)))
        }
        ExternReturn::Scalar(ExternTy::Unit) => {
            unsafe { dispatch_fn_void(fp, raw_args) };
            Ok(ExternCallValue::Scalar(interp_nil_value()))
        }
        ExternReturn::Scalar(ExternTy::Never) => {
            unsafe { dispatch_fn_void(fp, raw_args) };
            Err(format!("extern `{}` declared Never returned", signature.symbol))
        }
        ExternReturn::Scalar(ExternTy::I64) => {
            let value = unsafe { dispatch_fn_returning_int(fp, raw_args) };
            Ok(ExternCallValue::Scalar(AnyValue::Int(value as i64)))
        }
        // A C `int` result occupies only the low half of the return register.
        // Reading the whole register is how `open`'s -1 becomes 4294967295 on
        // a platform whose libc leaves the upper half zero.
        ExternReturn::Scalar(ExternTy::I32) => {
            let value = unsafe { dispatch_fn_returning_c_int(fp, raw_args) };
            Ok(ExternCallValue::Scalar(AnyValue::Int(value as i64)))
        }
        ExternReturn::Scalar(ExternTy::Bool) => {
            let value = unsafe { dispatch_fn_returning_int(fp, raw_args) };
            Ok(ExternCallValue::Scalar(decode_bool_word(value)))
        }
        ExternReturn::Scalar(ExternTy::Any | ExternTy::Binary | ExternTy::CString) => {
            let value = unsafe { dispatch_fn_returning_int(fp, raw_args) };
            interp_value_from_extern_ref_word(value).map(ExternCallValue::Scalar)
        }
        ExternReturn::Pair(fields) => {
            let values = unsafe { dispatch_fn_returning_pair(fp, raw_args, fields) }?;
            Ok(ExternCallValue::Pair(values))
        }
    }
}

fn decode_bool_word(word: u64) -> AnyValue {
    interp_bool_value(word != 0)
}

/// How many machine words the `dispatch_fn_*` family can forward. They
/// transmute to a concrete `extern "C" fn` type, so the enumerated shapes are
/// the limit -- and a shape is an arity TIMES an assignment of its parameters
/// to the integer and float register banks. An `extern "fz"` spends one slot on
/// the implicit process word.
const MAX_INTERP_EXTERN_ARGS: usize = 4;

/// The address to call for a declared extern symbol.
///
/// One resolver answers for every symbol: `fz_extern_symbol_addr` searches the
/// loaded image, then the standard C libraries. The declaration is the
/// authority on how that address is called -- its ABI, parameter lanes and
/// result lane are what the caller transmutes to.
pub(super) fn resolve_symbol(name: &str) -> Result<*const (), String> {
    #[cfg(test)]
    if let Some(fp) = tests_support::lookup_test_symbol(name) {
        return Ok(fp);
    }

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

unsafe fn dispatch_fn_returning_c_int(fp: *const (), args: &[ArgWord]) -> i32 {
    dispatch_shapes!(fp, args, i32)
}

unsafe fn dispatch_fn_returning_float(fp: *const (), args: &[ArgWord]) -> f64 {
    dispatch_shapes!(fp, args, f64)
}

#[repr(C)]
struct PairII {
    first: u64,
    second: u64,
}

#[repr(C)]
struct PairIF {
    first: u64,
    second: f64,
}

#[repr(C)]
struct PairFI {
    first: f64,
    second: u64,
}

#[repr(C)]
struct PairFF {
    first: f64,
    second: f64,
}

#[cfg(test)]
#[path = "extern_call_test.rs"]
mod extern_call_test;

unsafe fn dispatch_fn_returning_pair(
    fp: *const (),
    args: &[ArgWord],
    fields: [ExternTy; 2],
) -> Result<[AnyValue; 2], String> {
    fn int_field(word: u64, ty: ExternTy) -> Result<AnyValue, String> {
        match ty {
            ExternTy::I64 => Ok(AnyValue::Int(word as i64)),
            ExternTy::Bool => Ok(decode_bool_word(word)),
            _ => Err(format!("foreign integer return register cannot decode {ty:?}")),
        }
    }
    match fields {
        [ExternTy::F64, ExternTy::F64] => {
            let pair = dispatch_shapes!(fp, args, PairFF);
            Ok([AnyValue::Float(pair.first), AnyValue::Float(pair.second)])
        }
        [ExternTy::F64, second] => {
            let pair = dispatch_shapes!(fp, args, PairFI);
            Ok([AnyValue::Float(pair.first), int_field(pair.second, second)?])
        }
        [first, ExternTy::F64] => {
            let pair = dispatch_shapes!(fp, args, PairIF);
            Ok([int_field(pair.first, first)?, AnyValue::Float(pair.second)])
        }
        [first, second] => {
            let pair = dispatch_shapes!(fp, args, PairII);
            Ok([int_field(pair.first, first)?, int_field(pair.second, second)?])
        }
    }
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

#[cfg(test)]
pub(crate) fn tests_support_integer_boolean_pair_addr() -> *const u8 {
    tests_support::_test_integer_boolean_pair as *const u8
}

#[cfg(test)]
pub(crate) fn tests_support_scalar_pair_symbols() -> Vec<(&'static str, *const u8)> {
    tests_support::scalar_pair_symbols()
}

#[cfg(test)]
pub(crate) fn tests_support_resolved_symbol_addr(name: &str) -> Result<*const (), String> {
    resolve_symbol(name)
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

    pub unsafe extern "C" fn _test_never_returns() {}

    #[repr(C)]
    pub struct TestIntegerBooleanPair {
        pub value: i64,
        pub failed: u64,
    }

    pub unsafe extern "C" fn _test_integer_boolean_pair(value: i64) -> TestIntegerBooleanPair {
        TestIntegerBooleanPair { value, failed: 0 }
    }

    #[repr(C)]
    pub struct TestWordWordPair(pub u64, pub u64);
    #[repr(C)]
    pub struct TestWordFloatPair(pub u64, pub f64);
    #[repr(C)]
    pub struct TestFloatWordPair(pub f64, pub u64);
    #[repr(C)]
    pub struct TestFloatFloatPair(pub f64, pub f64);

    macro_rules! pair_fn {
        ($name:ident, $ret:ty, $value:expr) => {
            pub unsafe extern "C" fn $name() -> $ret {
                $value
            }
        };
    }

    pair_fn!(_test_pair_ii, TestWordWordPair, TestWordWordPair(1, 2));
    pair_fn!(_test_pair_ib, TestWordWordPair, TestWordWordPair(1, 0));
    pair_fn!(_test_pair_bi, TestWordWordPair, TestWordWordPair(1, 2));
    pair_fn!(_test_pair_bb, TestWordWordPair, TestWordWordPair(0, 1));
    pair_fn!(_test_pair_if, TestWordFloatPair, TestWordFloatPair(1, 2.5));
    pair_fn!(_test_pair_bf, TestWordFloatPair, TestWordFloatPair(1, 2.5));
    pair_fn!(_test_pair_fi, TestFloatWordPair, TestFloatWordPair(1.5, 2));
    pair_fn!(_test_pair_fb, TestFloatWordPair, TestFloatWordPair(1.5, 0));
    pair_fn!(_test_pair_ff, TestFloatFloatPair, TestFloatFloatPair(1.5, 2.5));
    pair_fn!(_test_pair_bad_bool, TestWordWordPair, TestWordWordPair(7, 2));

    pub fn scalar_pair_symbols() -> Vec<(&'static str, *const u8)> {
        vec![
            ("_test_pair_ii", _test_pair_ii as *const u8),
            ("_test_pair_ib", _test_pair_ib as *const u8),
            ("_test_pair_bi", _test_pair_bi as *const u8),
            ("_test_pair_bb", _test_pair_bb as *const u8),
            ("_test_pair_if", _test_pair_if as *const u8),
            ("_test_pair_bf", _test_pair_bf as *const u8),
            ("_test_pair_fi", _test_pair_fi as *const u8),
            ("_test_pair_fb", _test_pair_fb as *const u8),
            ("_test_pair_ff", _test_pair_ff as *const u8),
            ("_test_pair_bad_bool", _test_pair_bad_bool as *const u8),
        ]
    }

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
            "_test_never_returns" => Some(_test_never_returns as *const ()),
            "_test_integer_boolean_pair" => Some(_test_integer_boolean_pair as *const ()),
            name => scalar_pair_symbols()
                .into_iter()
                .find_map(|(candidate, address)| (name == candidate).then_some(address as *const ())),
        }
    }
}
