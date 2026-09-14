//! Calling a runtime helper by its Rust function item.
//!
//! A helper the code generator emits a call to is an ordinary `extern "C"`
//! function in `fz_runtime`, and that item is the whole story: its type is
//! the wire signature, and `stringify!` of its name is the linker symbol.
//! `runtime_call!` reads both off the item, so a call cannot disagree with
//! the function it reaches — the lanes come from the Rust parameter types,
//! and a parameter type with no lane is a compile error.
//!
//! A helper is declared on first use in the body that calls it, memoized per
//! body, the way a source-visible extern declares itself.

use super::*;
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, Signature};
use cranelift_module::{FuncId, Linkage, Module};

/// The register lane a C scalar travels in. Integers and floats ride
/// different banks, so a parameter's Rust type decides its bank.
pub(crate) trait CLane {
    const LANE: ir::Type;
}

macro_rules! impl_c_lane {
    ($lane:expr; $($ty:ty),+ $(,)?) => {
        $(impl CLane for $ty {
            const LANE: ir::Type = $lane;
        })+
    };
}

impl_c_lane!(ir::types::I64; i64, u64, usize);
impl_c_lane!(ir::types::I32; i32, u32);
impl_c_lane!(ir::types::I8; i8, u8, bool);
impl_c_lane!(ir::types::F64; f64);

impl<T> CLane for *mut T {
    const LANE: ir::Type = ir::types::I64;
}

impl<T> CLane for *const T {
    const LANE: ir::Type = ir::types::I64;
}

/// A result lane, or none at all for a helper that returns nothing.
pub(crate) trait CRet {
    const LANE: Option<ir::Type>;
}

impl CRet for () {
    const LANE: Option<ir::Type> = None;
}

impl<T: CLane> CRet for T {
    const LANE: Option<ir::Type> = Some(T::LANE);
}

/// A runtime helper's Cranelift signature, read off its Rust function type.
pub(crate) trait RuntimeFn {
    /// In the module's default calling convention: a runtime export is a
    /// plain C function, so the target names the convention.
    fn signature<M: Module>(module: &mut M) -> Signature;
}

macro_rules! impl_runtime_fn {
    ($($param:ident),*) => {
        impl<$($param: CLane,)* R: CRet> RuntimeFn for unsafe extern "C" fn($($param),*) -> R {
            fn signature<M: Module>(module: &mut M) -> Signature {
                let mut sig = module.make_signature();
                $(sig.params.push(AbiParam::new($param::LANE));)*
                if let Some(ret) = R::LANE {
                    sig.returns.push(AbiParam::new(ret));
                }
                sig
            }
        }
    };
}

impl_runtime_fn!();
impl_runtime_fn!(A);
impl_runtime_fn!(A, B);
impl_runtime_fn!(A, B, C);
impl_runtime_fn!(A, B, C, D);
impl_runtime_fn!(A, B, C, D, E);
impl_runtime_fn!(A, B, C, D, E, F);
impl_runtime_fn!(A, B, C, D, E, F, G);
impl_runtime_fn!(A, B, C, D, E, F, G, H);
impl_runtime_fn!(A, B, C, D, E, F, G, H, I);
impl_runtime_fn!(A, B, C, D, E, F, G, H, I, J);

/// Declare a runtime helper in `module`. Declaration is by name and is
/// idempotent, so every body that calls a helper reaches the same symbol.
pub(crate) fn declare_runtime_fn<M: Module, F: RuntimeFn>(module: &mut M, name: &str, _item: F) -> FuncId {
    let sig = F::signature(module);
    module
        .declare_function(name, Linkage::Import, &sig)
        .unwrap_or_else(|error| panic!("declare runtime helper `{name}`: {error}"))
}

/// A body under construction that can call runtime helpers: it holds the
/// module that declares the symbol and the builder that emits the call.
pub(crate) trait RuntimeCaller {
    /// The function-local reference to a helper, declared on first use and
    /// memoized by its linker name.
    fn runtime_func_ref<F: RuntimeFn + Copy>(&mut self, name: &'static str, item: F) -> ir::FuncRef;

    fn emit_call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst;

    fn sole_result(&self, call: ir::Inst) -> ir::Value;

    /// Emit a call to a runtime helper. The returned `Inst` carries the
    /// results, if the helper has any.
    fn call_runtime<F: RuntimeFn + Copy>(&mut self, name: &'static str, item: F, args: &[ir::Value]) -> ir::Inst {
        let callee = self.runtime_func_ref(name, item);
        self.emit_call(callee, args)
    }

    /// Emit a call to a runtime helper and read its single result.
    fn call_runtime1<F: RuntimeFn + Copy>(&mut self, name: &'static str, item: F, args: &[ir::Value]) -> ir::Value {
        let call = self.call_runtime(name, item, args);
        self.sole_result(call)
    }
}

impl<M: Module> RuntimeCaller for CodegenFn<'_, '_, M> {
    fn runtime_func_ref<F: RuntimeFn + Copy>(&mut self, name: &'static str, item: F) -> ir::FuncRef {
        if let Some(&callee) = self.cache.runtime_funcs.get(name) {
            return callee;
        }
        let id = declare_runtime_fn(self.jmod, name, item);
        let callee = self.jmod.declare_func_in_func(id, self.b.func);
        self.cache.runtime_funcs.insert(name, callee);
        callee
    }

    fn emit_call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst {
        self.b.ins().call(callee, args)
    }

    fn sole_result(&self, call: ir::Inst) -> ir::Value {
        self.b.inst_results(call)[0]
    }
}

/// Call a runtime helper named by its Rust function item:
/// `runtime_call!(body, fz_list_cons_int, [process, head, tail])`. The item
/// must be in scope at the call site.
macro_rules! runtime_call {
    ($body:expr, $item:ident, [$($arg:expr),* $(,)?]) => {{
        let args: &[cranelift_codegen::ir::Value] = &[$($arg),*];
        let item: unsafe extern "C" fn($(runtime_call!(@lane $arg)),*) -> _ = $item;
        $body.call_runtime(stringify!($item), item, args)
    }};
    (@lane $arg:expr) => {
        _
    };
}

/// `runtime_call!` for a helper with one result, yielding that result.
macro_rules! runtime_call1 {
    ($body:expr, $item:ident, [$($arg:expr),* $(,)?]) => {{
        let args: &[cranelift_codegen::ir::Value] = &[$($arg),*];
        let item: unsafe extern "C" fn($(runtime_call!(@lane $arg)),*) -> _ = $item;
        $body.call_runtime1(stringify!($item), item, args)
    }};
}

/// The function-local reference to a runtime helper, for a site that needs
/// the reference itself rather than a call. The parentheses hold one `_` per
/// parameter: `runtime_func_ref!(body, fz_fmod(_, _))`.
macro_rules! runtime_func_ref {
    ($body:expr, $item:ident($($lane:tt),* $(,)?)) => {{
        let item: unsafe extern "C" fn($($lane),*) -> _ = $item;
        $body.runtime_func_ref(stringify!($item), item)
    }};
}

/// The module-level `FuncId` of a runtime helper, for a site that needs the
/// symbol itself rather than a call — a relocation into static data, say.
/// The parentheses hold one `_` per parameter:
/// `runtime_fn_id!(jmod, shared_bin_destructor_noop(_))`.
macro_rules! runtime_fn_id {
    ($module:expr, $item:ident($($lane:tt),* $(,)?)) => {{
        let item: unsafe extern "C" fn($($lane),*) -> _ = $item;
        $crate::compiler2::native_codegen::runtime_call::declare_runtime_fn($module, stringify!($item), item)
    }};
}

pub(crate) use {runtime_call, runtime_call1, runtime_fn_id, runtime_func_ref};
