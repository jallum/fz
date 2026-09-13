use crate::ast::{SpecDecl, TypeExprBody};
use crate::function_surface::CallableSurface;
use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};
use crate::parser::lexer::{Tok, Token};
use crate::types::Types;

/// The symbols fz itself owns, and the convention each is really provided with.
///
/// "Owns" spans the runtime crate's exported functions, including arithmetic
/// and comparison helpers. What unites the rows is not a source spelling but
/// that fz decides how the real export is called, so a declaration claiming
/// otherwise is a lie.
///
/// It is provenance, not preference: `fz_dbg_value` is
/// `fn(*mut Process, u64) -> u64` whatever a declaration says about it, so a
/// foreign `extern "C" def fz_dbg_value(any) :: any` ends in a transmute. That
/// used to be harmless only because both doors intercepted some names before
/// the declaration was consulted; once the ABI became the authority the lie
/// reached the callee and segfaulted the JIT and AOT doors.
///
/// So the question is answered ONCE, here, and asked from the shared front end
/// (`resolve_extern_abi`) -- the only place an answer reaches every door
/// identically -- and again by the interpreter's symbol resolver as
/// defence-in-depth around a raw transmute.
///
/// INCOMPLETE BY CONSTRUCTION, and fz-5xp.32 tracks closing it. The runtime
/// crate exports far more `fz_*` symbols than appear here, and a foreign
/// declaration of one that is absent gets no check at all. Absence currently
/// means "fz makes no claim", which is the right default for a genuinely
/// foreign symbol like `libc::close` and the wrong one for an unlisted runtime export.
/// One runtime-owned symbol inventory. A physical row is present exactly when
/// this ticket changes or depends on its machine ABI; the remaining ABI-only
/// rows are deliberately the validation work owned by fz-5xp.32.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuntimeSymbol {
    pub name: &'static str,
    pub abi: ExternAbi,
    pub physical: Option<RuntimePhysicalContract>,
}

/// The exact declaration-side shape of a runtime export that is safe to call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuntimePhysicalContract {
    pub params: &'static [ExternTy],
    pub ret: ExternReturn,
    pub native_binding: Option<RuntimeNativeBinding>,
}

/// A native replacement is an optimization capability granted only after the
/// source declaration has resolved to this exact physical runtime contract.
/// It is intentionally data from the runtime inventory, never parsed from a
/// source spelling or linker symbol at the codegen site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeNativeBinding {
    Comparison(RuntimeComparison),
}

/// The comparison operation a validated runtime export may lower directly.
///
/// These are intentionally separate from `BinOp`: the variant preserves the
/// runtime export's physical lane contract, so native lowering never infers an
/// operation from a linker name or a suffix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeComparison {
    Eq,
    Neq,
    Identical,
    NotIdentical,
    LtII,
    LtFF,
    LtIF,
    LtFI,
    LtBB,
    LeII,
    LeFF,
    LeIF,
    LeFI,
    LeBB,
    GtII,
    GtFF,
    GtIF,
    GtFI,
    GtBB,
    GeII,
    GeFF,
    GeIF,
    GeFI,
    GeBB,
}

impl RuntimeSymbol {
    const fn abi(name: &'static str, abi: ExternAbi) -> Self {
        Self {
            name,
            abi,
            physical: None,
        }
    }

    const fn physical(
        name: &'static str,
        abi: ExternAbi,
        params: &'static [ExternTy],
        ret: ExternReturn,
        native_binding: Option<RuntimeNativeBinding>,
    ) -> Self {
        Self {
            name,
            abi,
            physical: Some(RuntimePhysicalContract {
                params,
                ret,
                native_binding,
            }),
        }
    }
}

const I: &[ExternTy] = &[ExternTy::I64];
const F: &[ExternTy] = &[ExternTy::F64];
const A: &[ExternTy] = &[ExternTy::Any];
const II: &[ExternTy] = &[ExternTy::I64, ExternTy::I64];
const IF: &[ExternTy] = &[ExternTy::I64, ExternTy::F64];
const FI: &[ExternTy] = &[ExternTy::F64, ExternTy::I64];
const FF: &[ExternTy] = &[ExternTy::F64, ExternTy::F64];
const BB: &[ExternTy] = &[ExternTy::Binary, ExternTy::Binary];
const AA: &[ExternTy] = &[ExternTy::Any, ExternTy::Any];
const IA: &[ExternTy] = &[ExternTy::I64, ExternTy::Any];
const WORD: ExternReturn = ExternReturn::Scalar(ExternTy::I64);
const ANY: ExternReturn = ExternReturn::Scalar(ExternTy::Any);
const BINARY: ExternReturn = ExternReturn::Scalar(ExternTy::Binary);
const NEVER: ExternReturn = ExternReturn::Scalar(ExternTy::Never);
const INT_RESULT: ExternReturn = ExternReturn::Pair([ExternTy::I64, ExternTy::Bool]);
const FLOAT_RESULT: ExternReturn = ExternReturn::Pair([ExternTy::F64, ExternTy::Bool]);
const BOOL: ExternReturn = ExternReturn::Scalar(ExternTy::Bool);

pub const RUNTIME_SYMBOLS: &[RuntimeSymbol] = &[
    // Allocating helpers reach the process heap, so they take the process.
    // These are the `extern "fz"` declarations in the runtime library.
    RuntimeSymbol::abi("fz_atom_to_binary", ExternAbi::Fz),
    RuntimeSymbol::physical("fz_binary_concat", ExternAbi::Fz, BB, BINARY, None),
    RuntimeSymbol::physical("fz_dbg_value", ExternAbi::Fz, A, ANY, None),
    RuntimeSymbol::abi("fz_float_to_binary", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_integer_to_binary", ExternAbi::Fz),
    RuntimeSymbol::physical("fz_panic", ExternAbi::Fz, A, NEVER, None),
    RuntimeSymbol::abi("fz_process_heap_alloc_stats", ExternAbi::Fz),
    RuntimeSymbol::physical("fz_self", ExternAbi::Fz, &[], WORD, None),
    RuntimeSymbol::physical("fz_make_resource", ExternAbi::Fz, IA, ANY, None),
    RuntimeSymbol::physical("fz_spawn", ExternAbi::Fz, A, WORD, None),
    RuntimeSymbol::physical("fz_send", ExternAbi::Fz, IA, ANY, None),
    // Plain C symbols the runtime exports for the interpreter to call.
    // fz-5xp.8 — the total term order. Takes the process because atoms order
    // by NAME, and the name table lives on the node.
    RuntimeSymbol::physical("fz_value_cmp_ref", ExternAbi::Fz, AA, WORD, None),
    RuntimeSymbol::abi("fz_binary_downcase", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_binary_to_atom", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_binary_upcase", ExternAbi::Fz),
    RuntimeSymbol::physical("fz_bitstring_byte_size", ExternAbi::C, A, WORD, None),
    RuntimeSymbol::abi("fz_bitstring_is_binary", ExternAbi::C),
    RuntimeSymbol::abi("fz_bitstring_valid_utf8", ExternAbi::C),
    RuntimeSymbol::abi("fz_bitstring_utf8_prefix", ExternAbi::C),
    RuntimeSymbol::abi("fz_brand_bitstring_as_utf8", ExternAbi::C),
    RuntimeSymbol::abi("fz_map_delete", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_map_from_kv", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_map_put_ref", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_map_put_int", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_map_put_float", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_map_put_atom", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_map_put_atom_ref", ExternAbi::Fz),
    RuntimeSymbol::abi("fz_map_count", ExternAbi::C),
    RuntimeSymbol::abi("fz_map_entry_key", ExternAbi::C),
    RuntimeSymbol::abi("fz_map_entry_value", ExternAbi::C),
    RuntimeSymbol::abi("fz_resource_test_print_dtor", ExternAbi::C),
    RuntimeSymbol::physical("fz_make_ref", ExternAbi::C, &[], WORD, None),
    RuntimeSymbol::physical("fz_op_add_ii", ExternAbi::C, II, INT_RESULT, None),
    RuntimeSymbol::physical("fz_op_add_if", ExternAbi::C, IF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_add_ff", ExternAbi::C, FF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_sub_ii", ExternAbi::C, II, INT_RESULT, None),
    RuntimeSymbol::physical("fz_op_sub_if", ExternAbi::C, IF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_sub_fi", ExternAbi::C, FI, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_sub_ff", ExternAbi::C, FF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_neg_i", ExternAbi::C, I, INT_RESULT, None),
    RuntimeSymbol::physical(
        "fz_op_neg_f",
        ExternAbi::C,
        F,
        ExternReturn::Scalar(ExternTy::F64),
        None,
    ),
    RuntimeSymbol::physical("fz_op_mul_ii", ExternAbi::C, II, INT_RESULT, None),
    RuntimeSymbol::physical("fz_op_mul_if", ExternAbi::C, IF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_mul_ff", ExternAbi::C, FF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_div_ii", ExternAbi::C, II, INT_RESULT, None),
    RuntimeSymbol::physical("fz_op_div_ii_to_float", ExternAbi::C, II, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_div_if", ExternAbi::C, IF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_div_fi", ExternAbi::C, FI, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_div_ff", ExternAbi::C, FF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_rem_ii", ExternAbi::C, II, INT_RESULT, None),
    RuntimeSymbol::physical("fz_op_rem_if", ExternAbi::C, IF, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_rem_fi", ExternAbi::C, FI, FLOAT_RESULT, None),
    RuntimeSymbol::physical("fz_op_rem_ff", ExternAbi::C, FF, FLOAT_RESULT, None),
    RuntimeSymbol::physical(
        "fz_op_eq",
        ExternAbi::Fz,
        AA,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::Eq)),
    ),
    RuntimeSymbol::physical(
        "fz_op_neq",
        ExternAbi::Fz,
        AA,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::Neq)),
    ),
    RuntimeSymbol::physical(
        "fz_op_identical",
        ExternAbi::Fz,
        AA,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::Identical)),
    ),
    RuntimeSymbol::physical(
        "fz_op_not_identical",
        ExternAbi::Fz,
        AA,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::NotIdentical)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lt_ii",
        ExternAbi::C,
        II,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LtII)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lt_ff",
        ExternAbi::C,
        FF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LtFF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lt_if",
        ExternAbi::C,
        IF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LtIF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lt_fi",
        ExternAbi::C,
        FI,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LtFI)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lt_bb",
        ExternAbi::Fz,
        BB,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LtBB)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lte_ii",
        ExternAbi::C,
        II,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LeII)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lte_ff",
        ExternAbi::C,
        FF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LeFF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lte_if",
        ExternAbi::C,
        IF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LeIF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lte_fi",
        ExternAbi::C,
        FI,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LeFI)),
    ),
    RuntimeSymbol::physical(
        "fz_op_lte_bb",
        ExternAbi::Fz,
        BB,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LeBB)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gt_ii",
        ExternAbi::C,
        II,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GtII)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gt_ff",
        ExternAbi::C,
        FF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GtFF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gt_if",
        ExternAbi::C,
        IF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GtIF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gt_fi",
        ExternAbi::C,
        FI,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GtFI)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gt_bb",
        ExternAbi::Fz,
        BB,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GtBB)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gte_ii",
        ExternAbi::C,
        II,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GeII)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gte_ff",
        ExternAbi::C,
        FF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GeFF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gte_if",
        ExternAbi::C,
        IF,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GeIF)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gte_fi",
        ExternAbi::C,
        FI,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GeFI)),
    ),
    RuntimeSymbol::physical(
        "fz_op_gte_bb",
        ExternAbi::Fz,
        BB,
        BOOL,
        Some(RuntimeNativeBinding::Comparison(RuntimeComparison::GeBB)),
    ),
];

pub fn runtime_symbol_abi(symbol: &str) -> Option<ExternAbi> {
    RUNTIME_SYMBOLS
        .iter()
        .find(|entry| entry.name == symbol)
        .map(|entry| entry.abi)
}

/// The exact wire contract for a source-visible runtime export, when this
/// manifest owns one. Compiler-private imports have no row here.
pub fn runtime_physical_contract(symbol: &str) -> Option<RuntimePhysicalContract> {
    RUNTIME_SYMBOLS
        .iter()
        .find(|entry| entry.name == symbol)
        .and_then(|entry| entry.physical)
}

pub fn validate_runtime_symbol_shape(
    symbol: &str,
    abi: ExternAbi,
    params: &[ExternTy],
    ret: ExternReturn,
) -> Result<Option<RuntimeNativeBinding>, String> {
    let Some(entry) = RUNTIME_SYMBOLS.iter().find(|entry| entry.name == symbol) else {
        return Ok(None);
    };
    let Some(physical) = entry.physical else {
        return Ok(None);
    };
    if entry.abi != abi || physical.params != params || physical.ret != ret {
        return Err(format!(
            "runtime export `{symbol}` requires `extern \"{}\"` params {:?} and result {:?}, not `extern \"{}\"` params {:?} and result {:?}",
            entry.abi, physical.params, physical.ret, abi, params, ret
        ));
    }
    Ok(physical.native_binding)
}

/// fz-y3k — split an extern's fz-visible name into the C symbol it resolves
/// to. A `lib::name` prefix is fz-side documentation/namespacing only; the
/// linker sees just the bare suffix. fz-axu — externs declared inside a
/// `defmodule Foo do ... end` get auto-qualified by the resolver to
/// `Foo.name` (with a `.`), which is also fz-side decoration; strip
/// either separator to recover the C symbol. Single-segment names
/// round-trip.
pub(crate) fn extern_symbol_from_name(fz_name: &str) -> &str {
    if let Some((_, sym)) = fz_name.rsplit_once("::") {
        return sym;
    }
    if let Some((_, sym)) = fz_name.rsplit_once('.') {
        return sym;
    }
    fz_name
}

pub(crate) fn extern_ty_from_name(name: &str) -> Option<ExternTy> {
    match name {
        "any" | "atom" => Some(ExternTy::Any),
        "boolean" => Some(ExternTy::Bool),
        "integer" => Some(ExternTy::I64),
        "float" => Some(ExternTy::F64),
        "nil" => Some(ExternTy::Unit),
        "never" => Some(ExternTy::Never),
        "binary" => Some(ExternTy::Binary),
        "cstring" => Some(ExternTy::CString),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ExternAbi, ExternReturn, ExternTy, RuntimeComparison, RuntimeNativeBinding, extern_ty_from_name,
        validate_runtime_symbol_shape,
    };

    #[test]
    fn boolean_is_the_extern_source_type_name() {
        assert_eq!(extern_ty_from_name("boolean"), Some(ExternTy::Bool));
    }

    #[test]
    fn runtime_physical_contracts_validate_every_kernel_gateway() {
        assert_eq!(
            validate_runtime_symbol_shape(
                "fz_op_add_ii",
                ExternAbi::C,
                &[ExternTy::I64, ExternTy::I64],
                ExternReturn::Pair([ExternTy::I64, ExternTy::Bool]),
            ),
            Ok(None)
        );
        assert_eq!(
            validate_runtime_symbol_shape(
                "fz_op_lt_bb",
                ExternAbi::Fz,
                &[ExternTy::Binary, ExternTy::Binary],
                ExternReturn::Scalar(ExternTy::Bool),
            ),
            Ok(Some(RuntimeNativeBinding::Comparison(RuntimeComparison::LtBB)))
        );
        assert_eq!(
            validate_runtime_symbol_shape(
                "fz_send",
                ExternAbi::Fz,
                &[ExternTy::I64, ExternTy::Any],
                ExternReturn::Scalar(ExternTy::Any),
            ),
            Ok(None)
        );
        let error =
            validate_runtime_symbol_shape("fz_panic", ExternAbi::Fz, &[], ExternReturn::Scalar(ExternTy::Never))
                .expect_err("a Kernel runtime gateway must not accept a missing physical argument");
        assert!(error.contains("fz_panic") && error.contains("Any"));
        let error = validate_runtime_symbol_shape(
            "fz_op_add_ii",
            ExternAbi::C,
            &[ExternTy::I64, ExternTy::I64],
            ExternReturn::Scalar(ExternTy::I64),
        )
        .expect_err("a scalar result must not pass the aggregate arithmetic contract");
        assert!(error.contains("fz_op_add_ii") && error.contains("result"));
        let error = validate_runtime_symbol_shape(
            "fz_op_lt_bb",
            ExternAbi::C,
            &[ExternTy::Binary, ExternTy::Binary],
            ExternReturn::Scalar(ExternTy::Bool),
        )
        .expect_err("a bare C binary pointer declaration must not acquire the ref comparison capability");
        assert!(error.contains("fz_op_lt_bb") && error.contains("extern \"fz\""));
    }
}

pub(crate) fn extern_semantic_contract(surface: &impl CallableSurface) -> Option<SpecDecl> {
    let mut contract = surface.extern_contract_decl()?;
    contract.param_body_tokens = contract
        .param_body_tokens
        .iter()
        .map(normalize_extern_semantic_body)
        .collect();
    contract.result_body_tokens = normalize_extern_semantic_body(&contract.result_body_tokens);
    contract.constraints = contract
        .constraints
        .iter()
        .map(|(name, body)| (name.clone(), normalize_extern_semantic_body(body)))
        .collect();
    Some(contract)
}

pub(crate) fn explicit_extern_wire_hint(body: &TypeExprBody) -> Option<ExternTy> {
    match body.0.as_slice() {
        [
            Token {
                tok: Tok::Ident(name), ..
            },
        ] => match name.as_str() {
            "binary" => Some(ExternTy::Binary),
            "cstring" => Some(ExternTy::CString),
            "unit" => Some(ExternTy::Unit),
            _ => None,
        },
        [Token { tok: Tok::Nil, .. }] => Some(ExternTy::Unit),
        _ => None,
    }
}

/// Derive a coarse C-ABI wire type from a semantic Ty.
///
/// Explicit marshal hints should already have been handled before this point.
/// The fallback uses the semantic upper bound: raw integer lanes cover both
/// `integer` and the closed builtin word identities; float-only types get F64; nil-only -> Unit;
/// never -> Never. Everything else stays as a tagged value.
pub(crate) fn ty_to_extern_ty<T: Types>(t: &mut T, d: &T::Ty) -> ExternTy {
    if t.is_empty(d) {
        return ExternTy::Never;
    }
    if t.is_nil(d) {
        return ExternTy::Unit;
    }
    let boolean = t.bool();
    if t.is_equivalent(d, &boolean) {
        return ExternTy::Bool;
    }
    if t.is_floating(d) {
        return ExternTy::F64;
    }
    let int = t.int();
    let pid = t.pid();
    let reference = t.reference();
    let cpointer = t.cpointer();
    let raw_word = t.union(int, pid);
    let raw_word = t.union(raw_word, reference);
    let raw_word = t.union(raw_word, cpointer);
    if t.is_subtype(d, &raw_word) {
        return ExternTy::I64;
    }
    ExternTy::Any
}

fn normalize_extern_semantic_body(body: &TypeExprBody) -> TypeExprBody {
    let mut normalized = body.clone();
    if let [token] = normalized.0.as_mut_slice() {
        match &token.tok {
            Tok::Ident(name) if name == "cstring" => {
                token.tok = Tok::Ident("binary".to_string());
            }
            Tok::Ident(name) if name == "unit" => {
                token.tok = Tok::Nil;
            }
            _ => {}
        }
    }
    normalized
}

#[cfg(test)]
mod runtime_symbol_reachability_test {
    use super::RUNTIME_SYMBOLS;
    use crate::ir_codegen::runtime_symbol_addrs;

    /// fz-5xp.58 — a symbol fz DECLARES must be reachable when compiled code
    /// calls it. There are exactly two ways for that to be true on the native
    /// path: the JIT is handed its address, or native codegen lowers the call
    /// in place and never asks for an address at all.
    ///
    /// Nothing checked it, and the JIT's symbol list had drifted:
    /// `fz_bitstring_is_binary` was declared and never registered. On macOS the
    /// JIT falls back to `dlsym` over the process image and finds the
    /// `no_mangle` export anyway, so the whole six-target local gate was green
    /// while `to_string` died on Linux with `can't resolve symbol`. Every
    /// symbol missing from that list is a landmine that only goes off on one
    /// platform, which is precisely the kind of thing a test has to hold.
    #[test]
    fn every_declared_runtime_symbol_is_reachable_from_compiled_code() {
        let registered: Vec<&str> = runtime_symbol_addrs().into_iter().map(|(name, _)| name).collect();
        let unreachable: Vec<&str> = RUNTIME_SYMBOLS
            .iter()
            .map(|entry| entry.name)
            .filter(|name| !registered.contains(name))
            .collect();
        assert!(
            unreachable.is_empty(),
            "declared in RUNTIME_SYMBOLS but neither registered with the JIT nor lowered in place \
             by native codegen -- these resolve on macOS only by dlsym accident and fail on Linux: {:?}",
            unreachable
        );
    }
}

#[cfg(test)]
mod builtin_opaque_wire_test {
    use super::{ExternTy, ty_to_extern_ty};
    use crate::compiler2::Types;

    #[test]
    fn only_builtin_opaque_word_types_use_the_integer_abi_lane() {
        let mut types = Types::new();
        let pid = types.pid();
        let reference = types.reference();
        let cpointer = types.cpointer();
        let builtin_union = types.union(pid, reference);
        let builtin_union = types.union(builtin_union, cpointer);

        for builtin in [pid, reference, cpointer, builtin_union] {
            assert_eq!(ty_to_extern_ty(&mut types, &builtin), ExternTy::I64);
        }
        for spelling in ["pid", "ref", "cpointer"] {
            let user_opaque = types.opaque_of(spelling);
            assert_eq!(
                ty_to_extern_ty(&mut types, &user_opaque),
                ExternTy::Any,
                "display spelling cannot grant a user opaque a raw ABI lane"
            );
        }
    }
}
