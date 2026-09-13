use crate::ast::{SpecDecl, TypeExprBody};
use crate::function_surface::CallableSurface;
use crate::fz_ir::{ExternAbi, ExternTy};
use crate::parser::lexer::{Tok, Token};
use crate::types::Types;

/// The symbols fz itself owns, and the convention each is really provided with.
///
/// "Owns" spans two providers, deliberately: some rows are exported by the
/// runtime crate (`fz_binary_concat`, `fz_map_count`), and the `fz_op_*` rows
/// are private shims inside `ir_interp/extern_call.rs` that exist only because
/// native codegen answers those symbols by emitting arithmetic instead of a
/// call. What unites them is not where the code lives but that fz decides how
/// they are called, so a declaration claiming otherwise is a lie.
///
/// It is provenance, not preference: `fz_dbg_value` is
/// `fn(*mut Process, u64) -> u64` whatever a declaration says about it, so a
/// foreign `extern "C" def fz_dbg_value(any) :: any` ends in a transmute. That
/// used to be harmless only because both doors claimed those symbols by name
/// before the declaration was consulted; once the ABI became the authority the
/// lie reached the callee and segfaulted the JIT and AOT doors.
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
/// foreign symbol like `libc::close` and the wrong one for `fz_self_raw`.
pub const RUNTIME_SYMBOLS: &[(&str, ExternAbi)] = &[
    // Allocating helpers reach the process heap, so they take the process.
    // These are the `extern "fz"` declarations in the runtime library.
    ("fz_atom_to_binary", ExternAbi::Fz),
    ("fz_binary_concat", ExternAbi::Fz),
    ("fz_dbg_value", ExternAbi::Fz),
    ("fz_float_to_binary", ExternAbi::Fz),
    ("fz_integer_to_binary", ExternAbi::Fz),
    ("fz_process_heap_alloc_stats", ExternAbi::Fz),
    // Plain C symbols the runtime exports for the interpreter to call.
    // fz-5xp.8 — the total term order. Takes the process because atoms order
    // by NAME, and the name table lives on the node.
    ("fz_value_cmp_ref", ExternAbi::Fz),
    ("fz_binary_downcase", ExternAbi::Fz),
    ("fz_binary_to_atom", ExternAbi::Fz),
    ("fz_binary_upcase", ExternAbi::Fz),
    ("fz_bitstring_byte_size", ExternAbi::C),
    ("fz_bitstring_is_binary", ExternAbi::C),
    ("fz_bitstring_valid_utf8", ExternAbi::C),
    ("fz_brand_bitstring_as_utf8", ExternAbi::C),
    ("fz_map_delete", ExternAbi::Fz),
    ("fz_map_from_kv", ExternAbi::Fz),
    ("fz_map_put_ref", ExternAbi::Fz),
    ("fz_map_put_int", ExternAbi::Fz),
    ("fz_map_put_float", ExternAbi::Fz),
    ("fz_map_put_atom", ExternAbi::Fz),
    ("fz_map_put_atom_ref", ExternAbi::Fz),
    ("fz_map_count", ExternAbi::C),
    ("fz_map_entry_key", ExternAbi::C),
    ("fz_map_entry_value", ExternAbi::C),
    ("fz_resource_test_print_dtor", ExternAbi::C),
    ("fz_op_add_ii", ExternAbi::C),
    ("fz_op_add_if", ExternAbi::C),
    ("fz_op_add_ff", ExternAbi::C),
    ("fz_op_sub_ii", ExternAbi::C),
    ("fz_op_sub_if", ExternAbi::C),
    ("fz_op_sub_fi", ExternAbi::C),
    ("fz_op_sub_ff", ExternAbi::C),
    ("fz_op_neg_i", ExternAbi::C),
    ("fz_op_neg_f", ExternAbi::C),
    ("fz_op_mul_ii", ExternAbi::C),
    ("fz_op_mul_if", ExternAbi::C),
    ("fz_op_mul_ff", ExternAbi::C),
    ("fz_op_div_ii", ExternAbi::C),
    ("fz_op_div_ii_to_float", ExternAbi::C),
    ("fz_op_div_if", ExternAbi::C),
    ("fz_op_div_fi", ExternAbi::C),
    ("fz_op_div_ff", ExternAbi::C),
    ("fz_op_rem_ii", ExternAbi::C),
    ("fz_op_rem_if", ExternAbi::C),
    ("fz_op_rem_fi", ExternAbi::C),
    ("fz_op_rem_ff", ExternAbi::C),
];

pub fn runtime_symbol_abi(symbol: &str) -> Option<ExternAbi> {
    RUNTIME_SYMBOLS
        .iter()
        .find(|(name, _)| *name == symbol)
        .map(|(_, abi)| *abi)
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
        "any" | "atom" | "boolean" => Some(ExternTy::Any),
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
    use super::{ExternTy, extern_ty_from_name};

    #[test]
    fn boolean_is_the_extern_source_type_name() {
        assert_eq!(extern_ty_from_name("boolean"), Some(ExternTy::Any));
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
/// `integer` and `cpointer`; float-only types get F64; nil-only -> Unit;
/// never -> Never. Everything else stays as a tagged value.
pub(crate) fn ty_to_extern_ty<T: Types>(t: &mut T, d: &T::Ty) -> ExternTy {
    if t.is_empty(d) {
        return ExternTy::Never;
    }
    if t.is_nil(d) {
        return ExternTy::Unit;
    }
    if t.is_floating(d) {
        return ExternTy::F64;
    }
    let int = t.int();
    let cpointer = t.cpointer();
    let raw_word = t.union(int, cpointer);
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
    use crate::compiler2::native_codegen::ARITH_SHIMS;
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
            .map(|(name, _)| *name)
            .filter(|name| !registered.contains(name) && !ARITH_SHIMS.iter().any(|(shim, _)| shim == name))
            .collect();
        assert!(
            unreachable.is_empty(),
            "declared in RUNTIME_SYMBOLS but neither registered with the JIT nor lowered in place \
             by native codegen -- these resolve on macOS only by dlsym accident and fail on Linux: {:?}",
            unreachable
        );
    }

    /// The escape hatch cannot become a dumping ground: a name is only allowed
    /// to skip registration because codegen really does lower it, so every
    /// entry in that table has to be a symbol fz declares.
    #[test]
    fn every_natively_lowered_shim_is_a_declared_symbol() {
        let declared: Vec<&str> = RUNTIME_SYMBOLS.iter().map(|(name, _)| *name).collect();
        let strays: Vec<&str> = ARITH_SHIMS
            .iter()
            .map(|(name, _)| *name)
            .filter(|name| !declared.contains(name))
            .collect();
        assert!(strays.is_empty(), "lowered in place but never declared: {:?}", strays);
    }
}
