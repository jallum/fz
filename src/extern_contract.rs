use crate::ast::{SpecDecl, TypeExprBody};
use crate::function_surface::CallableSurface;
use crate::fz_ir::ExternTy;
use crate::parser::lexer::{Tok, Token};
use crate::types::Types;

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
        "any" | "atom" | "bool" => Some(ExternTy::Any),
        "integer" => Some(ExternTy::I64),
        "float" => Some(ExternTy::F64),
        "nil" => Some(ExternTy::Unit),
        "never" => Some(ExternTy::Never),
        "binary" => Some(ExternTy::Binary),
        "cstring" => Some(ExternTy::CString),
        _ => None,
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
