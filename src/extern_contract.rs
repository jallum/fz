//! Extern wire types, from two directions.
//!
//! One table names every source spelling an extern declaration may write —
//! the `ExternTy` lane it means, whether a declared parameter takes its lane
//! from the spelling, and, for a wire-only spelling that names a calling
//! convention the type system has no type for, the semantic spelling the type
//! checker must see instead.
//!
//! `ty_to_extern_ty` answers the other direction: it derives a lane from a
//! semantic type through the type calculator, which is where every declared
//! parameter whose spelling does not name its own lane is answered.

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

/// One source spelling of an extern wire type.
struct WireSpelling {
    /// The spelling as it is written in a declaration or a call-site
    /// ascription.
    name: &'static str,
    /// The lane the spelling names.
    ty: ExternTy,
    /// Whether a declared parameter takes its lane from the spelling rather
    /// than from its semantic type.
    lane_from_spelling: bool,
    /// The semantic spelling a wire-only spelling is rewritten to before the
    /// type checker sees the contract.
    semantic: Option<&'static str>,
}

impl WireSpelling {
    /// A spelling a declared parameter's lane is read off the semantic type
    /// for, so an alias or a constraint can widen it.
    const fn from_semantic_type(name: &'static str, ty: ExternTy) -> Self {
        Self {
            name,
            ty,
            lane_from_spelling: false,
            semantic: None,
        }
    }

    /// A spelling that names its own lane, because the semantic type cannot:
    /// `binary` is a pointer convention the calculator reads as `Any`, and
    /// `nil` carries no value at all.
    const fn names_its_lane(name: &'static str, ty: ExternTy) -> Self {
        Self {
            name,
            ty,
            lane_from_spelling: true,
            semantic: None,
        }
    }

    /// A spelling the type system has no type for. It names its own lane, and
    /// the contract the type checker sees is rewritten to `semantic`.
    const fn wire_only(name: &'static str, ty: ExternTy, semantic: &'static str) -> Self {
        Self {
            name,
            ty,
            lane_from_spelling: true,
            semantic: Some(semantic),
        }
    }
}

const WIRE_SPELLINGS: &[WireSpelling] = &[
    WireSpelling::from_semantic_type("any", ExternTy::Any),
    WireSpelling::from_semantic_type("atom", ExternTy::Any),
    WireSpelling::from_semantic_type("boolean", ExternTy::Bool),
    WireSpelling::from_semantic_type("integer", ExternTy::I64),
    WireSpelling::from_semantic_type("float", ExternTy::F64),
    WireSpelling::from_semantic_type("never", ExternTy::Never),
    WireSpelling::names_its_lane("nil", ExternTy::Unit),
    WireSpelling::names_its_lane("binary", ExternTy::Binary),
    WireSpelling::wire_only("cstring", ExternTy::CString, "binary"),
    WireSpelling::wire_only("unit", ExternTy::Unit, "nil"),
];

fn wire_spelling(name: &str) -> Option<&'static WireSpelling> {
    WIRE_SPELLINGS.iter().find(|row| row.name == name)
}

/// The token the lexer produces for a spelling: `nil` is its own token,
/// everything else is an identifier.
fn token_for_spelling(name: &str) -> Tok {
    if name == "nil" {
        Tok::Nil
    } else {
        Tok::Ident(name.to_string())
    }
}

/// The lane a bare type name means, as written in a variadic call site's
/// `arg :: ty` ascription.
pub(crate) fn extern_ty_from_name(name: &str) -> Option<ExternTy> {
    wire_spelling(name).map(|row| row.ty)
}

#[cfg(test)]
mod tests {
    use super::{ExternTy, extern_ty_from_name};

    #[test]
    fn boolean_is_the_extern_source_type_name() {
        assert_eq!(extern_ty_from_name("boolean"), Some(ExternTy::Bool));
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

/// The lane a declared parameter's type tokens name outright. `None` leaves
/// the answer to `ty_to_extern_ty` and the semantic type.
pub(crate) fn explicit_extern_wire_hint(body: &TypeExprBody) -> Option<ExternTy> {
    let spelling = match body.0.as_slice() {
        [
            Token {
                tok: Tok::Ident(name), ..
            },
        ] => name.as_str(),
        [Token { tok: Tok::Nil, .. }] => "nil",
        _ => return None,
    };
    let row = wire_spelling(spelling)?;
    row.lane_from_spelling.then_some(row.ty)
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

/// Rewrite a wire-only spelling to its semantic spelling, so the type checker
/// sees a type it has.
fn normalize_extern_semantic_body(body: &TypeExprBody) -> TypeExprBody {
    let mut normalized = body.clone();
    if let [token] = normalized.0.as_mut_slice()
        && let Tok::Ident(name) = &token.tok
        && let Some(semantic) = wire_spelling(name).and_then(|row| row.semantic)
    {
        token.tok = token_for_spelling(semantic);
    }
    normalized
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
