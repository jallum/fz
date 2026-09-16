//! Extern wire types, from two directions.
//!
//! One table names every source spelling an extern declaration may write —
//! the `ExternTy` lane it means, whether a declared parameter takes its lane
//! from the spelling, and, for a wire-only spelling that names a calling
//! convention the type system has no type for, the semantic spelling the type
//! checker must see instead. A wire-only spelling names one lane, and a lane
//! is a whole register, so it stands only as a whole parameter or result; a
//! contract that writes one inside a larger type is refused here by name.
//!
//! `ty_to_extern_ty` answers the other direction: it derives a lane from a
//! semantic type through the type calculator, which is where every declared
//! parameter whose spelling does not name its own lane is answered.

use crate::ast::{SpecDecl, TypeExprBody};
use crate::diag::{Diagnostic, codes};
use crate::function_surface::CallableSurface;
use crate::fz_ir::ExternTy;
use crate::parser::lexer::{Tok, Token};
use crate::source::Span;
use crate::types::Types;

/// The C symbol an extern's fz-visible name resolves to. A `lib::name`
/// prefix is fz-side namespacing only, and an extern declared inside a
/// `defmodule Foo do ... end` is qualified to `Foo.name` by the resolver,
/// which is also fz-side decoration; the linker sees the bare suffix either
/// way. A single-segment name is already the symbol.
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

    /// A spelling the type system has no type for: a C width or pointer
    /// convention. It names its own lane, and the contract the type checker
    /// sees is rewritten to `semantic`, which is the fz type the values in
    /// that lane are.
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
    WireSpelling::wire_only("c_int", ExternTy::I32, "integer"),
    WireSpelling::wire_only("c_string", ExternTy::CString, "binary"),
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

/// Why a declaration hands the type checker no extern contract.
#[derive(Debug)]
pub(crate) enum ExternContractError {
    /// The declaration is not an extern, so it has no wire contract at all.
    NotAnExtern,
    /// A wire-only spelling is written inside a larger type. Such a spelling
    /// names one calling-convention lane, and a lane is a whole register, so
    /// it stands exactly where a whole parameter or result stands.
    WireSpellingInsideType { spelling: &'static str, span: Span },
}

impl ExternContractError {
    /// The refusal as every door reports it, so one declaration reads the
    /// same however it is compiled.
    pub(crate) fn diagnostic(&self, function: &str, name_span: Span) -> Diagnostic {
        match self {
            Self::NotAnExtern => Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("`{function}` is not an extern declaration"),
                name_span,
            ),
            Self::WireSpellingInsideType { spelling, span } => Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!(
                    "`{function}` writes `{spelling}` inside a larger type: a wire spelling names \
                     one C lane, so it stands only as a whole parameter or result"
                ),
                *span,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ExternContractError, ExternTy, TypeExprBody, WIRE_SPELLINGS, extern_ty_from_name,
        normalize_extern_semantic_body, token_for_spelling,
    };
    use crate::parser::lexer::{Tok, Token};
    use crate::source::Span;

    fn token(tok: Tok) -> Token {
        Token {
            tok,
            span: Span::DUMMY,
            space_before: false,
        }
    }

    fn ident(name: &str) -> Token {
        token(Tok::Ident(name.to_string()))
    }

    #[test]
    fn boolean_is_the_extern_source_type_name() {
        assert_eq!(extern_ty_from_name("boolean"), Some(ExternTy::Bool));
    }

    #[test]
    fn c_string_is_the_only_nul_terminated_binary_wire_spelling() {
        assert_eq!(extern_ty_from_name("c_string"), Some(ExternTy::CString));
        assert_eq!(extern_ty_from_name("cstring"), None);
    }

    /// Every wire-only spelling obeys one rule, and the table is what states
    /// it: alone it becomes the semantic type the checker has, and inside a
    /// larger type it is refused by name.
    #[test]
    fn a_wire_only_spelling_stands_alone_or_is_refused_by_name() {
        for row in WIRE_SPELLINGS.iter().filter(|row| row.semantic.is_some()) {
            let alone = TypeExprBody(vec![ident(row.name)]);
            let rewritten = normalize_extern_semantic_body(&alone).expect("a whole body names a lane");
            assert_eq!(
                rewritten.0[0].tok,
                token_for_spelling(row.semantic.expect("a wire-only row carries a semantic spelling")),
            );

            let inside_a_tuple = TypeExprBody(vec![
                token(Tok::LBrace),
                ident(row.name),
                token(Tok::Comma),
                ident("integer"),
                token(Tok::RBrace),
            ]);
            match normalize_extern_semantic_body(&inside_a_tuple) {
                Err(ExternContractError::WireSpellingInsideType { spelling, .. }) => {
                    assert_eq!(spelling, row.name)
                }
                other => panic!("`{}` inside a tuple must be refused by name: {other:?}", row.name),
            }
        }
    }
}

pub(crate) fn extern_semantic_contract(surface: &impl CallableSurface) -> Result<SpecDecl, ExternContractError> {
    let mut contract = surface.extern_contract_decl().ok_or(ExternContractError::NotAnExtern)?;
    contract.param_body_tokens = contract
        .param_body_tokens
        .iter()
        .map(normalize_extern_semantic_body)
        .collect::<Result<_, _>>()?;
    contract.result_body_tokens = normalize_extern_semantic_body(&contract.result_body_tokens)?;
    contract.constraints = contract
        .constraints
        .iter()
        .map(|(name, body)| Ok((name.clone(), normalize_extern_semantic_body(body)?)))
        .collect::<Result<_, _>>()?;
    Ok(contract)
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
    let c_pointer = t.c_pointer();
    let raw_word = t.union(int, pid);
    let raw_word = t.union(raw_word, reference);
    let raw_word = t.union(raw_word, c_pointer);
    if t.is_subtype(d, &raw_word) {
        return ExternTy::I64;
    }
    ExternTy::Any
}

/// Rewrite a wire-only spelling to its semantic spelling, so the type checker
/// sees a type it has. A whole body is the only place the rewrite can reach,
/// which is also the only place the lane it names has a register of its own,
/// so a spelling written anywhere else is refused here by name.
fn normalize_extern_semantic_body(body: &TypeExprBody) -> Result<TypeExprBody, ExternContractError> {
    let mut normalized = body.clone();
    if let [token] = normalized.0.as_mut_slice() {
        if let Tok::Ident(name) = &token.tok
            && let Some(semantic) = wire_spelling(name).and_then(|row| row.semantic)
        {
            token.tok = token_for_spelling(semantic);
        }
        return Ok(normalized);
    }
    match misplaced_wire_spelling(&normalized) {
        Some(refusal) => Err(refusal),
        None => Ok(normalized),
    }
}

/// The first wire-only spelling written among a compound type's tokens. A
/// field key lexes as its own token, so only a spelling in type position is
/// found here.
fn misplaced_wire_spelling(body: &TypeExprBody) -> Option<ExternContractError> {
    body.0.iter().find_map(|token| {
        let Tok::Ident(name) = &token.tok else {
            return None;
        };
        let row = wire_spelling(name).filter(|row| row.semantic.is_some())?;
        Some(ExternContractError::WireSpellingInsideType {
            spelling: row.name,
            span: token.span,
        })
    })
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
        let c_pointer = types.c_pointer();
        let builtin_union = types.union(pid, reference);
        let builtin_union = types.union(builtin_union, c_pointer);

        for builtin in [pid, reference, c_pointer, builtin_union] {
            assert_eq!(ty_to_extern_ty(&mut types, &builtin), ExternTy::I64);
        }
        for spelling in ["pid", "ref", "c_pointer"] {
            let user_opaque = types.opaque_of(spelling);
            assert_eq!(
                ty_to_extern_ty(&mut types, &user_opaque),
                ExternTy::Any,
                "display spelling cannot grant a user opaque a raw ABI lane"
            );
        }
    }
}
