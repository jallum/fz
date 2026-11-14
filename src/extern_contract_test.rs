#[cfg(test)]
mod builtin_opaque_wire_test {
    use super::super::{ExternTy, ty_to_extern_ty};
    use crate::compiler2::Types;
    use fz_runtime::any_value::ValueKind;

    #[test]
    fn a_pid_and_a_reference_have_lanes_of_their_own_and_a_c_pointer_the_integer_lane() {
        let mut types = Types::new();
        let pid = types.pid();
        let reference = types.reference();
        let c_pointer = types.c_pointer();
        assert_eq!(ty_to_extern_ty(&mut types, &pid), ExternTy::Opaque(ValueKind::PID));
        assert_eq!(
            ty_to_extern_ty(&mut types, &reference),
            ExternTy::Opaque(ValueKind::REF)
        );
        assert_eq!(ty_to_extern_ty(&mut types, &c_pointer), ExternTy::I64);
        let pid_or_reference = types.union(pid, reference);
        let pid_or_c_pointer = types.union(pid, c_pointer);
        for mixed in [pid_or_reference, pid_or_c_pointer] {
            assert_eq!(
                ty_to_extern_ty(&mut types, &mixed),
                ExternTy::Any,
                "a union of kinds is held as a tagged value"
            );
        }
        for spelling in ["pid", "ref", "c_pointer"] {
            let int = types.int();
            let payload = types.resource(int);
            let user_opaque = types.mint_brand(payload, spelling);
            assert_eq!(
                ty_to_extern_ty(&mut types, &user_opaque),
                ExternTy::Any,
                "display spelling cannot grant a user opaque a raw ABI lane"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
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
