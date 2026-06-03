use crate::types::ClosureTypes;
use ScalarLiteral::{Atom, Bool, Float, Int, Nil};
use TypeMatch::{No, Opaque, Yes};

#[derive(Clone, Debug, PartialEq)]
pub enum ScalarLiteral {
    Int(i64),
    Float(f64),
    Nil,
    Bool(bool),
    Atom(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeMatch {
    Yes,
    No,
    Opaque,
}

pub trait LiteralTypes: ClosureTypes {
    /// If `a` is a single bool literal (`true` or `false`), return it.
    /// Default reuses `as_atom_singleton`; future implementations may
    /// override with a more direct check.
    fn as_bool_lit(&self, a: &Self::Ty) -> Option<bool> {
        match self.as_atom_singleton(a).as_deref() {
            Some("true") => Some(true),
            Some("false") => Some(false),
            _ => None,
        }
    }

    /// True iff `a` uniquely determines a single runtime value — a
    /// singleton scalar, `nil`, or a tuple/closure whose every part is
    /// itself literal. Used by the reducer to decide whether a fold's
    /// inputs are fully known.
    fn is_literal(&self, a: &Self::Ty) -> bool {
        self.is_singleton_lit(a)
            || self.is_nil(a)
            || self
                .tuple_lit_elems(a)
                .is_some_and(|elems| elems.iter().all(|elem| self.is_literal(elem)))
            || self
                .closure_lit_parts(a)
                .is_some_and(|lit| lit.captures.iter().all(|capture| self.is_literal(capture)))
    }

    /// If `a` is a scalar literal representable as an IR `Const`, return it.
    fn scalar_literal(&self, a: &Self::Ty) -> Option<ScalarLiteral> {
        self.as_int_singleton(a)
            .map(Int)
            .or_else(|| self.as_float_singleton(a).map(Float))
            .or_else(|| self.is_nil(a).then_some(Nil))
            .or_else(|| self.as_bool_lit(a).map(Bool))
            .or_else(|| self.as_atom_singleton(a).map(Atom))
    }

    /// True iff `a` can be reconstructed by the reducer as a literal value:
    /// scalar const, closure literal with materializable captures, literal
    /// tuple with materializable elements, or the empty-list literal.
    fn is_materializable(&self, a: &Self::Ty) -> bool {
        self.scalar_literal(a).is_some()
            || self
                .closure_lit_parts(a)
                .is_some_and(|lit| lit.captures.iter().all(|capture| self.is_materializable(capture)))
            || self
                .tuple_lit_elems(a)
                .is_some_and(|elems| elems.iter().all(|elem| self.is_materializable(elem)))
            || self.is_empty_list_lit(a)
    }

    /// Match a subject type against a specific literal/shape witness.
    /// `Yes` means definite match, `No` means definite miss, `Opaque`
    /// means the overlap is non-empty but not precise enough to decide.
    fn match_literal_ty(&mut self, subject: &Self::Ty, expected: &Self::Ty) -> TypeMatch {
        if self.is_literal(subject) {
            if self.is_equivalent(subject, expected) {
                Yes
            } else {
                let overlap = self.intersect(subject.clone(), expected.clone());
                if self.is_empty(&overlap) { No } else { Opaque }
            }
        } else {
            let overlap = self.intersect(subject.clone(), expected.clone());
            if self.is_empty(&overlap) {
                No
            } else if self.is_subtype(subject, expected) {
                Yes
            } else {
                Opaque
            }
        }
    }
}

impl<T: ClosureTypes> LiteralTypes for T {}

#[cfg(test)]
mod conformance_tests {
    use super::*;
    use crate::types::{ConcreteTypes, Types};

    macro_rules! literal_helper_conformance_tests {
        ($mod_name:ident, $ctor:expr) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn scalar_literal_recognizes_all_scalar_const_forms() {
                    let mut t = $ctor;
                    let int_lit = t.int_lit(7);
                    let float_lit = t.float_lit(3.5);
                    let nil = t.nil();
                    let tru = t.bool_lit(true);
                    let ok = t.atom_lit("ok");
                    let int = t.int();
                    assert_eq!(t.scalar_literal(&int_lit), Some(ScalarLiteral::Int(7)));
                    assert_eq!(t.scalar_literal(&float_lit), Some(ScalarLiteral::Float(3.5)));
                    assert_eq!(t.scalar_literal(&nil), Some(ScalarLiteral::Nil));
                    assert_eq!(t.scalar_literal(&tru), Some(ScalarLiteral::Bool(true)));
                    assert_eq!(t.scalar_literal(&ok), Some(ScalarLiteral::Atom("ok".to_string())));
                    assert_eq!(t.scalar_literal(&int), None);
                }

                #[test]
                fn is_materializable_recognizes_recursive_literal_shapes() {
                    let mut t = $ctor;
                    let cap = t.int_lit(7);
                    let ok = t.atom_lit("ok");
                    let one = t.int_lit(1);
                    let wide = t.int();
                    let closure = t.closure_lit(crate::fz_ir::FnId(9).into(), vec![cap], 0);
                    let tuple = t.tuple(&[ok.clone(), one]);
                    let empty_list = t.empty_list();
                    let wide_tuple = t.tuple(&[ok, wide]);
                    assert!(t.is_materializable(&closure));
                    assert!(t.is_materializable(&tuple));
                    assert!(t.is_materializable(&empty_list));
                    assert!(!t.is_materializable(&wide_tuple));
                }

                #[test]
                fn match_literal_ty_triages_yes_no_and_opaque() {
                    let mut t = $ctor;
                    let int = t.int();
                    let one = t.int_lit(1);
                    let two = t.int_lit(2);
                    assert_eq!(t.match_literal_ty(&one, &one), TypeMatch::Yes);
                    assert_eq!(t.match_literal_ty(&one, &two), TypeMatch::No);
                    assert_eq!(t.match_literal_ty(&int, &one), TypeMatch::Opaque);
                }

                #[test]
                #[allow(clippy::approx_constant)]
                fn is_literal_recognizes_scalar_singletons() {
                    let mut t = $ctor;
                    let int = t.int_lit(42);
                    let float = t.float_lit(3.14);
                    let atom = t.atom_lit("foo");
                    let nil = t.nil();
                    let tru = t.bool_lit(true);
                    let fls = t.bool_lit(false);
                    assert!(t.is_literal(&int));
                    assert!(t.is_literal(&float));
                    assert!(t.is_literal(&atom));
                    assert!(t.is_literal(&nil));
                    assert!(t.is_literal(&tru));
                    assert!(t.is_literal(&fls));
                }

                #[test]
                fn is_literal_rejects_wide_types() {
                    let mut t = $ctor;
                    let int = t.int();
                    let float = t.float();
                    let any = t.any();
                    let bool_t = t.bool();
                    assert!(!t.is_literal(&int));
                    assert!(!t.is_literal(&float));
                    assert!(!t.is_literal(&any));
                    assert!(!t.is_literal(&bool_t));
                }

                #[test]
                fn is_literal_recognizes_literal_tuple() {
                    let mut t = $ctor;
                    let num = t.atom_lit("num");
                    let value = t.int_lit(42);
                    let tuple = t.tuple(&[num, value]);
                    assert!(t.is_literal(&tuple));
                }

                #[test]
                fn is_literal_rejects_tuple_with_wide_element() {
                    let mut t = $ctor;
                    let num = t.atom_lit("num");
                    let value = t.int();
                    let tuple = t.tuple(&[num, value]);
                    assert!(!t.is_literal(&tuple));
                }

                #[test]
                fn as_bool_lit_recognizes_true_and_false() {
                    let mut t = $ctor;
                    let tru = t.bool_lit(true);
                    let fls = t.bool_lit(false);
                    let wide = t.bool();
                    assert_eq!(t.as_bool_lit(&tru), Some(true));
                    assert_eq!(t.as_bool_lit(&fls), Some(false));
                    assert_eq!(t.as_bool_lit(&wide), None);
                }
            }
        };
    }

    literal_helper_conformance_tests!(concrete_types_literals, ConcreteTypes);
}
