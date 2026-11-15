//! The facts settled when a type is interned, read through `TyCtx`.

use super::*;

fn attrs(t: &Types, ty: Ty) -> attrs::TyAttrs {
    t.ctx().attrs(&ty)
}

/// A variable anywhere in a type shows through every enclosing structure.
#[test]
fn a_variable_shows_through_every_structure_that_holds_it() {
    let mut t = Types::new();
    let var = t.type_var(TypeVarId(0));
    let int = t.int();
    let inner = t.tuple(&[int, var]);
    let in_list = t.list(inner);
    let in_resource = t.resource(inner);
    let in_arrow = t.arrow(&[int], inner);

    for ty in [var, inner, in_list, in_resource, in_arrow] {
        assert!(attrs(&t, ty).has_vars());
        assert!(attrs(&t, ty).has_open_vars());
    }
    assert!(!attrs(&t, int).has_vars());
    assert!(!attrs(&t, int).has_open_vars());
}

/// A closure literal's own arrow binds the variables of its arguments and
/// result, so they are not open; the types it captured are values and are.
#[test]
fn a_closure_literals_own_arrow_binds_its_variables_but_its_captures_do_not() {
    let mut t = Types::new();
    let int = t.int();
    let var = t.type_var(TypeVarId(0));
    let bare = t.closure_lit(ClosureTarget(1), vec![int], 2);
    let capturing_var = t.closure_lit(ClosureTarget(2), vec![var], 2);

    assert!(attrs(&t, bare).has_vars());
    assert!(!attrs(&t, bare).has_open_vars());
    assert!(attrs(&t, capturing_var).has_open_vars());
}

/// Whether a closure literal occurs is a fact of the type alone: no literal has
/// been registered with the world here, and the answer does not wait for one.
#[test]
fn a_closure_literal_is_mentioned_wherever_it_sits_registered_or_not() {
    let mut t = Types::new();
    let int = t.int();
    let closure = t.closure_lit(ClosureTarget(3), vec![int], 1);
    let nested = t.tuple(&[int, closure]);
    let plain_arrow = t.arrow(&[int], int);

    assert!(attrs(&t, closure).mentions_closure_literal());
    assert!(attrs(&t, nested).mentions_closure_literal());
    assert!(!attrs(&t, plain_arrow).mentions_closure_literal());
    assert!(!attrs(&t, int).mentions_closure_literal());
}

/// A structural address is minted only at a list, a callable or a variable, so
/// a type with none of them at any depth has no address to mint.
#[test]
fn a_type_is_path_free_exactly_when_no_list_callable_or_variable_sits_below_it() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();
    let list = t.list(int);
    let closure = t.closure_lit(ClosureTarget(4), vec![int], 1);
    let var = t.type_var(TypeVarId(0));
    let plain = t.tuple(&[int, atom]);

    assert!(attrs(&t, plain).path_free());
    for leaf in [list, closure, var] {
        let deep = (0..8).fold(leaf, |inner, _| t.tuple(&[inner, int]));
        assert!(!attrs(&t, deep).path_free());
    }
}

/// A type is literal blind when no specific atom sits where a value can: the
/// arguments and result of an arrow are its surface, so a literal there does
/// not count, while one it captured does.
#[test]
fn a_type_is_literal_blind_unless_a_specific_atom_sits_where_a_value_can() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();
    let ok = t.atom_lit("ok");
    let blind_tuple = t.tuple(&[int, atom]);
    let literal_tuple = t.tuple(&[int, ok]);
    let literal_in_list = t.list(literal_tuple);
    let literal_in_surface = t.arrow(&[ok], ok);
    let literal_captured = t.closure_lit(ClosureTarget(5), vec![ok], 1);

    assert!(attrs(&t, blind_tuple).literal_blind());
    assert!(!attrs(&t, ok).literal_blind());
    assert!(!attrs(&t, literal_tuple).literal_blind());
    assert!(!attrs(&t, literal_in_list).literal_blind());
    assert!(attrs(&t, literal_in_surface).literal_blind());
    assert!(!attrs(&t, literal_captured).literal_blind());
}

/// `is_literal_blind` is `widen_literals(a) == a`, answered without interning.
#[test]
fn literal_blindness_is_the_fixed_point_of_widening() {
    let mut t = Types::new();
    let int = t.int();
    let ok = t.atom_lit("ok");
    let closure = t.closure_lit(ClosureTarget(6), vec![ok], 1);
    let surface = t.arrow(&[ok], int);
    let tuple = t.tuple(&[ok, int]);
    let list = t.list(tuple);

    for ty in [int, ok, closure, surface, tuple, list] {
        let widened = t.widen_literals(&ty);
        assert_eq!(t.is_literal_blind(&ty), widened == ty);
    }
}
