//! What the one absorber guarantees about an axis it has finished with.

use super::*;
use crate::compiler2::types::Types;

fn absorbed<T: Clone + 'static>(t: &Types, mut clauses: Vec<Conj<T>>, view: &AxisView<T>) -> Vec<Conj<T>> {
    let cx = t.ctx();
    let subtype = &|narrower: &Ty, wider: &Ty| cx.descr(narrower).is_subtype(cx, cx.descr(wider));
    let covers = &|wider: &Descr, narrower: &Descr| narrower.is_subtype(cx, wider);
    absorb_axis(cx, &mut clauses, subtype, covers, view);
    clauses
}

/// An axis has ONE top, the clause with no factors. The widest sig denotes the
/// same set, so it is a second spelling of it and is rewritten — otherwise the
/// two cover each other, the coverage walk keeps whichever it visited second,
/// and one set takes two identities.
#[test]
fn the_widest_sig_and_the_contentless_clause_are_one_spelling() {
    let mut t = Types::new();
    let any = t.any();
    let widest = Conj::pos_of(ListSig {
        empty: true,
        elem: Some(any),
    });
    assert_eq!(
        vec![Conj::top()],
        absorbed(&t, vec![widest.clone()], &LISTS),
        "the widest list sig IS every list"
    );
    let forward = absorbed(&t, vec![Conj::top(), widest.clone()], &LISTS);
    let backward = absorbed(&t, vec![widest, Conj::top()], &LISTS);
    assert_eq!(forward, backward, "the survivor followed the index, not the axis");
    assert_eq!(vec![Conj::top()], forward);
}

/// The contentless clause constrains nothing, so the narrower clauses beside it
/// add nothing whatever order they arrive in.
#[test]
fn a_contentless_clause_beside_narrower_sigs_absorbs_them_either_way() {
    let mut t = Types::new();
    let int = t.int();
    let narrow = Conj::pos_of(ListSig {
        empty: false,
        elem: Some(int),
    });
    let forward = absorbed(&t, vec![Conj::top(), narrow.clone()], &LISTS);
    let backward = absorbed(&t, vec![narrow, Conj::top()], &LISTS);
    assert_eq!(forward, backward);
    assert_eq!(vec![Conj::top()], forward);
}

/// No union of positive-only tuple clauses is every tuple — a positive sig
/// fixes an arity — so the tuple axis answers its plain case structurally and
/// never pays the exact question for it. The contentless clause still swallows
/// its siblings there, because that answer belongs to no axis.
#[test]
fn a_positive_tuple_axis_is_never_its_top_but_a_contentless_clause_is() {
    let mut t = Types::new();
    let int = t.int();
    let any = t.any();
    let pair = Conj::pos_of(TupleSig { elems: vec![int, int] });
    let widest_pair = Conj::pos_of(TupleSig { elems: vec![any, any] });
    assert_eq!(
        vec![Conj::pos_of(TupleSig { elems: vec![any, any] })],
        absorbed(&t, vec![pair.clone(), widest_pair], &TUPLES),
        "the wider pair absorbs the narrower one and is still only the pairs"
    );
    let forward = absorbed(&t, vec![Conj::top(), pair.clone()], &TUPLES);
    let backward = absorbed(&t, vec![pair, Conj::top()], &TUPLES);
    assert_eq!(forward, backward);
    assert_eq!(vec![Conj::top()], forward);
}

/// The first of the three surpluses that keep the callable axis out of the
/// absorber, measured rather than preferred (see the module doc for all
/// three).
///
/// An arrow is also how the compiler writes a record down: `ActivationKey`
/// keeps a specialization's inputs and result as one arrow's params and result
/// and reads them back with `Types::arrow_params`. The kernel calls an arrow
/// whose result is every value the WHOLE callable axis, so the top rule would
/// answer that question and replace the key with the contentless clause --
/// after which the same reader finds no params at all, and two activations
/// over different inputs key one specialization.
#[test]
fn absorbing_the_callable_axis_would_erase_the_inputs_a_key_reads_back() {
    let mut t = Types::new();
    let any = t.any();
    let int = t.int();
    let key_shaped = t.arrow(&[any, int], any);
    let fun_top = t.intern(Descr::fun_top());

    assert!(
        t.is_subtype(&key_shaped, &fun_top) && t.is_subtype(&fun_top, &key_shaped),
        "the hazard this test guards must exist: the kernel already calls this arrow every callable",
    );
    assert_eq!(
        vec![any, int],
        t.arrow_params(&key_shaped),
        "and its params are what a key reads back out of it",
    );

    let clauses = t.descr(&key_shaped).funcs.clone();
    assert_eq!(
        vec![Conj::top()],
        absorbed(&t, clauses, &FUNCS),
        "so the absorber would answer the denotation and throw the inputs away",
    );
    assert!(
        t.arrow_params(&fun_top).is_empty(),
        "there is nothing left to read out of the clause it would leave behind",
    );
}
