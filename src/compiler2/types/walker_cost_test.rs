//! A walker over interned types costs the number of distinct handles it
//! reaches, not the size of the tree they unfold to.
//!
//! A doubling type `{t, t}` nested `DEPTH` deep is `DEPTH` handles and a tree of
//! `2^DEPTH` leaves. Every test observes the cost as descriptor reads, which
//! count the work of a walk however it is written, rather than elapsed time.

use super::*;

const DEPTH: usize = 20;

/// Reads of any one walk of the tower that stay linear in its handles.
const LINEAR_IN_DEPTH: usize = 8 * DEPTH;

fn doubling_tower(t: &mut Types, leaf: Ty, depth: usize) -> Ty {
    (0..depth).fold(leaf, |inner, _| t.tuple(&[inner, inner]))
}

fn reads_during<R>(t: &mut Types, walk: impl FnOnce(&mut Types) -> R) -> (R, usize) {
    let before = t.descr_reads();
    let answer = walk(t);
    (answer, t.descr_reads() - before)
}

/// The context-free questions are answered where the type is interned, so
/// asking them of a doubling tower reads no descriptor below its root.
#[test]
fn context_free_questions_of_a_doubling_tower_are_answered_from_its_handle() {
    let mut t = Types::new();
    let int = t.int();
    let tower = doubling_tower(&mut t, int, DEPTH);

    let (answers, reads) = reads_during(&mut t, |t| {
        (
            t.has_vars(&tower),
            t.has_open_vars(&tower),
            t.is_literal_blind(&tower),
            t.erase_closure_identity(&tower) == tower,
        )
    });

    assert_eq!(answers, (false, false, true, true));
    assert!(
        reads <= LINEAR_IN_DEPTH,
        "{reads} descriptor reads for a tower of {DEPTH}"
    );
}

/// A type with no list, callable or variable has nowhere to mint an address
/// variable, so its convergence class is itself and no walk is needed to say so.
#[test]
fn the_convergence_class_of_a_path_free_tower_is_the_tower() {
    let mut t = Types::new();
    let int = t.int();
    let tower = doubling_tower(&mut t, int, DEPTH);

    let (class, reads) = reads_during(&mut t, |t| {
        t.convergence_class_at(&tower, &[], ClassReach::Demanded, KeyCollapse::Recursive)
    });

    assert_eq!(class, tower);
    assert!(
        reads <= LINEAR_IN_DEPTH,
        "{reads} descriptor reads for a tower of {DEPTH}"
    );
}

/// Whether a doubling tuple is an atom is decided by its own clause: an
/// interned coordinate is inhabited unless it is the one bottom type, so the
/// coordinates are not walked down to their leaves.
#[test]
fn a_doubling_tower_is_compared_to_an_atom_without_walking_its_tree() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();
    let tower = doubling_tower(&mut t, int, DEPTH);

    let (is_atom, reads) = reads_during(&mut t, |t| t.is_subtype(&tower, &atom));

    assert!(!is_atom);
    assert!(
        reads <= LINEAR_IN_DEPTH,
        "{reads} descriptor reads for a tower of {DEPTH}"
    );
}
