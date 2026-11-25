use super::*;

fn clause(pos: &[u8], neg: &[u8]) -> Conj<u8> {
    Conj {
        pos: pos.to_vec(),
        neg: neg.to_vec(),
    }
}

/// A difference is the minuend met with the subtrahend's negation, whichever
/// side is empty, top, or a real disjunction.
#[test]
fn diff_is_intersect_with_the_negation() {
    let sides: [Vec<Conj<u8>>; 5] = [
        vec![],
        vec![Conj::top()],
        vec![clause(&[1], &[])],
        vec![clause(&[1], &[2]), clause(&[3], &[])],
        vec![clause(&[2], &[]), clause(&[], &[3])],
    ];
    for a in &sides {
        for b in &sides {
            assert!(dnf_diff(a, b) == dnf_intersect(a, &dnf_neg(b)), "{a:?} minus {b:?}");
        }
    }
}

/// Nothing minus anything is nothing.
#[test]
fn an_empty_minuend_stays_empty() {
    assert!(dnf_diff::<u8>(&[], &[clause(&[1], &[2])]).is_empty());
}

/// Whether the DNF holds at a truth assignment of its literals, read as sets: a clause holds when every
/// positive literal is true and every negative one false.
fn holds(dnf: &[Conj<u8>], truth: u8) -> bool {
    let is_true = |lit: &u8| truth & (1 << lit) != 0;
    dnf.iter()
        .any(|c| c.pos.iter().all(is_true) && !c.neg.iter().any(is_true))
}

/// An intersection never keeps a clause that another kept clause covers: the covered clause adds literals
/// to a clause already kept, so it names nothing the kept one does not.
#[test]
fn an_intersection_keeps_no_clause_another_kept_clause_covers() {
    let a = [clause(&[1], &[])];
    let b = [Conj::top(), clause(&[], &[2])];
    assert_eq!(dnf_intersect(&a, &b), vec![clause(&[1], &[])]);
}

/// The wider clause survives whichever order the product meets the two in.
#[test]
fn a_later_wider_clause_replaces_the_narrower_ones_already_kept() {
    let a = [clause(&[1], &[2]), clause(&[1, 3], &[]), clause(&[1], &[])];
    let out = dnf_intersect(&a, &[Conj::top()]);
    assert_eq!(out, vec![clause(&[1], &[])]);
}

/// Dropping covered clauses changes no denotation: at every assignment of literals the intersection holds
/// exactly when both sides do.
#[test]
fn dropping_covered_clauses_keeps_the_intersection_exact() {
    let clauses = [
        Conj::top(),
        clause(&[1], &[]),
        clause(&[1], &[2]),
        clause(&[1, 2], &[]),
        clause(&[], &[3]),
        clause(&[2], &[3]),
    ];
    for a in clauses.iter().map(|c| vec![c.clone()]) {
        for b in [
            vec![clauses[0].clone(), clauses[2].clone()],
            vec![clauses[1].clone(), clauses[4].clone(), clauses[5].clone()],
        ] {
            let product = dnf_intersect(&a, &b);
            for truth in 0..16u8 {
                assert_eq!(
                    holds(&product, truth),
                    holds(&a, truth) && holds(&b, truth),
                    "{a:?} and {b:?} at {truth:04b}"
                );
            }
        }
    }
}

/// The negation of a union of map literals is two clauses however many members the union has. Each member
/// `m` negates to `not m` or the struct exclusion's complement; of the 2^n ways to pick one per member, every
/// pick that takes the complement at least once is covered by the pick that takes it everywhere.
#[test]
fn the_negation_of_a_union_of_clauses_sharing_one_negative_is_two_clauses() {
    const EXCLUSION: u8 = 200;
    let members: Vec<Conj<u8>> = (0..12).map(|i| clause(&[i], &[EXCLUSION])).collect();
    assert_eq!(dnf_neg(&members).len(), 2);
}
