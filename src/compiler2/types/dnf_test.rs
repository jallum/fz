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
