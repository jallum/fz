//! Emptiness and subtype recursion must not fan out per branch.
//!
//! A synthetic regular (mu-)type built directly through
//! [`Types::intern_regular_component`] does not reproduce the blowup this
//! guards against: minimization already collapses two constructions of the
//! same bisimilar language to one `Ty` at intern time (see
//! `regular_component_interns_bisimilar_unrollings_once` in
//! `types_test.rs`), so a direct comparison never reaches the exponential
//! path. The real pathology is between two NOT-YET-unified representations
//! of the same recursive language, which only type inference's widening
//! produces. This test drives the actual two-state mutual recursion fixture
//! through the compiler.

use super::{Conj, Memo, MemoKey, Operand, TupleSig, tuple_clause_empty};
use crate::compiler2::types::Types;
use crate::compiler2::types::descr::Descr;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::exec::runtime::DbgCapture;
use crate::telemetry::ConfiguredTelemetry;

const MUTUAL_TUPLE_STATES_SOURCE: &str = r#"
def even([]), do: {:even, 0}
def even([_ | t]), do: {:e, odd(t)}

def odd([]), do: {:odd, 0}
def odd([_ | t]), do: {:o, even(t)}

def main() do
  dbg(even([1, 2]))
end
"#;

/// Without the memo this hangs forever: `is_equivalent -> is_subtype ->
/// phi_tuple` recomputes the same tuple-emptiness subproblem across every
/// branch of the two-state mutual recursion, fanning out `arity^|negs|`.
/// With it the compile terminates and the fixture's return ladder is pinned
/// per activation in `drive_test::RETURN_LADDERS`, so the cost is measured
/// there rather than by a wall clock here.
#[test]
fn mutual_recursive_tuple_states_do_not_blow_up_emptiness() {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("mutual_tuple_states".to_string()),
        text: MUTUAL_TUPLE_STATES_SOURCE.to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.run_root_interp(root_id).unwrap_or_else(|error| {
        let diagnostic = dbg.lines().join("\n");
        panic!(
            "Compiler2 backend interpreter should run the two-state mutual recursion fixture: {error}; dbg={diagnostic}"
        );
    });

    assert_eq!(
        dbg.lines().as_slice(),
        ["{:e, {:o, {:even, 0}}}"],
        "even([1, 2]) alternates state through odd/even exactly once per element",
    );
}

/// White-box proof that a repeated subproblem is answered from the cache,
/// not recomputed: `compute` runs once for two identical queries, and the
/// second is counted as a hit.
#[test]
fn memo_answers_a_repeated_witness_from_the_cache() {
    let mut memo = Memo::default();
    let key = MemoKey::Descr(Operand::built(Descr::none()));
    let mut compute_calls = 0;

    let first = memo.query(key.clone(), |_memo| {
        compute_calls += 1;
        false
    });
    let second = memo.query(key, |_memo| {
        compute_calls += 1;
        false
    });

    assert_eq!(first, second, "the cached answer must match the computed one");
    assert_eq!(compute_calls, 1, "the second query must hit the cache, not recompute");
    assert_eq!(memo.misses, 1, "one miss: the first, computing query");
    assert_eq!(memo.hits, 1, "one hit: the second, cached query");
}

/// White-box proof of the coinductive back-edge: a subproblem that only
/// depends on itself is assumed empty on re-entry, without recursing
/// further, and that assumption is cached once its (trivial, one-member)
/// component closes.
#[test]
fn memo_closes_a_self_referential_component_as_empty() {
    let mut memo = Memo::default();
    let key = MemoKey::Descr(Operand::built(Descr::none()));

    let result = memo.query(key.clone(), |memo| {
        // Re-entering `key` while it is still open on the DFS stack is the
        // coinductive back-edge: it must return `true` (assume empty)
        // without invoking `compute` again.
        memo.query(key.clone(), |_memo| unreachable!("a back-edge must not recompute"))
    });

    assert!(
        result,
        "a subproblem that only depends on itself is coinductively empty"
    );
    assert_eq!(
        memo.results.get(&key),
        Some(&true),
        "the closed component's answer is cached"
    );
    assert_eq!(
        memo.hits, 0,
        "neither call finds a cached RESULT yet: the inner one is a fresh back-edge, not a result hit"
    );
    assert_eq!(
        memo.misses, 2,
        "both the outer call and the in-flight back-edge miss the results cache"
    );
}

/// `Operand` is the memo key's payload: a `Ty` this call was already handed,
/// or a descriptor an algebra step just built. Its size proves the second
/// case cannot inline a whole `Descr` (a `Vec<BrandCase<Ty>>`, at least three
/// words before a single case) — a built descriptor must sit behind a shared
/// pointer, so cloning an `Operand` can never re-walk one.
#[test]
fn operand_cannot_inline_a_descriptor() {
    assert!(
        std::mem::size_of::<Operand>() <= 2 * std::mem::size_of::<usize>(),
        "an Operand must be at most a discriminant plus one pointer-sized field, \
         proving Operand::Built cannot hold a Descr inline"
    );
}

/// White-box proof that an untouched coordinate is keyed on the `Ty` it
/// already is, not on a rebuilt copy of its descriptor: a plain
/// single-positive tuple clause over two already-interned types must leave
/// exactly one `Operand::Ty`-only key in the memo, never an `Operand::Built`
/// one, because nothing here ever needed to intersect, diff, or otherwise
/// rebuild either coordinate.
#[test]
fn tuple_clause_empty_keys_untouched_coordinates_by_ty() {
    let mut types = Types::new();
    let int = types.int();
    let atom = types.atom();
    let cx = types.ctx();
    let mut memo = Memo::default();

    let clause = Conj::pos_of(TupleSig { elems: vec![int, atom] });
    let empty = tuple_clause_empty(cx, &clause, &mut memo);

    assert!(!empty, "int × atom is a nonempty product");
    let expected_key = MemoKey::Tuple(vec![Operand::Ty(int), Operand::Ty(atom)], Vec::new());
    assert_eq!(
        memo.results.get(&expected_key),
        Some(&false),
        "the cached key must be the two coordinates' own Ty identity, not a rebuilt descriptor"
    );
}
