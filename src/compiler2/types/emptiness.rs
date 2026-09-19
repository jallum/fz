//! Per-axis emptiness algorithms for the interned descriptor kernel.

use crate::fz_ir::FnId;
use std::collections::{BTreeMap, HashSet};

use super::conj::Conj;
use super::descr::Descr;
use super::sigs::{ArrowSig, ClosureLit, ListSig, ListSigOf, MapSig, ResourceSig, TupleSig};
use super::{MapKey, Ty, TyCtx};

/// Coinductive assumption set for one top-level emptiness query. Emptiness
/// over recursive descriptors is a greatest fixpoint: a query that re-enters a
/// descriptor already `in_flight` assumes it empty, and the assumption is
/// discharged if the whole cycle checks out.
#[derive(Default)]
pub(crate) struct Memo {
    pub(super) in_flight: HashSet<Descr>,
}

pub(crate) fn tuple_clause_empty(cx: TyCtx<'_>, c: &Conj<TupleSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        return false;
    }
    let arity = c.pos[0].elems.len();
    if c.pos.iter().any(|p| p.elems.len() != arity) {
        return true;
    }
    let mut t: Vec<Descr> = c.pos[0].elems.iter().map(|ty| cx.descr(ty).clone()).collect();
    for p in &c.pos[1..] {
        for (i, e) in p.elems.iter().enumerate() {
            t[i] = t[i].intersect(cx.descr(e));
        }
    }
    let negs: Vec<Vec<Descr>> = c
        .neg
        .iter()
        .filter(|n| n.elems.len() == arity)
        .map(|n| n.elems.iter().map(|ty| cx.descr(ty).clone()).collect())
        .collect();
    phi_tuple(cx, &t, &negs, memo)
}

/// Is the product `∏t` minus the union of the products `∏n` empty?
///
/// Exact, and stated over DESCRIPTORS rather than interned coordinates, so a
/// caller can decide `∏t ⊆ ⋃∏n` for rectangles it built but never interned.
/// Every entry of `n` must have the same arity as `t`; a mismatched arity
/// subtracts nothing and belongs to the caller's filter.
pub(super) fn phi_tuple(cx: TyCtx<'_>, t: &[Descr], n: &[Vec<Descr>], memo: &mut Memo) -> bool {
    // One empty coordinate empties the whole product — no negation needed.
    // Checking at entry prunes every recursive branch whose diff/intersect
    // zeroed a coordinate; without this the recursion only discovers the
    // emptiness at the leaves, after fanning out arity^|negs| branches.
    if t.iter().any(|d| d.is_empty_memo(cx, memo)) {
        return true;
    }
    let Some((head, rest)) = n.split_first() else {
        return false;
    };
    // A negation disjoint from the product on any coordinate subtracts
    // nothing: drop it instead of splitting on it.
    if head
        .iter()
        .zip(t)
        .any(|(h, ti)| ti.intersect(h).is_empty_memo(cx, memo))
    {
        return phi_tuple(cx, t, rest, memo);
    }
    for i in 0..t.len() {
        let mut t_split = t.to_vec();
        for j in 0..i {
            t_split[j] = t_split[j].intersect(&head[j]);
        }
        t_split[i] = t_split[i].diff(&head[i]);
        if !phi_tuple(cx, &t_split, rest, memo) {
            return false;
        }
    }
    true
}

/// The positive fold's evidence about the NONEMPTY fragment of a list-clause
/// intersection ("unknown is not none"): before any sig is folded the
/// fragment is unconstrained — a distinct state from proven-empty. An
/// exact-empty sig (`elem: None`) admits no nonempty lists, so it forces
/// `Empty`, and `Empty` absorbs everything folded after it.
enum ElemEvidence {
    Unconstrained,
    Empty,
    Inhabited(Box<Descr>),
}

impl ElemEvidence {
    /// Fold one positive sig's element constraint into the cell. `Empty` is
    /// absorbing; every other transition is a plain set intersection, so
    /// inhabited evidence degrades to `Empty` only on genuine set facts (an
    /// exact-empty sig, or an intersection that empties).
    fn meet(self, cx: TyCtx<'_>, sig_elem: Option<Ty>, memo: &mut Memo) -> Self {
        let Some(elem) = sig_elem else {
            return Self::Empty;
        };
        let next = match self {
            Self::Empty => return Self::Empty,
            Self::Unconstrained => cx.descr(&elem).clone(),
            Self::Inhabited(prev) => prev.intersect(cx.descr(&elem)),
        };
        if next.is_empty_memo(cx, memo) {
            Self::Empty
        } else {
            Self::Inhabited(Box::new(next))
        }
    }

    /// The fragment's element descriptor, `None` meaning ONLY "proven empty".
    fn fragment(self) -> Option<Descr> {
        match self {
            Self::Unconstrained => Some(Descr::any()),
            Self::Empty => None,
            Self::Inhabited(d) => Some(*d),
        }
    }
}

/// What a list clause DENOTES, read off its factors once.
///
/// A `ListSig` denotes `[]` (when `empty`) together with every non-empty list
/// whose elements all lie in `elem`, so a whole clause says only two things:
/// does it hold `[]`, and which non-empty lists does it keep. Everything that
/// reads a list clause -- emptiness here, the normal form the persistence
/// boundary writes, the canonical rendering -- reads it through this one
/// answer, so none of them can disagree about what a clause means.
pub(crate) struct ListDenotation {
    pub(crate) holds_empty: bool,
    /// The non-empty lists the clause keeps, absent when it keeps none.
    pub(crate) non_empty: Option<NonEmptyLists>,
}

/// Every non-empty list over `elem`, except those whose elements all lie in
/// one of `minus`.
///
/// Each entry of `minus` is already met with `elem`, which is exact
/// (`L(F) \ L(N) = L(F) \ L(F ∩ N)`) and is what makes a subtraction that
/// removes nothing recognizable: it survives only when it removes some of
/// `elem` and not all of it.
pub(crate) struct NonEmptyLists {
    pub(crate) elem: Descr,
    pub(crate) minus: Vec<Descr>,
}

/// Whether a list clause holds `[]`, read off the `empty` flags alone.
///
/// `[]` is in every positive that carries the flag and in no negative that
/// does, which is the whole rule: it touches no element, so it is the same
/// answer before and after a substitution, and the axis merge across a clause
/// set may ask it without a `TyCtx`.
pub(super) fn clause_holds_empty<R>(c: &Conj<ListSigOf<R>>) -> bool {
    c.pos.iter().all(|p| p.empty) && !c.neg.iter().any(|n| n.empty)
}

/// `None` when the clause denotes nothing.
///
/// A subtraction swallows the non-empty fragment on its OWN or not at all: as
/// soon as no single `minus` covers `elem`, pick one element outside each and
/// put them in one list -- it is over `elem` and outside every `minus`. That
/// single-negative rule is the one the axis rewrites above must not outrun.
pub(crate) fn list_denotation(cx: TyCtx<'_>, c: &Conj<ListSig>, memo: &mut Memo) -> Option<ListDenotation> {
    let holds_empty = clause_holds_empty(c);
    let just_empty = || {
        holds_empty.then_some(ListDenotation {
            holds_empty: true,
            non_empty: None,
        })
    };
    let mut evidence = ElemEvidence::Unconstrained;
    for p in &c.pos {
        evidence = evidence.meet(cx, p.elem, memo);
    }
    let Some(elem) = evidence.fragment() else {
        return just_empty();
    };
    let mut minus: Vec<Descr> = Vec::new();
    for n in &c.neg {
        // A negative with no element denotes `[]` alone, so it has already
        // been read into `holds_empty` and takes nothing off the fragment.
        let Some(cut) = n.elem else { continue };
        let cut = elem.intersect(cx.descr(&cut));
        if cut.is_empty_memo(cx, memo) {
            continue;
        }
        if elem.diff(&cut).is_empty_memo(cx, memo) {
            return just_empty();
        }
        if !minus.contains(&cut) {
            minus.push(cut);
        }
    }
    Some(ListDenotation {
        holds_empty,
        non_empty: Some(NonEmptyLists { elem, minus }),
    })
}

pub(crate) fn list_clause_empty(cx: TyCtx<'_>, c: &Conj<ListSig>, memo: &mut Memo) -> bool {
    list_denotation(cx, c, memo).is_none()
}

pub(crate) fn resource_clause_empty(cx: TyCtx<'_>, c: &Conj<ResourceSig>, memo: &mut Memo) -> bool {
    let payload = if c.pos.is_empty() {
        Descr::any()
    } else {
        let mut payload = cx.descr(&c.pos[0].payload).clone();
        for p in &c.pos[1..] {
            payload = payload.intersect(cx.descr(&p.payload));
        }
        if payload.is_empty_memo(cx, memo) {
            return true;
        }
        payload
    };
    let negatives: Vec<Vec<Descr>> = c
        .neg
        .iter()
        .map(|negative| vec![cx.descr(&negative.payload).clone()])
        .collect();
    phi_tuple(cx, &[payload], &negatives, memo)
}

fn arrow_input(sig: &ArrowSig) -> Descr {
    Descr::tuple_of(sig.args.clone())
}

/// Whether two closure literals can name ONE value: the same brand, or either
/// one anonymous — an anonymous literal is every brand at once.
fn closure_brands_meet(a: Option<FnId>, b: Option<FnId>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a == b,
        _ => true,
    }
}

/// Whether every brand `pos` names, `neg` names too. An anonymous `neg`
/// subtracts every brand; a branded `neg` subtracts only its own, and never
/// covers an anonymous `pos`, which names every other brand as well.
fn closure_brand_inside(pos: Option<FnId>, neg: Option<FnId>) -> bool {
    match (pos, neg) {
        (_, None) => true,
        (Some(pos), Some(neg)) => pos == neg,
        (None, Some(_)) => false,
    }
}

/// Whether one partition of `positives` witnesses a function outside
/// `input -> output`.
///
/// A positive is either selected, which removes its input region from the
/// remaining witness input, or unselected, which intersects its return into
/// the remaining witness output. Both fragments only shrink, so an empty
/// fragment rules out every descendant partition. This is the exact
/// partition law without encoding a partition in a fixed-width integer.
fn arrow_partition_witness(
    cx: TyCtx<'_>,
    positives: &[ArrowSig],
    next: usize,
    remaining_input: Descr,
    remaining_output: Descr,
    memo: &mut Memo,
) -> bool {
    if remaining_input.is_empty_memo(cx, memo) || remaining_output.is_empty_memo(cx, memo) {
        return false;
    }
    let Some(positive) = positives.get(next) else {
        return true;
    };

    let selected_input = remaining_input.diff(&arrow_input(positive));
    if arrow_partition_witness(cx, positives, next + 1, selected_input, remaining_output.clone(), memo) {
        return true;
    }

    let unselected_output = remaining_output.intersect(cx.descr(&positive.ret));
    arrow_partition_witness(cx, positives, next + 1, remaining_input, unselected_output, memo)
}

pub(crate) fn func_clause_empty(cx: TyCtx<'_>, c: &Conj<ArrowSig>, memo: &mut Memo) -> bool {
    let p = &c.pos;
    let n = &c.neg;

    let pos_lits: Vec<&ClosureLit> = p.iter().filter_map(|s| s.lit.as_ref()).collect();
    // A closure holds exactly one value per capture slot, so a literal whose
    // capture TYPE is empty denotes nothing -- however it got that way. An
    // anonymous literal is every brand at once, so it MERGES with a branded
    // one instead of staying distinct from it, and the merged literal's
    // capture is the two captures' intersection; one brand at two capture
    // types merges the same way. Asking each literal about its own captures
    // covers both, where the pairwise loop below can only see pairs that
    // survived the merge.
    if pos_lits
        .iter()
        .any(|lit| lit.captures.iter().any(|c| cx.descr(c).is_empty_memo(cx, memo)))
    {
        return true;
    }
    for i in 0..pos_lits.len() {
        for j in (i + 1)..pos_lits.len() {
            if !closure_brands_meet(pos_lits[i].fn_id, pos_lits[j].fn_id)
                || pos_lits[i].captures.len() != pos_lits[j].captures.len()
            {
                return true;
            }
            for (a, b) in pos_lits[i].captures.iter().zip(&pos_lits[j].captures) {
                if cx.descr(a).intersect(cx.descr(b)).is_empty_memo(cx, memo) {
                    return true;
                }
            }
        }
    }

    'next_neg_lit: for negj in n {
        let Some(neg_lit) = &negj.lit else {
            continue;
        };
        let mut found_matching_pos = false;
        for posi in p {
            let Some(pos_lit) = &posi.lit else {
                continue;
            };
            if !closure_brand_inside(pos_lit.fn_id, neg_lit.fn_id) || pos_lit.captures.len() != neg_lit.captures.len() {
                continue;
            }
            found_matching_pos = true;
            // The clause is empty only when the positive capture space is
            // fully covered by the negated capture space: P \ N = empty iff
            // P ⊆ N.
            let pos_subset_of_neg = pos_lit
                .captures
                .iter()
                .zip(&neg_lit.captures)
                .all(|(pc, nc)| cx.descr(pc).diff(cx.descr(nc)).is_empty_memo(cx, memo));
            if pos_subset_of_neg {
                return true;
            }
        }
        if found_matching_pos {
            continue 'next_neg_lit;
        }
    }

    let filtered_negs: Vec<ArrowSig> = n.iter().filter(|negj| negj.lit.is_none()).cloned().collect();
    let n = &filtered_negs;
    if n.is_empty() {
        return false;
    }
    'next_neg: for negj in n {
        let s = arrow_input(negj);
        let v = cx.descr(&negj.ret).clone();
        let output_outside_v = Descr::any().diff(&v);
        if arrow_partition_witness(cx, p, 0, s, output_outside_v, memo) {
            continue 'next_neg;
        }
        return true;
    }
    false
}

pub(crate) fn map_clause_empty(cx: TyCtx<'_>, c: &Conj<MapSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        return false;
    }
    if c.pos.iter().skip(1).any(|p| p.tag != c.pos[0].tag) {
        return true;
    }
    let mut merged: BTreeMap<MapKey, Descr> = c.pos[0]
        .fields
        .iter()
        .map(|(k, v)| (k.clone(), cx.descr(v).clone()))
        .collect();
    for p in &c.pos[1..] {
        for (k, v) in &p.fields {
            merged
                .entry(k.clone())
                .and_modify(|e| *e = e.intersect(cx.descr(v)))
                .or_insert_with(|| cx.descr(v).clone());
        }
    }
    if merged.values().any(|v| v.is_empty_memo(cx, memo)) {
        return true;
    }
    // A positive map is open, so its smallest witnesses have exactly its
    // required keys. A negative that requires another key cannot cover one of
    // those witnesses. The remaining negatives are rectangles over the
    // positive keys; absent negative fields admit every value on that axis.
    let negatives: Vec<Vec<Descr>> = c
        .neg
        .iter()
        .filter(|negative| negative.tag == c.pos[0].tag)
        .filter(|negative| negative.fields.keys().all(|key| merged.contains_key(key)))
        .map(|negative| {
            merged
                .keys()
                .map(|key| match negative.fields.get(key) {
                    Some(value) => cx.descr(value).clone(),
                    None => Descr::any(),
                })
                .collect()
        })
        .collect();
    phi_tuple(cx, &merged.into_values().collect::<Vec<_>>(), &negatives, memo)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::types::{ComponentRef, DescrOf, Types};

    fn exhaustive_arrow_partition_witness(
        cx: TyCtx<'_>,
        positives: &[ArrowSig],
        input: Descr,
        output: Descr,
        memo: &mut Memo,
    ) -> bool {
        assert!(positives.len() <= 8, "the test oracle is deliberately bounded");
        for mask in 0usize..(1usize << positives.len()) {
            let mut selected_inputs = Descr::none();
            let mut unselected_outputs = Descr::any();
            for (index, positive) in positives.iter().enumerate() {
                if (mask >> index) & 1 == 1 {
                    selected_inputs = selected_inputs.union(cx, &arrow_input(positive));
                } else {
                    unselected_outputs = unselected_outputs.intersect(cx.descr(&positive.ret));
                }
            }
            let remaining_input = input.diff(&selected_inputs);
            let remaining_output = unselected_outputs.diff(&output);
            if !remaining_input.is_empty_memo(cx, memo) && !remaining_output.is_empty_memo(cx, memo) {
                return true;
            }
        }
        false
    }

    fn literal_free_clause_empty_oracle(cx: TyCtx<'_>, clause: &Conj<ArrowSig>, memo: &mut Memo) -> bool {
        if clause.neg.is_empty() {
            return false;
        }
        clause.neg.iter().any(|negative| {
            !exhaustive_arrow_partition_witness(
                cx,
                &clause.pos,
                arrow_input(negative),
                cx.descr(&negative.ret).clone(),
                memo,
            )
        })
    }

    #[test]
    fn arrow_partition_calculator_handles_thirty_two_positives() {
        let mut types = Types::new();
        let int = types.int();
        let atom = types.atom();
        let clause = Conj {
            pos: (1..=32)
                .map(|arity| ArrowSig {
                    args: vec![int; arity],
                    ret: int,
                    lit: None,
                })
                .collect(),
            neg: vec![ArrowSig {
                args: vec![int],
                ret: atom,
                lit: None,
            }],
        };

        assert!(
            !func_clause_empty(types.ctx(), &clause, &mut Memo::default()),
            "the unary int→atom negation leaves an int→int witness"
        );
    }

    #[test]
    fn arrow_partition_calculator_prunes_thirty_two_and_sixty_four_proven_constraints() {
        let mut types = Types::new();
        let int = types.int();
        let atom = types.atom();
        let int_or_atom = types.union(int, atom);
        for positive_count in [32, 64] {
            let clause = Conj {
                pos: (1..=positive_count)
                    .map(|arity| ArrowSig {
                        args: vec![int; arity],
                        ret: int,
                        lit: None,
                    })
                    .collect(),
                neg: vec![ArrowSig {
                    args: vec![int],
                    ret: int_or_atom,
                    lit: None,
                }],
            };

            assert!(
                func_clause_empty(types.ctx(), &clause, &mut Memo::default()),
                "the unary positive proves int→int|atom at {positive_count} positives"
            );
        }
    }

    #[test]
    fn one_implied_negative_empties_a_clause_with_other_escaping_negatives() {
        let mut types = Types::new();
        let int = types.int();
        let float = types.float();
        let atom = types.atom();
        let int_or_atom = types.union(int, atom);
        let clause = Conj {
            pos: vec![ArrowSig {
                args: vec![int],
                ret: int,
                lit: None,
            }],
            neg: vec![
                ArrowSig {
                    args: vec![float],
                    ret: atom,
                    lit: None,
                },
                ArrowSig {
                    args: vec![int],
                    ret: int_or_atom,
                    lit: None,
                },
            ],
        };

        assert!(
            func_clause_empty(types.ctx(), &clause, &mut Memo::default()),
            "one covered negative is enough to empty a conjunction even when another negative has a witness"
        );
    }

    #[test]
    fn arrow_partition_calculator_matches_bounded_exhaustive_oracle() {
        let mut types = Types::new();
        let none = types.none();
        let int = types.int();
        let float = types.float();
        let atom = types.atom();
        let int_or_atom = types.union(int, atom);
        let list_int = types.list(int);
        let empty_recursive_tuple = types.intern_regular_component(1, |nodes| {
            vec![DescrOf::tuple_of(vec![nodes[0], ComponentRef::Published(int)])]
        })[0];
        let productive_recursive = types.intern_regular_component(1, |nodes| {
            let mut body = DescrOf::atom_lit("leaf");
            body.cases[0]
                .structure
                .tuples
                .push(Conj::pos_of(super::super::TupleSigOf {
                    elems: vec![ComponentRef::Published(int), nodes[0]],
                }));
            vec![body]
        })[0];
        let shapes = [
            none,
            int,
            float,
            atom,
            int_or_atom,
            list_int,
            empty_recursive_tuple,
            productive_recursive,
        ];
        let mut state = 0x6d5a_56a9_u64;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            (state >> 32) as usize
        };

        for case_index in 0..256 {
            let positives = (0..next() % 9)
                .map(|_| {
                    let arity = next() % 4;
                    ArrowSig {
                        args: (0..arity).map(|_| shapes[next() % shapes.len()]).collect(),
                        ret: shapes[next() % shapes.len()],
                        lit: None,
                    }
                })
                .collect();
            let negatives = (0..next() % 4)
                .map(|_| {
                    let arity = next() % 4;
                    ArrowSig {
                        args: (0..arity).map(|_| shapes[next() % shapes.len()]).collect(),
                        ret: shapes[next() % shapes.len()],
                        lit: None,
                    }
                })
                .collect();
            let clause = Conj {
                pos: positives,
                neg: negatives,
            };
            let actual = func_clause_empty(types.ctx(), &clause, &mut Memo::default());
            let expected = literal_free_clause_empty_oracle(types.ctx(), &clause, &mut Memo::default());
            assert_eq!(
                actual, expected,
                "seed=0x6d5a56a9 case={case_index}: pruned traversal must match exhaustive partitions"
            );
        }
    }
}
