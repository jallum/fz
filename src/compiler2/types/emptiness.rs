//! Per-axis emptiness algorithms for the interned descriptor kernel.

use crate::fz_ir::FnId;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use super::conj::Conj;
use super::descr::{Descr, is_empty_memo_ty};
use super::sigs::{ArrowSig, ClosureLit, ListSig, ListSigOf, MapSig, ResourceSig, TupleSig};
use super::{MapKey, Ty, TyCtx};

/// One emptiness/tuple-carving operand: the `Ty` a coordinate already
/// arrived as, or a descriptor an algebra step (`intersect`/`diff`/`union`)
/// just built. A built descriptor names no `Ty`: interning it would mint an
/// id as the side effect of a pure predicate, and the tuple carving that
/// runs during `Types::intern`'s own construction of a new type would have
/// to call back into an interner that has not finished building the type
/// it's partway through. So a built descriptor stays uninterned, behind a
/// shared pointer — cloning an `Operand` bumps a refcount or copies a `Ty`
/// id, never re-walks a descriptor's cases.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum Operand {
    Ty(Ty),
    Built(Rc<Descr>),
}

impl Operand {
    pub(super) fn built(d: Descr) -> Self {
        Self::Built(Rc::new(d))
    }

    /// Resolve to the descriptor this operand names, without cloning it.
    pub(super) fn as_descr<'a>(&'a self, cx: TyCtx<'a>) -> &'a Descr {
        match self {
            Self::Ty(ty) => cx.descr(ty),
            Self::Built(d) => d,
        }
    }

    /// Structural equality across variants, for callers that only ever
    /// compare — never cache — an operand (tuple-rectangle fusion). Two
    /// operands naming the same `Ty` are equal without touching the arena;
    /// anything else falls back to comparing the descriptors themselves, by
    /// reference, never by clone.
    pub(super) fn same_as(&self, other: &Self, cx: TyCtx<'_>) -> bool {
        match (self, other) {
            (Self::Ty(a), Self::Ty(b)) => a == b,
            _ => self.as_descr(cx) == other.as_descr(cx),
        }
    }

    fn intersect(&self, cx: TyCtx<'_>, other: &Self) -> Self {
        Self::built(self.as_descr(cx).intersect(other.as_descr(cx)))
    }

    fn diff(&self, cx: TyCtx<'_>, other: &Self) -> Self {
        Self::built(self.as_descr(cx).diff(other.as_descr(cx)))
    }

    fn is_empty_memo(&self, cx: TyCtx<'_>, memo: &mut Memo) -> bool {
        match self {
            Self::Ty(ty) => is_empty_memo_ty(*ty, cx, memo),
            Self::Built(d) => d.is_empty_memo(cx, memo),
        }
    }
}

/// One emptiness subproblem, identified by the operands it is asked about.
/// `Operand` compares and hashes by `Ty` identity where it has one, and
/// falls back to descriptor structure only for the algebra results that
/// were never interned — the narrowest key that still recognises a
/// coinductive back-edge for every cycle that passes back through an
/// unmodified `Ty` reference, which every genuinely recursive descriptor
/// does (a recursive occurrence is a component reference, not a rebuilt
/// fragment).
#[derive(Clone, PartialEq, Eq, Hash)]
enum MemoKey {
    /// `Descr::is_empty_memo`'s own question.
    Descr(Operand),
    /// `phi_tuple`'s question: is `∏t \ ⋃n` empty? `phi_tuple`'s branching is
    /// exponential in the negation count on its own, independent of how fast
    /// any single coordinate's emptiness resolves, so its `(t, n)` pairs need
    /// their own cache entries, not just the coordinates'.
    Tuple(Vec<Operand>, Vec<Vec<Operand>>),
}

/// One frame of the coinductive DFS, tracked the way Tarjan's SCC algorithm
/// tracks a DFS frame: `low_link` starts at this frame's own discovery
/// `index` and is pulled down by every back-edge reachable from it.
struct Frame {
    key: MemoKey,
    index: usize,
    low_link: usize,
}

/// Coinductive assumption set and result cache for one top-level emptiness
/// query. Emptiness over recursive descriptors is a greatest fixpoint: a
/// subproblem that re-enters a key already in flight assumes it empty, and
/// the whole surrounding strongly-connected component of subproblems either
/// closes cleanly (every member's assumption holds, so every member is
/// permanently cacheable) or is refuted by a witness found anywhere inside it
/// (a witness is *always* cacheable, cyclic or not — it needed no assumption
/// to be found). This is Tarjan's SCC algorithm applied on the fly to the
/// implicit call graph of `query`: `frames` mirrors the live Rust recursion,
/// `open` is Tarjan's "on stack" set — it outlives a frame's own return,
/// since a callee can pop back to its caller while its component is still
/// being explored through a sibling path — and `results` is the permanent,
/// cross-branch cache.
#[derive(Default)]
pub(crate) struct Memo {
    results: HashMap<MemoKey, bool>,
    frames: Vec<Frame>,
    open: Vec<MemoKey>,
    index: HashMap<MemoKey, usize>,
    next_index: usize,
    #[cfg(test)]
    pub(crate) hits: usize,
    #[cfg(test)]
    pub(crate) misses: usize,
}

impl Memo {
    /// Entry point for [`Descr::is_empty_memo`], for a descriptor an algebra
    /// step already built. `MemoKey` and `Operand` stay private to this
    /// module; this is one of the two seams `descr.rs` calls through instead
    /// (the other is [`Memo::query_ty`], for a `Descr` that is still a bare
    /// `Ty`).
    pub(super) fn query_descr(&mut self, d: &Descr, compute: impl FnOnce(&mut Self) -> bool) -> bool {
        self.query(MemoKey::Descr(Operand::built(d.clone())), compute)
    }

    /// Entry point for [`is_empty_memo_ty`]: the common case, where the
    /// question is about a `Ty` nothing has touched yet, so the key is the
    /// id itself.
    pub(super) fn query_ty(&mut self, ty: Ty, compute: impl FnOnce(&mut Self) -> bool) -> bool {
        self.query(MemoKey::Descr(Operand::Ty(ty)), compute)
    }

    /// Look up or compute the emptiness answer for `key`, threading the SCC
    /// bookkeeping described on [`Memo`]. `compute` must reach every
    /// sub-question through another `query` call (directly, or through
    /// [`Descr::is_empty_memo`]) so a cycle back to `key` is visible here.
    fn query(&mut self, key: MemoKey, compute: impl FnOnce(&mut Self) -> bool) -> bool {
        if let Some(&cached) = self.results.get(&key) {
            #[cfg(test)]
            {
                self.hits += 1;
            }
            return cached;
        }
        #[cfg(test)]
        {
            self.misses += 1;
        }
        if let Some(&ancestor_index) = self.index.get(&key) {
            // A back-edge to a key still open on the DFS stack: the
            // coinductive default. Pull the caller's low_link down to the
            // ancestor so its component is recognised once the DFS returns
            // to that ancestor.
            if let Some(caller) = self.frames.last_mut() {
                caller.low_link = caller.low_link.min(ancestor_index);
            }
            return true;
        }

        let my_index = self.next_index;
        self.next_index += 1;
        self.index.insert(key.clone(), my_index);
        self.open.push(key.clone());
        self.frames.push(Frame {
            key: key.clone(),
            index: my_index,
            low_link: my_index,
        });

        let result = compute(self);

        let frame = self.frames.pop().expect("pushed immediately above");
        debug_assert!(frame.key == key);
        if let Some(caller) = self.frames.last_mut() {
            caller.low_link = caller.low_link.min(frame.low_link);
        }

        // A witness is a positive, self-contained proof: cache it
        // unconditionally, regardless of which assumptions were consulted to
        // find it (an over-optimistic "assume empty" guess can only ever
        // make a computation look MORE empty, never manufacture a witness).
        if !result {
            self.results.insert(key.clone(), false);
        }

        if frame.low_link == frame.index {
            // `key` roots its own strongly-connected component: every key
            // still open above it was reached only through cycles back into
            // this component, so it closes here too.
            let scc_start = self
                .open
                .iter()
                .position(|open_key| *open_key == key)
                .expect("key stays open until its own root closes");
            let component: Vec<MemoKey> = self.open.split_off(scc_start);
            for member in &component {
                self.index.remove(member);
            }
            let has_witness = component.iter().any(|member| self.results.get(member) == Some(&false));
            if !has_witness {
                // No witness anywhere in the component: the coinductive
                // "assume empty" guesses that tied it together all held, so
                // every member (besides the witnesses already cached above,
                // of which there are none here) is permanently empty.
                for member in &component {
                    self.results.entry(member.clone()).or_insert(true);
                }
            }
            // If the component does contain a witness, its other members'
            // `true` answers were only ever provisional guesses used to
            // reach that witness — they stay uncached and are recomputed
            // fresh the next time something asks, exactly as before this
            // cache existed.
        }

        result
    }
}

pub(crate) fn tuple_clause_empty(cx: TyCtx<'_>, c: &Conj<TupleSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        return false;
    }
    let arity = c.pos[0].elems.len();
    if c.pos.iter().any(|p| p.elems.len() != arity) {
        return true;
    }
    let mut t: Vec<Operand> = c.pos[0].elems.iter().map(|ty| Operand::Ty(*ty)).collect();
    for p in &c.pos[1..] {
        for (i, e) in p.elems.iter().enumerate() {
            t[i] = t[i].intersect(cx, &Operand::Ty(*e));
        }
    }
    let negs: Vec<Vec<Operand>> = c
        .neg
        .iter()
        .filter(|n| n.elems.len() == arity)
        .map(|n| n.elems.iter().map(|ty| Operand::Ty(*ty)).collect())
        .collect();
    phi_tuple(cx, &t, &negs, memo)
}

/// Is the product `∏t` minus the union of the products `∏n` empty?
///
/// Exact, and stated over OPERANDS rather than interned coordinates, so a
/// caller can decide `∏t ⊆ ⋃∏n` for rectangles it built but never interned.
/// Every entry of `n` must have the same arity as `t`; a mismatched arity
/// subtracts nothing and belongs to the caller's filter.
///
/// The branching below is exponential in `n.len()` on its own — one call
/// per coordinate at every negation consumed — regardless of how fast any
/// single coordinate's own emptiness resolves, so the `(t, n)` subproblem
/// itself is cached, not just the coordinates it examines.
pub(super) fn phi_tuple(cx: TyCtx<'_>, t: &[Operand], n: &[Vec<Operand>], memo: &mut Memo) -> bool {
    let key = MemoKey::Tuple(t.to_vec(), n.to_vec());
    memo.query(key, |memo| phi_tuple_uncached(cx, t, n, memo))
}

fn phi_tuple_uncached(cx: TyCtx<'_>, t: &[Operand], n: &[Vec<Operand>], memo: &mut Memo) -> bool {
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
        .any(|(h, ti)| ti.intersect(cx, h).is_empty_memo(cx, memo))
    {
        return phi_tuple(cx, t, rest, memo);
    }
    for i in 0..t.len() {
        let mut t_split = t.to_vec();
        for j in 0..i {
            t_split[j] = t_split[j].intersect(cx, &head[j]);
        }
        t_split[i] = t_split[i].diff(cx, &head[i]);
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
    Inhabited(Operand),
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
            Self::Unconstrained => Operand::Ty(elem),
            Self::Inhabited(prev) => prev.intersect(cx, &Operand::Ty(elem)),
        };
        if next.is_empty_memo(cx, memo) {
            Self::Empty
        } else {
            Self::Inhabited(next)
        }
    }

    /// The fragment's element operand, `None` meaning ONLY "proven empty".
    fn fragment(self) -> Option<Operand> {
        match self {
            Self::Unconstrained => Some(Operand::built(Descr::any())),
            Self::Empty => None,
            Self::Inhabited(d) => Some(d),
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
///
/// `elem` and `minus` are plain descriptors, materialized once here: unlike
/// the recursion above, this is the rendering boundary the canonical display
/// reads from, so what it needs is content, not identity.
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
        let cut = elem.intersect(cx, &Operand::Ty(cut));
        if cut.is_empty_memo(cx, memo) {
            continue;
        }
        if elem.diff(cx, &cut).is_empty_memo(cx, memo) {
            return just_empty();
        }
        let cut = cut.as_descr(cx).clone();
        if !minus.contains(&cut) {
            minus.push(cut);
        }
    }
    Some(ListDenotation {
        holds_empty,
        non_empty: Some(NonEmptyLists {
            elem: elem.as_descr(cx).clone(),
            minus,
        }),
    })
}

pub(crate) fn list_clause_empty(cx: TyCtx<'_>, c: &Conj<ListSig>, memo: &mut Memo) -> bool {
    list_denotation(cx, c, memo).is_none()
}

pub(crate) fn resource_clause_empty(cx: TyCtx<'_>, c: &Conj<ResourceSig>, memo: &mut Memo) -> bool {
    let payload = if c.pos.is_empty() {
        Operand::built(Descr::any())
    } else {
        let mut payload = Operand::Ty(c.pos[0].payload);
        for p in &c.pos[1..] {
            payload = payload.intersect(cx, &Operand::Ty(p.payload));
        }
        if payload.is_empty_memo(cx, memo) {
            return true;
        }
        payload
    };
    let negatives: Vec<Vec<Operand>> = c
        .neg
        .iter()
        .map(|negative| vec![Operand::Ty(negative.payload)])
        .collect();
    phi_tuple(cx, &[payload], &negatives, memo)
}

fn arrow_input(sig: &ArrowSig) -> Operand {
    Operand::built(Descr::tuple_of(sig.args.clone()))
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
    remaining_input: Operand,
    remaining_output: Operand,
    memo: &mut Memo,
) -> bool {
    if remaining_input.is_empty_memo(cx, memo) || remaining_output.is_empty_memo(cx, memo) {
        return false;
    }
    let Some(positive) = positives.get(next) else {
        return true;
    };

    let selected_input = remaining_input.diff(cx, &arrow_input(positive));
    if arrow_partition_witness(cx, positives, next + 1, selected_input, remaining_output.clone(), memo) {
        return true;
    }

    let unselected_output = remaining_output.intersect(cx, &Operand::Ty(positive.ret));
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
        .any(|lit| lit.captures.iter().any(|c| is_empty_memo_ty(*c, cx, memo)))
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
                if Operand::Ty(*a).intersect(cx, &Operand::Ty(*b)).is_empty_memo(cx, memo) {
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
                .all(|(pc, nc)| Operand::Ty(*pc).diff(cx, &Operand::Ty(*nc)).is_empty_memo(cx, memo));
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
        let v = Operand::Ty(negj.ret);
        let output_outside_v = Operand::built(Descr::any()).diff(cx, &v);
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
    let mut merged: BTreeMap<MapKey, Operand> = c.pos[0]
        .fields
        .iter()
        .map(|(k, v)| (k.clone(), Operand::Ty(*v)))
        .collect();
    for p in &c.pos[1..] {
        for (k, v) in &p.fields {
            merged
                .entry(k.clone())
                .and_modify(|e| *e = e.intersect(cx, &Operand::Ty(*v)))
                .or_insert_with(|| Operand::Ty(*v));
        }
    }
    if merged.values().any(|v| v.is_empty_memo(cx, memo)) {
        return true;
    }
    // A positive map is open, so its smallest witnesses have exactly its
    // required keys. A negative that requires another key cannot cover one of
    // those witnesses. The remaining negatives are rectangles over the
    // positive keys; absent negative fields admit every value on that axis.
    let negatives: Vec<Vec<Operand>> = c
        .neg
        .iter()
        .filter(|negative| negative.tag == c.pos[0].tag)
        .filter(|negative| negative.fields.keys().all(|key| merged.contains_key(key)))
        .map(|negative| {
            merged
                .keys()
                .map(|key| match negative.fields.get(key) {
                    Some(value) => Operand::Ty(*value),
                    None => Operand::built(Descr::any()),
                })
                .collect()
        })
        .collect();
    phi_tuple(cx, &merged.into_values().collect::<Vec<_>>(), &negatives, memo)
}

#[cfg(test)]
#[path = "emptiness_test.rs"]
mod emptiness_test;

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
                    selected_inputs = selected_inputs.union(cx, &arrow_input(positive).as_descr(cx).clone());
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
                arrow_input(negative).as_descr(cx).clone(),
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
