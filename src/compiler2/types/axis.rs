//! The rewrites that make one DNF axis a function of the set it denotes.
//!
//! An axis denotes the UNION of its clauses, and three rewrites follow from
//! that alone:
//!
//! - a clause that denotes nothing is the union's identity and is dropped
//!   (`A ∨ ∅ = A`);
//! - a clause the union of the others already covers adds nothing and is
//!   dropped (`A ⊆ B₁ ∨ … ∨ Bₙ ⇒ A ∨ B₁ ∨ … ∨ Bₙ = B₁ ∨ … ∨ Bₙ`), exact
//!   duplicates being the degenerate case;
//! - an axis whose clauses between them cover the axis IS that axis's top, and
//!   collapses to it, written as the ONE clause with no factors at all. The
//!   lattice reaches a top through ordinary clauses —
//!   `empty_list() ∨ non_empty_list(any)` is every list, `{any, any} ∨
//!   ¬{any, any}` is every tuple — and without this the one set takes one
//!   identity per spelling the arena happens to mint.
//!
//! Each rewrites a descriptor to a semantically EQUAL one, so emptiness and
//! subtyping answers are unchanged; only the clause list shrinks. Equal under
//! the relation the CALCULATOR answers with, which is the only relation there
//! is. An axis rule that reasons about a clause as a plain set of values can
//! outrun the kernel's own containment — see the resource rule below for the
//! case where it does — and a rule that outruns it drops clauses the union
//! they are folded into does not contain.
//!
//! The tuple axis has a fourth, because a union of products can be CARVED
//! into products more than one way and neither carving's clauses contain the
//! other's: [`fuse_tuple_rects`] rewrites both carvings to one. It is the only
//! rewrite here that can grow a clause rather than remove one, and the only
//! one that mints a type.
//!
//! # One spelling of the top
//!
//! The top of every axis is the clause with no factors, [`Conj::top`] — the
//! spelling `Descr::any()` already writes on all five axes. Nothing else is a
//! spelling of it: an axis written `[ListSig { empty: true, elem: any }]` and
//! an axis written `[Conj::top()]` denote one set, and two descriptors that
//! denote one set take two ids. So a single plain clause that IS the axis top
//! is rewritten to the contentless clause here, at the same boundary, and
//! `t.list(any)`, `[] ∨ non_empty_list(any)` and `any ∨ [any]` all land on it.
//!
//! What that costs is that a reader projecting a positive sig off a list or
//! resource clause has to read a contentless clause as the widest sig —
//! `[any]`, `resource(any)` — rather than as "no list at all". `as_pure_list`
//! and `pure_resource` do; `list_element_type` and `resource_payload_type`
//! already did; `format` renders the axis top as the widest type a user could
//! write.
//!
//! # Whether an axis is its top
//!
//! One rule, [`axis_is_top`], for all five axes. A clause with no factors
//! constrains nothing, so an axis carrying one is its top outright. Otherwise
//! the axis is asked what its clauses' positive sigs say
//! ([`AxisView::plain_top`]), and only what that cannot settle reaches the
//! exact calculator question.
//!
//! The split falls where it does because a clause carrying a NEGATIVE factor
//! carves a set no sig comparison can read. A finite union of positive-only
//! tuple clauses is never every tuple — a positive `TupleSig` fixes an arity,
//! and arity is unbounded — and a finite union of positive-only map clauses is
//! never every map, for the same reason about struct tags. But `{any, any} ∨
//! ¬{any, any}` IS every tuple, and `%{k: any} ∨ ¬%{k: any}` is every map, so
//! "this axis has no top to reach" would be false. Lists and resources answer
//! their positive-only case exactly, reading the verdict off the kernel's own
//! clause-emptiness rule rather than off set reasoning, and go to the
//! calculator for the rest.
//!
//! What those two rules ask of a child — "is this every value" — is a question
//! about the DENOTATION, and `Descr::is_full` is its one implementation. A
//! structural reading would answer no for an `any` written some other way,
//! which the unabsorbed callable axis makes reachable (`f ∨ ¬f` is every
//! callable in two clauses), and `[x]` and `[any]` would take two ids and two
//! canonical forms for one set of lists.
//!
//! `Types::intern` is the authority: it applies them at the persistence
//! boundary, so an interned descriptor arrives already rewritten and identity
//! is assigned to the rewritten form. [`TyCanon`](super::canon) is the second
//! caller, for the one descriptor it still builds ITSELF — a list clause's
//! intersected element fragment is a `Descr` that never reaches the interner,
//! and rendering one unrewritten would report two carvings of a type as two
//! types. One function each way, so the boundary and the rendering cannot
//! drift apart.
//!
//! Absorption reaches the tuple, list, resource and map axes. The callable
//! axis remains excluded on the two measured facts about literal shapes that
//! still carry planner evidence. The formerly separate lit-free obstruction is
//! gone: `ActivationKey` and resolved source contracts now keep their addressed
//! inputs and result in typed coordinate records, not an `ArrowSig`, so an axis
//! top can no longer erase planner bookkeeping from a callable `Ty`.
//!
//! A LIT-BEARING arrow's `args` and `ret` are evidence `func_clause_empty`
//! does not read, so two specializations of one lambda are mutually subtypes
//! and a rule reading the denotation alone would merge them — stated once, and
//! pinned against the planner that reads them, by `semantic`'s
//! `activation_input_rows_keep_arrows_that_differ_only_where_subtyping_is_blind`.
//! What puts the discarded evidence back is `Types::row_column_dominates`,
//! and it is a conjunction of three: equal free var ids (which is what keeps
//! a template beside its ground instance, a surplus with its own test),
//! containment of `lit_arrow_shapes` in one direction — every literal shape of
//! the dominated column appears in the dominator's — and `is_subtype`. A shape
//! is `(brand, captures, args, ret)`; the kernel reads brand and captures, so
//! `args` and `ret` are the part containment adds.
//!
//! A closure literal's CAPTURE LAYOUT is the third, and here the kernel
//! ENDORSES the containment rather than refusing it: the capture-subset rule
//! in `func_clause_empty` makes `closure[f]([mailbox]) ⊆ closure[f]([any])`,
//! so absorbing the narrower clause into the wider one would be exact — and
//! would still erase an environment, because `Types::callable_clauses` hands
//! transport the captures of every clause it finds, narrower ones included.
//! Absorb the axis and
//! `transport_relation_incremental_test::a_nested_source_union_retains_both_environments_of_the_same_function`
//! fails: one source union stops naming the same lambda with a `[mailbox]`
//! environment beside its `[any]` one.
//!
//! That axis keeps its exact-duplicate dedupe instead. Dropping what denotes
//! nothing is safe there and reaches all five. This is the one statement of
//! that exclusion; every other site points here.

use super::Ty;
use super::TyCtx;
use super::conj::Conj;
use super::descr::Descr;
use super::dnf::is_dnf_top;
use super::emptiness::{self, ListDenotation, NonEmptyLists};
use super::sigs::{ListSig, ResourceSig, TupleSig};

/// Install one axis's clauses into an otherwise contentless descriptor. The
/// axis's containment questions are then asked of the shared type calculator
/// rather than of a per-axis rule.
pub(super) type InstallAxis<T> = fn(&mut Descr, Vec<Conj<T>>);

/// One axis, named once: how to put a clause list into a descriptor and how to
/// read it back out. Every caller here works through a view rather than
/// spelling the field, so an axis is one name rather than a closure per site.
pub(super) struct AxisView<T: 'static> {
    pub(super) install: InstallAxis<T>,
    /// `wider ⊇ narrower` for two clauses OF THIS AXIS, by sufficient
    /// conditions only: `false` means "not proven", never "proven not". It
    /// reads the clauses' own interned children, so it asks the memoized
    /// calculator and costs a cache hit.
    pub(super) clause_covers: fn(&Conj<T>, &Conj<T>, IsSubtype<'_>) -> bool,
    /// What this axis can say about one clause against the surviving siblings
    /// without descriptor arithmetic. `Unproven` is the only answer that costs
    /// the exact union question.
    pub(super) coverage: CoverageRule<T>,
    /// What this axis can say about "do these clauses cover the whole axis"
    /// from their positive sigs alone. Asked only where every clause is one
    /// positive sig and nothing else; anything carrying a negative factor goes
    /// straight to the calculator, so this rule never has to reason about a
    /// carved-out set.
    pub(super) plain_top: PlainTopRule<T>,
}

/// `narrower ⊆ wider` for two interned types. Injected so every answer comes
/// from `Types`' comparison cache, and it is the ONLY question this module
/// asks of the calculator.
pub(super) type IsSubtype<'a> = &'a dyn Fn(&Ty, &Ty) -> bool;

/// One axis's structural reading of "is this clause inside its siblings".
pub(super) type CoverageRule<T> = fn(TyCtx<'_>, &Conj<T>, &[&Conj<T>], IsSubtype<'_>) -> Coverage;

/// One axis's reading of its own saturation, from the positive sigs of clauses
/// that carry nothing else.
pub(super) type PlainTopRule<T> = fn(TyCtx<'_>, &[&T]) -> Coverage;

/// What an axis can prove structurally about a containment — of one clause in
/// its siblings, or of the whole axis in its clauses. The same three answers
/// serve both, because both end at the same exact question.
///
/// Both verdicts are PROOFS; an axis that is merely unable to see a way for the
/// containment to hold answers `Unproven` and lets the calculator decide. The
/// difference matters: a `NotCovered` that was only a failure to see would hand
/// one set two identities.
pub(super) enum Coverage {
    /// Proven contained.
    Covered,
    /// Proven NOT contained, so the exact question would only say so again.
    NotCovered,
    /// Neither, so the exact question has to be asked.
    Unproven,
}

/// The union operand here is a DESCRIPTOR, never an interned type: a question
/// must not mint an id, so the siblings' coordinates are folded with
/// `Descr::union` and only the containment itself goes through the
/// calculator's cache.
///
/// A clause is inside a union of products only if each of its POSITIONS is
/// inside the union of the same position over the siblings — a product is not
/// the product of its projections, but it is contained in one, so this
/// direction is sound as a filter.
///
/// Every same-arity sibling contributes, overlapping or not. Restricting the
/// fold to siblings that actually overlap makes the filter sharper, but
/// deciding overlap costs a disjointness question per sibling and coordinate,
/// and that measured well above what the sharper filter saves. A superset
/// union still proves NOT covered, which is the only verdict this filter is
/// for.
fn positionwise_gate(cx: TyCtx<'_>, clause: &[Ty], siblings: &[&[Ty]]) -> Coverage {
    let same_arity: Vec<&&[Ty]> = siblings
        .iter()
        .filter(|sibling| sibling.len() == clause.len())
        .collect();
    for (position, ours) in clause.iter().enumerate() {
        let reachable = same_arity.iter().fold(Descr::none(), |acc, sibling| {
            acc.union(cx, cx.descr(&sibling[position]))
        });
        if !cx.descr(ours).is_subtype(cx, &reachable) {
            return Coverage::NotCovered;
        }
    }
    // With ONE sibling, "inside the union of the siblings" is "inside that
    // sibling", which the exact positionwise containment already asked and
    // answered no — every caller reaches here only after it failed.
    if siblings.len() == 1 {
        return Coverage::NotCovered;
    }
    Coverage::Unproven
}

/// Every clause of `wider` is a factor of `narrower`, so `narrower` is a
/// conjunction of at least as many constraints. Axis-independent, and what
/// makes an exact duplicate cover its twin.
fn factors_are_superset<T: PartialEq>(wider: &Conj<T>, narrower: &Conj<T>) -> bool {
    wider.pos.iter().all(|p| narrower.pos.contains(p)) && wider.neg.iter().all(|n| narrower.neg.contains(n))
}

/// The one positive sig of a clause that carries nothing else. Every
/// structural rule here reads this shape and nothing more: a clause with a
/// negative factor describes a carved-out set that no sig comparison can see.
fn plain_sig<T>(clause: &Conj<T>) -> Option<&T> {
    match (clause.pos.as_slice(), clause.neg.as_slice()) {
        ([sig], []) => Some(sig),
        _ => None,
    }
}

/// Every clause's one positive sig, or `None` as soon as a clause carries
/// anything else.
fn plain_sigs<'a, T>(clauses: impl IntoIterator<Item = &'a Conj<T>>) -> Option<Vec<&'a T>> {
    clauses.into_iter().map(plain_sig).collect()
}

pub(super) const TUPLES: AxisView<TupleSig> = AxisView {
    install: |d, clauses| d.tuples = clauses,
    // Products of non-empty sets compare coordinatewise: `∏Aᵢ ⊆ ∏Bᵢ` exactly
    // when every `Aᵢ ⊆ Bᵢ`, which is exact given an interned clause never
    // carries an empty coordinate.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (plain_sig(narrower), plain_sig(wider)) {
                (Some(a), Some(b)) => {
                    a.elems.len() == b.elems.len() && a.elems.iter().zip(b.elems.iter()).all(|(x, y)| sub(x, y))
                }
                _ => false,
            }
    },
    coverage: |cx, clause, siblings, _subtype| {
        let Some(ours) = plain_sig(clause) else {
            return Coverage::Unproven;
        };
        // A clause carrying a negative contributes a shape this filter cannot
        // read, so the exact question decides.
        let Some(theirs) = plain_sigs(siblings.iter().copied()) else {
            return Coverage::Unproven;
        };
        let rects: Vec<&[Ty]> = theirs.iter().map(|sig| sig.elems.as_slice()).collect();
        positionwise_gate(cx, &ours.elems, &rects)
    },
    // A positive `TupleSig` fixes an arity, so a union of positive-only
    // clauses reaches finitely many arities, and arity is unbounded.
    plain_top: |_, _| Coverage::NotCovered,
};
pub(super) const LISTS: AxisView<ListSig> = AxisView {
    install: |d, clauses| d.lists = clauses,
    // A plain list clause has two exact dimensions: whether it admits `[]`,
    // and what its non-empty fragment's element type is.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (plain_sig(narrower), plain_sig(wider)) {
                (Some(a), Some(b)) => {
                    (!a.empty || b.empty)
                        && match (a.elem, b.elem) {
                            (None, _) => true,
                            (Some(_), None) => false,
                            (Some(a), Some(b)) => sub(&a, &b),
                        }
                }
                _ => false,
            }
    },
    // EXACT, and no descriptor arithmetic: a list clause has two independent
    // shapes, and a union covers it only by covering each shape with ONE
    // sibling. There is no union-of-elements case — a list whose elements come
    // from `A ∪ B` is in neither `[A]` nor `[B]` — so the non-empty shape
    // needs a single sibling whose element already contains ours. The two
    // shapes may be covered by DIFFERENT siblings, which is what pairwise
    // containment cannot see: `[] ∨ non_empty_list(int)` covers `list(int)`.
    coverage: |_, clause, siblings, subtype| {
        let Some(ours) = plain_sig(clause) else {
            return Coverage::Unproven;
        };
        let Some(plain) = plain_sigs(siblings.iter().copied()) else {
            return Coverage::Unproven;
        };
        let empty_covered = !ours.empty || plain.iter().any(|theirs| theirs.empty);
        let non_empty_covered = match ours.elem {
            None => true,
            Some(ours) => plain.iter().any(|theirs| match theirs.elem {
                None => false,
                Some(theirs) => (subtype)(&ours, &theirs),
            }),
        };
        if empty_covered && non_empty_covered {
            Coverage::Covered
        } else {
            Coverage::NotCovered
        }
    },
    // EXACT, and read off the kernel's own rule rather than from set
    // reasoning. `top \ (C₁ ∨ … ∨ Cₙ)` over plain clauses is the single clause
    // `¬C₁ ∧ … ∧ ¬Cₙ`, and `emptiness::list_clause_empty` calls that empty
    // exactly when ONE negated sig admits `[]` and ONE negated sig's element
    // swallows the whole fragment. So the axis is its top exactly when one
    // clause admits `[]` and one clause's element is every value — and when
    // neither holds, the exact question would only say so again.
    //
    // "Every value" is a question about the DENOTATION, so it goes to
    // `Descr::is_full`. A spelling test would answer no for an `any` written
    // some other way and leave `[x]` and `[any]` two ids for one set.
    plain_top: |cx, sigs| {
        let admits_empty = sigs.iter().any(|sig| sig.empty);
        let admits_every_element = sigs.iter().any(|sig| sig.elem.is_some_and(|elem| is_full(cx, elem)));
        if admits_empty && admits_every_element {
            Coverage::Covered
        } else {
            Coverage::NotCovered
        }
    },
};

/// One list clause written from what it DENOTES.
///
/// A clause that keeps non-empty lists becomes ONE positive sig carrying the
/// fragment's element type and the `[]` flag, plus one negative sig per
/// surviving subtraction, each a bare non-empty fragment. The negatives' own
/// `[]` flags were read into the positive's, so repeating them would be a
/// second spelling of one fact; a clause that keeps no non-empty list is `[]`
/// itself.
///
/// `intern` is injected because the fragment and the subtractions are
/// descriptors that this rewrite computes: giving them identity is the
/// interner's job, and only the boundary is holding it.
pub(super) fn list_clause_of(denotation: ListDenotation, intern: &mut dyn FnMut(Descr) -> Ty) -> Conj<ListSig> {
    let ListDenotation { holds_empty, non_empty } = denotation;
    let Some(NonEmptyLists { elem, minus }) = non_empty else {
        return Conj::pos_of(ListSig::empty());
    };
    Conj {
        pos: vec![ListSig {
            empty: holds_empty,
            elem: Some(intern(elem)),
        }],
        neg: minus
            .into_iter()
            .map(|cut| ListSig {
                empty: false,
                elem: Some(intern(cut)),
            })
            .collect(),
    }
}

/// `[] ∨ non_empty(T) = list(T)`, decided from the clause SET.
///
/// The axis is a union, so which clause a member joined first may not decide
/// what the union is. `[]` is held by the axis as soon as ONE clause holds it,
/// and every clause that keeps only non-empty lists may then hold it too --
/// widening adds exactly the one list that was already there. Writing `[]`
/// into every such clause rather than leaving it in a clause of its own is
/// what makes the form reachable from either end of a fold: a fold that
/// merged `[]` away early still carries it in the clause it merged into, and
/// the next member widens against that.
///
/// A clause in the list normal form carries no negative that could hold `[]`,
/// so reading the flags is exact. A clause the boundary left alone (its
/// elements carry type variables) may, and one is neither widened nor read as
/// holding `[]`.
pub(super) fn merge_empty_list_clause(clauses: &mut Vec<Conj<ListSig>>) {
    fn just_empty(c: &Conj<ListSig>) -> bool {
        plain_sig(c).is_some_and(ListSig::is_exact_empty)
    }
    // Not `plain_sig`: a clause carrying a residual subtraction still keeps
    // only non-empty lists, and widening its positive is the same one step.
    fn keeps_only_non_empty(c: &Conj<ListSig>) -> bool {
        matches!(c.pos.as_slice(), [sig] if !sig.empty && sig.elem.is_some()) && !c.neg.iter().any(|n| n.empty)
    }
    if !clauses.iter().any(emptiness::clause_holds_empty) {
        return;
    }
    for c in clauses.iter_mut().filter(|c| keeps_only_non_empty(c)) {
        c.pos[0].allow_empty();
    }
    // The bare `[]` clause is what the widened clauses now carry, so it is
    // left only when no other clause holds `[]` to carry it.
    if clauses
        .iter()
        .any(|c| !just_empty(c) && emptiness::clause_holds_empty(c))
    {
        clauses.retain(|c| !just_empty(c));
    }
}

pub(super) const RESOURCES: AxisView<ResourceSig> = AxisView {
    install: |d, clauses| d.resources = clauses,
    // A resource wraps one payload, and the kernel meets two resources by
    // meeting their payloads, so containment is the payload's.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (plain_sig(narrower), plain_sig(wider)) {
                (Some(a), Some(b)) => sub(&a.payload, &b.payload),
                _ => false,
            }
    },
    // EXACT, and no descriptor arithmetic — but exact under the KERNEL's
    // relation, which is narrower than reading a resource as a set of
    // payloads. `emptiness::resource_clause_empty` decides a resource clause
    // carrying negatives by asking whether a SINGLE negative swallows the
    // payload, never whether their union does, so under the calculator's own
    // containment `resource(C)` is inside a union of plain resource clauses
    // exactly when ONE of them contains it — the same reasoning the list rule
    // uses for its non-empty shape. `clause_covers` has already asked that and
    // answered no, so there is nothing left for the union to add.
    coverage: |_, clause, siblings, _| {
        if plain_sig(clause).is_none() || plain_sigs(siblings.iter().copied()).is_none() {
            return Coverage::Unproven;
        }
        Coverage::NotCovered
    },
    // EXACT, by the same reading of the kernel as the list rule. `top` minus a
    // union of plain resource clauses is the one clause negating them all, and
    // `emptiness::resource_clause_empty` calls that empty exactly when a
    // SINGLE negated payload swallows `any` — so the axis is its top exactly
    // when ONE clause's payload is every value, and two clauses partitioning
    // the payloads between them are not every resource.
    //
    // "Every value" is `Descr::is_full`, for the reason the list rule states.
    plain_top: |cx, sigs| {
        if sigs.iter().any(|sig| is_full(cx, sig.payload)) {
            Coverage::Covered
        } else {
            Coverage::NotCovered
        }
    },
};
pub(super) const MAPS: AxisView<super::sigs::MapSig> = AxisView {
    install: |d, clauses| d.maps = clauses,
    // A map clause constrains exactly the fields it names, so the clause that
    // names MORE is the narrower one, and on the fields they share the
    // narrower one's types are inside the wider one's.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (plain_sig(narrower), plain_sig(wider)) {
                (Some(a), Some(b)) => {
                    a.tag == b.tag
                        && b.fields
                            .iter()
                            .all(|(key, wide)| a.fields.get(key).is_some_and(|narrow| sub(narrow, wide)))
                }
                _ => false,
            }
    },
    // Fieldwise, like a product, over the fields the clause names. A map
    // clause is OPEN: it restricts exactly the fields it names and admits any
    // value at the others, so a sibling that does not name one of our fields
    // places no restriction there and reaches every value of it. Siblings
    // under a different tag cannot contribute at all.
    coverage: |cx, clause, siblings, _subtype| {
        let Some(ours) = plain_sig(clause) else {
            return Coverage::Unproven;
        };
        let Some(theirs) = plain_sigs(siblings.iter().copied()) else {
            return Coverage::Unproven;
        };
        let same_tag: Vec<_> = theirs.into_iter().filter(|sig| sig.tag == ours.tag).collect();
        for (key, ours) in &ours.fields {
            let reachable = same_tag
                .iter()
                .fold(Descr::none(), |acc, theirs| match theirs.fields.get(key) {
                    Some(theirs) => acc.union(cx, cx.descr(theirs)),
                    None => acc.union(cx, &Descr::any()),
                });
            if !cx.descr(ours).is_subtype(cx, &reachable) {
                return Coverage::NotCovered;
            }
        }
        if same_tag.len() == 1 {
            return Coverage::NotCovered;
        }
        Coverage::Unproven
    },
    // A positive `MapSig` fixes a tag, and struct tags are unbounded, so a
    // union of positive-only clauses is never every map: a field-less PLAIN
    // clause is every plain map and says nothing about `%Range{}`.
    plain_top: |_, _| Coverage::NotCovered,
};

/// Whether a clause's child denotes every value, asked of the one
/// implementation of that question ([`Descr::is_full`]). A structural answer
/// alone would report `[x]` and `[any]` as two types wherever `x` is `any`
/// written some other way — which the callable axis, left unabsorbed here,
/// makes reachable.
fn is_full(cx: TyCtx<'_>, ty: Ty) -> bool {
    cx.descr(&ty).is_full(cx)
}

/// The callable axis, absorbed only where a RENDERING asks for it — where
/// nothing reads the arrow back, so none of the three surpluses the module
/// doc names can be lost. Intern leaves this axis alone, so its clause rule
/// is the axis-independent one and every real question goes to the
/// calculator.
pub(super) const FUNCS: AxisView<super::sigs::ArrowSig> = AxisView {
    install: |d, clauses| d.funcs = clauses,
    clause_covers: |wider, narrower, _| factors_are_superset(wider, narrower),
    coverage: |_, _, _, _| Coverage::Unproven,
    // An arrow can BE the whole axis — `(X) -> any` constrains nothing a
    // callable could fail — but no reading of the sigs says so: a clause
    // naming a closure literal is one construction, not every callable, and
    // the two look alike from here. Only the calculator can tell them apart.
    plain_top: |_, _| Coverage::Unproven,
};

/// `A ∨ ∅ = A` on every axis.
///
/// `is_empty_ty` is injected so a caller holding a memo answers coordinate
/// emptiness through it; without one the same algorithm runs uncached. It is
/// consulted only on the plain single-positive tuple product — overwhelmingly
/// the common shape, and the one where a coordinate decides the clause on its
/// own.
pub(super) fn drop_empty_clauses(cx: TyCtx<'_>, d: &mut Descr, is_empty_ty: &dyn Fn(&Ty) -> bool) {
    d.tuples.retain(|clause| !tuple_clause_empty(cx, clause, is_empty_ty));
    retain_inhabited(cx, &mut d.lists, emptiness::list_clause_empty);
    retain_inhabited(cx, &mut d.resources, emptiness::resource_clause_empty);
    retain_inhabited(cx, &mut d.funcs, emptiness::func_clause_empty);
    retain_inhabited(cx, &mut d.maps, emptiness::map_clause_empty);
}

fn tuple_clause_empty(cx: TyCtx<'_>, c: &Conj<TupleSig>, is_empty_ty: &dyn Fn(&Ty) -> bool) -> bool {
    match plain_sig(c) {
        Some(product) => product.elems.iter().any(is_empty_ty),
        None => emptiness::tuple_clause_empty(cx, c, &mut emptiness::Memo::default()),
    }
}

fn retain_inhabited<T>(
    cx: TyCtx<'_>,
    clauses: &mut Vec<Conj<T>>,
    clause_empty: fn(TyCtx<'_>, &Conj<T>, &mut emptiness::Memo) -> bool,
) {
    clauses.retain(|clause| !clause_empty(cx, clause, &mut emptiness::Memo::default()));
}

/// Collapse the axis to its top when its clauses cover it, and otherwise drop
/// what the survivors already cover.
///
/// The top is asked about FIRST, because an axis that IS its top has no walk
/// worth running — every clause in it is covered by the one clause that
/// replaces them all — and because the axis's widest sig and the contentless
/// clause cover each other, so leaving that pair to the walk would let
/// position choose between two spellings of one set.
pub(super) fn absorb_axis<T: Clone + 'static>(
    cx: TyCtx<'_>,
    clauses: &mut Vec<Conj<T>>,
    subtype: IsSubtype<'_>,
    covers: Covers<'_>,
    view: &AxisView<T>,
) {
    if clauses.is_empty() || is_dnf_top(clauses) {
        return;
    }
    if axis_is_top(cx, clauses, covers, view) {
        *clauses = vec![Conj::top()];
        return;
    }
    let before = clauses.len();
    drop_covered_clauses(cx, clauses, subtype, covers, view);
    // Dropping does not change what the axis denotes, but it can remove the
    // clause whose shape a structural top rule could not read, so a drop is
    // the only reason to ask again.
    if clauses.len() < before && axis_is_top(cx, clauses, covers, view) {
        *clauses = vec![Conj::top()];
    }
}

/// Whether these clauses between them denote the whole axis.
///
/// A clause with no factors constrains nothing, so an axis carrying one is its
/// top however many clauses sit beside it — that answer belongs to no axis and
/// is settled here. Otherwise the axis reads its clauses' positive sigs, and
/// only what it cannot settle reaches the exact question. A clause carrying a
/// negative factor is never readable that way, so it goes straight there.
pub(super) fn axis_is_top<T: Clone + 'static>(
    cx: TyCtx<'_>,
    clauses: &[Conj<T>],
    covers: Covers<'_>,
    view: &AxisView<T>,
) -> bool {
    if clauses.iter().any(Conj::is_top) {
        return true;
    }
    let structural = match plain_sigs(clauses) {
        Some(sigs) => (view.plain_top)(cx, &sigs),
        None => Coverage::Unproven,
    };
    match structural {
        Coverage::Covered => true,
        Coverage::NotCovered => false,
        Coverage::Unproven => axis_covers_its_top(covers, clauses, view.install),
    }
}

/// `wider ⊇ narrower` for two one-axis descriptors. Injected so the caller
/// answers through its memo; the relation itself is `Descr::is_subtype`.
pub(super) type Covers<'a> = &'a dyn Fn(&Descr, &Descr) -> bool;

/// Survivorship is threaded through the walk rather than decided pairwise
/// afterwards, which is what leaves exact duplicates with one survivor: the
/// first copy is covered by the second and goes, and the second is then
/// covered by nothing.
///
/// Clauses are visited in index order. At `Types::intern` that is the
/// canonical clause order the sort just imposed, so which of a MUTUALLY
/// covering pair lives is a function of the descriptor and not of the
/// schedule that built it. That order is canonical within one arena; on the
/// callable axis, which only the renderer absorbs, two arenas agree only as
/// far as their `FnId` mint orders do.
///
/// [`TyCanon`](super::canon) also runs this on descriptors it synthesized
/// itself, whose clause lists carry the order its folds produced; there a
/// mutually covering pair — two carvings of one set, each outside the other's
/// containment rule — is decided by position. The one such pair that is
/// reachable by construction, the axis's widest sig beside the contentless
/// clause, never reaches here: [`absorb_axis`] asks about the top first and
/// replaces the whole axis with its one spelling.
fn drop_covered_clauses<T: Clone + 'static>(
    cx: TyCtx<'_>,
    clauses: &mut Vec<Conj<T>>,
    subtype: IsSubtype<'_>,
    covers: Covers<'_>,
    view: &AxisView<T>,
) {
    if clauses.len() < 2 {
        return;
    }
    let mut keep = vec![true; clauses.len()];
    for index in 0..clauses.len() {
        keep[index] = !clause_is_covered(cx, subtype, covers, clauses, &keep, index, view);
    }
    let mut verdicts = keep.into_iter();
    clauses.retain(|_| verdicts.next().unwrap_or(true));
}

/// Whether the clause at `index` denotes nothing the surviving others do not,
/// asked in the order that keeps the work proportional to what can change.
///
/// A SINGLE sibling containing it settles the question on its own, and that
/// containment reads the clauses' own interned children, so it is a cache hit.
/// It is only a sufficient condition, so when no sibling contains the clause
/// the axis is asked what its structure says: a clause outside the union of
/// the siblings' same positions is outside the union, and a list or resource
/// axis decides outright. Only what neither settles reaches the exact union
/// question — descriptor arithmetic, and the only place this rule pays for it.
pub(super) fn clause_is_covered<T: Clone + 'static>(
    cx: TyCtx<'_>,
    subtype: IsSubtype<'_>,
    covers: Covers<'_>,
    clauses: &[Conj<T>],
    keep: &[bool],
    index: usize,
    view: &AxisView<T>,
) -> bool {
    let borrowed: Vec<&Conj<T>> = clauses
        .iter()
        .enumerate()
        .filter(|(other, _)| *other != index && keep[*other])
        .map(|(_, clause)| clause)
        .collect();
    if borrowed.is_empty() {
        return false;
    }
    if borrowed
        .iter()
        .any(|sibling| (view.clause_covers)(sibling, &clauses[index], subtype))
    {
        return true;
    }
    match (view.coverage)(cx, &clauses[index], &borrowed, subtype) {
        Coverage::Covered => true,
        Coverage::NotCovered => false,
        Coverage::Unproven => covers(
            &axis_of(borrowed.into_iter().cloned().collect(), view.install),
            &axis_of(vec![clauses[index].clone()], view.install),
        ),
    }
}

/// Whether the clauses between them denote the whole axis, asked of the
/// calculator: the exact question, for what no axis could read structurally.
fn axis_covers_its_top<T: Clone>(covers: Covers<'_>, clauses: &[Conj<T>], install: InstallAxis<T>) -> bool {
    covers(
        &axis_of(clauses.to_vec(), install),
        &axis_of(vec![Conj::top()], install),
    )
}

fn axis_of<T>(clauses: Vec<Conj<T>>, install: InstallAxis<T>) -> Descr {
    let mut d = Descr::unbranded();
    install(&mut d, clauses);
    d
}

// ----------------------------------------------------------------------
// Tuple carving
// ----------------------------------------------------------------------

/// One tuple coordinate. Carving builds coordinates that no type names yet, so
/// a coordinate is either the id it arrived as or a descriptor still to be
/// interned — and a coordinate carving never touched costs no interning at
/// all.
pub(super) enum Coord {
    Interned(Ty),
    Built(Box<Descr>),
}

impl Coord {
    fn descr(&self, cx: TyCtx<'_>) -> Descr {
        match self {
            Self::Interned(ty) => cx.descr(ty).clone(),
            Self::Built(d) => (**d).clone(),
        }
    }

    fn same_as(&self, other: &Self, cx: TyCtx<'_>) -> bool {
        match (self, other) {
            (Self::Interned(a), Self::Interned(b)) => a == b,
            _ => self.descr(cx) == other.descr(cx),
        }
    }
}

/// A plain single-positive tuple clause, read as the product of its
/// coordinates.
pub(super) type Rect = Vec<Coord>;

/// One union of rectangles, carved the same way whichever decomposition
/// arrived.
///
/// A tuple axis stores a union of products, and one set of tuples can be cut
/// into products more than one way. Neither carving's clauses contain the
/// other's, so no clause-by-clause rule reaches it; these two rewrites do, and
/// both preserve the denoted set exactly:
///
/// - FUSION, exact: two rectangles that agree on every coordinate but one are
///   the single rectangle over the union of that coordinate,
///   `{A,C} ∨ {B,C} = {A∨B, C}`. It is what turns a tagged union's width
///   growth into depth growth.
/// - WIDENING: replace coordinate `k` of one rectangle with the union of
///   coordinate `k` over its same-arity siblings, and keep the step only while
///   the grown rectangle is still inside the axis union. A rectangle only
///   grows, and never past the union, so the union is invariant and the result
///   does not depend on the order the steps are taken in.
///
/// Fusion runs to fixpoint first because it strictly reduces the rectangle
/// count; widening then runs against a settled sibling set. The pair repeats
/// only while something changed, so the walk is bounded by the rectangle count
/// it started with.
pub(super) fn fuse_tuple_rects(cx: TyCtx<'_>, mut rects: Vec<Rect>) -> Vec<Rect> {
    if rects.len() < 2 {
        return rects;
    }
    loop {
        let fused = fuse_one_coordinate_unions(cx, &mut rects);
        let widened = widen_to_axis_union(cx, &mut rects);
        if !fused && !widened {
            return rects;
        }
    }
}

/// `{A,C} ∨ {B,C} = {A∨B, C}`, to fixpoint. Reports whether anything merged.
fn fuse_one_coordinate_unions(cx: TyCtx<'_>, rects: &mut Vec<Rect>) -> bool {
    let mut fused = false;
    while let Some((left, right, coord)) = next_fusible_pair(cx, rects) {
        let grown = rects[left][coord].descr(cx).union(cx, &rects[right][coord].descr(cx));
        rects[left][coord] = Coord::Built(Box::new(grown));
        rects.remove(right);
        fused = true;
    }
    fused
}

/// The first pair agreeing on every coordinate but one, with that coordinate.
/// A pair agreeing on ALL coordinates is a duplicate, which the axis absorber
/// owns, so it is not reported here.
fn next_fusible_pair(cx: TyCtx<'_>, rects: &[Rect]) -> Option<(usize, usize, usize)> {
    for left in 0..rects.len() {
        for right in (left + 1)..rects.len() {
            if rects[left].len() != rects[right].len() {
                continue;
            }
            let mut differing = (0..rects[left].len()).filter(|k| !rects[left][*k].same_as(&rects[right][*k], cx));
            let Some(coord) = differing.next() else {
                continue;
            };
            if differing.next().is_none() {
                return Some((left, right, coord));
            }
        }
    }
    None
}

/// Grow coordinates to the axis union while the rectangle stays inside it.
/// Reports whether anything grew.
fn widen_to_axis_union(cx: TyCtx<'_>, rects: &mut [Rect]) -> bool {
    let mut widened = false;
    while let Some((index, coord, grown)) = next_widening(cx, rects) {
        rects[index][coord] = Coord::Built(Box::new(grown));
        widened = true;
    }
    widened
}

fn next_widening(cx: TyCtx<'_>, rects: &[Rect]) -> Option<(usize, usize, Descr)> {
    let mats: Vec<Vec<Descr>> = rects
        .iter()
        .map(|rect| rect.iter().map(|coord| coord.descr(cx)).collect())
        .collect();
    for (index, rect) in mats.iter().enumerate() {
        let arity = rect.len();
        let siblings: Vec<&Vec<Descr>> = mats.iter().filter(|other| other.len() == arity).collect();
        for coord in 0..arity {
            let candidate = siblings
                .iter()
                .fold(Descr::none(), |acc, sibling| acc.union(cx, &sibling[coord]));
            if candidate == rect[coord] {
                continue;
            }
            let mut trial = rect.clone();
            trial[coord] = candidate.clone();
            let cover: Vec<Vec<Descr>> = siblings.iter().map(|sibling| (*sibling).clone()).collect();
            if emptiness::phi_tuple(cx, &trial, &cover, &mut emptiness::Memo::default()) {
                return Some((index, coord, candidate));
            }
        }
    }
    None
}

#[cfg(test)]
#[path = "axis_test.rs"]
mod axis_test;
