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
//!   collapses to it. The lattice reaches a top through ordinary clauses —
//!   `empty_list() ∨ non_empty_list(any)` is every list — and without this the
//!   one set takes one identity per spelling the arena happens to mint. Only
//!   the LIST and RESOURCE axes have a top to reach: tuple arity and struct
//!   tags are both unbounded, so no finite union of tuple or map clauses is
//!   every tuple or every map. The top is written as the axis's widest single
//!   sig (`[any]`, `resource(any)`), never as an empty conjunction, which
//!   would leave every reader that projects a positive sig answering "not a
//!   list" for the widest list.
//!
//! Each rewrites a descriptor to a semantically EQUAL one, so emptiness and
//! subtyping answers are unchanged; only the clause list shrinks.
//!
//! `Types::intern` is the authority: it applies them at the persistence
//! boundary, so an interned descriptor arrives already rewritten and identity
//! is assigned to the rewritten form. [`TyCanon`](super::canon) is the second
//! caller, for the descriptors it builds ITSELF — tuple-coordinate widening
//! and a list clause's intersected element fragment are `Descr` values that
//! never reach the interner, and rendering one unrewritten would report two
//! carvings of a type as two types. One function each way, so the boundary and
//! the rendering cannot drift apart.
//!
//! Absorption reaches the tuple, list, resource and map axes. The callable
//! axis carries more than its denotation — an arrow holds a declared signature
//! that `@spec` resolution reads its parameters and result back out of, and a
//! closure literal holds a capture layout — so absorbing
//! `closure[f]([mailbox])` into `closure[f]([any])` would lose an environment,
//! and collapsing `(X) -> any` to the axis top would lose a declaration.
//! Dropping what denotes nothing is safe there and reaches all five.

use super::Ty;
use super::TyCtx;
use super::conj::Conj;
use super::descr::Descr;
use super::dnf::is_dnf_top;
use super::emptiness;
use super::sigs::TupleSig;

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
    /// Whether ONE clause is already the whole axis. Exact, so an axis holding
    /// a single clause needs no descriptor arithmetic to decide saturation.
    pub(super) clause_is_top: fn(TyCtx<'_>, &Conj<T>) -> bool,
    /// This axis's top written as ONE sig, built from a sig the clauses
    /// already carry. Only the axes that can saturate have one; the rest
    /// answer `None` and never reach this.
    ///
    /// Saturation writes THIS, never `Conj::top()`. An empty conjunction has
    /// no positive sig, so every reader that projects one — `as_pure_list`,
    /// `pure_resource`, the runtime type predicate, instantiation's
    /// substitution walk — would answer "not a list" for the widest list and
    /// silently lose its head question. Writing the maximal sig keeps all of
    /// them working and keeps the rendering a type a user could have written.
    pub(super) top_clause: TopClause<T>,
    /// Whether SEVERAL clauses cover the axis between them. The axes with a
    /// single-sig top answer structurally and exactly, so the boundary asks no
    /// descriptor arithmetic for saturation at all; an axis with no reachable
    /// top answers `false` outright. Only the callable axis, which this
    /// boundary does not absorb, defers to the calculator.
    pub(super) multi_clause_saturates: MultiClauseSaturates<T>,
}

/// `narrower ⊆ wider` for two interned types. Injected so every answer comes
/// from `Types`' comparison cache, and it is the ONLY question this module
/// asks of the calculator.
pub(super) type IsSubtype<'a> = &'a dyn Fn(&Ty, &Ty) -> bool;

/// One axis's structural reading of "is this clause inside its siblings".
pub(super) type CoverageRule<T> = fn(TyCtx<'_>, &Conj<T>, &[&Conj<T>], IsSubtype<'_>) -> Coverage;

/// This axis's top written as one clause, built from a sig the axis carries.
pub(super) type TopClause<T> = fn(TyCtx<'_>, &[Conj<T>]) -> Option<Conj<T>>;

/// Whether several clauses cover the axis between them.
pub(super) type MultiClauseSaturates<T> = fn(TyCtx<'_>, &[Conj<T>], Covers<'_>) -> bool;

/// What an axis can say about one clause against its surviving siblings
/// without descriptor arithmetic.
pub(super) enum Coverage {
    /// Proven inside the union of the siblings.
    Covered,
    /// Proven outside it, so the exact question would only say so again.
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

pub(super) const TUPLES: AxisView<TupleSig> = AxisView {
    install: |d, clauses| d.tuples = clauses,
    // Products of non-empty sets compare coordinatewise: `∏Aᵢ ⊆ ∏Bᵢ` exactly
    // when every `Aᵢ ⊆ Bᵢ`, which is exact given an interned clause never
    // carries an empty coordinate.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (
                narrower.pos.as_slice(),
                narrower.neg.as_slice(),
                wider.pos.as_slice(),
                wider.neg.as_slice(),
            ) {
                ([a], [], [b], []) => {
                    a.elems.len() == b.elems.len() && a.elems.iter().zip(b.elems.iter()).all(|(x, y)| sub(x, y))
                }
                _ => false,
            }
    },
    coverage: |cx, clause, siblings, _subtype| {
        let ([ours], []) = (clause.pos.as_slice(), clause.neg.as_slice()) else {
            return Coverage::Unproven;
        };
        let mut rects: Vec<&[Ty]> = Vec::with_capacity(siblings.len());
        for sibling in siblings {
            match (sibling.pos.as_slice(), sibling.neg.as_slice()) {
                ([theirs], []) => rects.push(&theirs.elems),
                // A clause carrying a negative contributes a shape this filter
                // cannot read, so the exact question decides.
                _ => return Coverage::Unproven,
            }
        }
        positionwise_gate(cx, &ours.elems, &rects)
    },
    // Tuple arity is unbounded, so no finite union of products is every
    // product and the axis never reaches its top.
    clause_is_top: |_, _| false,
    top_clause: |_, _| None,
    multi_clause_saturates: |_, _, _| false,
};
pub(super) const LISTS: AxisView<super::sigs::ListSig> = AxisView {
    install: |d, clauses| d.lists = clauses,
    // A plain list clause has two exact dimensions: whether it admits `[]`,
    // and what its non-empty fragment's element type is.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (
                narrower.pos.as_slice(),
                narrower.neg.as_slice(),
                wider.pos.as_slice(),
                wider.neg.as_slice(),
            ) {
                ([a], [], [b], []) => {
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
        let ([ours], []) = (clause.pos.as_slice(), clause.neg.as_slice()) else {
            return Coverage::Unproven;
        };
        let mut plain = Vec::with_capacity(siblings.len());
        for sibling in siblings {
            match (sibling.pos.as_slice(), sibling.neg.as_slice()) {
                ([theirs], []) => plain.push(theirs),
                _ => return Coverage::Unproven,
            }
        }
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
    // Every list is the one that admits `[]` and every element.
    clause_is_top: |cx, c| match (c.pos.as_slice(), c.neg.as_slice()) {
        ([sig], []) => sig.empty && sig.elem.is_some_and(|elem| cx.descr(&elem).looks_full()),
        _ => false,
    },
    top_clause: |cx, clauses| {
        full_child(cx, clauses, |sig| sig.elem).map(|elem| {
            Conj::pos_of(super::sigs::ListSig {
                empty: true,
                elem: Some(elem),
            })
        })
    },
    // Every list is `[]` plus every non-empty list, and a list over `A ∪ B`
    // is in neither `[A]` nor `[B]` — so a union covers the axis exactly when
    // one clause admits `[]` and ONE clause already admits every element.
    // Structural, and exact.
    multi_clause_saturates: |cx, clauses, _| {
        let sigs = || clauses.iter().flat_map(|c| c.pos.iter());
        clauses.iter().all(|c| c.neg.is_empty() && c.pos.len() == 1)
            && sigs().any(|sig| sig.empty)
            && sigs().any(|sig| sig.elem.is_some_and(|elem| cx.descr(&elem).looks_full()))
    },
};
pub(super) const RESOURCES: AxisView<super::sigs::ResourceSig> = AxisView {
    install: |d, clauses| d.resources = clauses,
    // A resource wraps one payload, and the kernel meets two resources by
    // meeting their payloads, so containment is the payload's.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (
                narrower.pos.as_slice(),
                narrower.neg.as_slice(),
                wider.pos.as_slice(),
                wider.neg.as_slice(),
            ) {
                ([a], [], [b], []) => sub(&a.payload, &b.payload),
                _ => false,
            }
    },
    // EXACT: a resource carries ONE payload, and the kernel meets two
    // resources by meeting their payloads and subtracts by subtracting them,
    // so `resource(C) ⊆ ⋃ resource(Aᵢ)` exactly when `C ⊆ ⋃ Aᵢ`. Every
    // sibling contributes, overlapping or not — the union only grows and the
    // test is on the payloads themselves.
    coverage: |cx, clause, siblings, _| {
        let ([ours], []) = (clause.pos.as_slice(), clause.neg.as_slice()) else {
            return Coverage::Unproven;
        };
        let mut reachable = Descr::none();
        for sibling in siblings {
            match (sibling.pos.as_slice(), sibling.neg.as_slice()) {
                ([theirs], []) => reachable = reachable.union(cx, cx.descr(&theirs.payload)),
                _ => return Coverage::Unproven,
            }
        }
        if cx.descr(&ours.payload).is_subtype(cx, &reachable) {
            Coverage::Covered
        } else {
            Coverage::NotCovered
        }
    },
    clause_is_top: |cx, c| match (c.pos.as_slice(), c.neg.as_slice()) {
        ([sig], []) => cx.descr(&sig.payload).looks_full(),
        _ => false,
    },
    top_clause: |cx, clauses| {
        full_child(cx, clauses, |sig| Some(sig.payload))
            .map(|payload| Conj::pos_of(super::sigs::ResourceSig { payload }))
    },
    // `resource(A) ∨ resource(B)` IS `resource(A ∨ B)`, so the axis is every
    // resource exactly when the union of the payloads is. Structural, and
    // exact.
    multi_clause_saturates: |cx, clauses, _| {
        clauses.iter().all(|c| c.neg.is_empty() && c.pos.len() == 1)
            && clauses
                .iter()
                .flat_map(|c| c.pos.iter())
                .fold(Descr::none(), |acc, sig| acc.union(cx, cx.descr(&sig.payload)))
                .looks_full()
    },
};
pub(super) const MAPS: AxisView<super::sigs::MapSig> = AxisView {
    install: |d, clauses| d.maps = clauses,
    // A map clause constrains exactly the fields it names, so the clause that
    // names MORE is the narrower one, and on the fields they share the
    // narrower one's types are inside the wider one's.
    clause_covers: |wider, narrower, sub| {
        factors_are_superset(wider, narrower)
            || match (
                narrower.pos.as_slice(),
                narrower.neg.as_slice(),
                wider.pos.as_slice(),
                wider.neg.as_slice(),
            ) {
                ([a], [], [b], []) => {
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
        let ([ours], []) = (clause.pos.as_slice(), clause.neg.as_slice()) else {
            return Coverage::Unproven;
        };
        let mut same_tag = Vec::with_capacity(siblings.len());
        for sibling in siblings {
            match (sibling.pos.as_slice(), sibling.neg.as_slice()) {
                ([theirs], []) if theirs.tag == ours.tag => same_tag.push(theirs),
                ([theirs], []) if theirs.tag != ours.tag => {}
                _ => return Coverage::Unproven,
            }
        }
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
    // A `MapSig` always carries a tag, and struct tags are unbounded, so no
    // finite union of map clauses is every map: a field-less PLAIN clause is
    // every plain map and says nothing about `%Range{}`. The axis has no top
    // it can reach.
    clause_is_top: |_, _| false,
    top_clause: |_, _| None,
    multi_clause_saturates: |_, _, _| false,
};

/// The `any` a saturating axis is already carrying. Saturation only fires
/// once some clause's child is unrestricted, so the type is in hand and needs
/// no minting.
fn full_child<T>(cx: TyCtx<'_>, clauses: &[Conj<T>], child: fn(&T) -> Option<Ty>) -> Option<Ty> {
    clauses
        .iter()
        .flat_map(|c| c.pos.iter())
        .filter_map(child)
        .find(|ty| cx.descr(ty).looks_full())
}

/// The callable axis, absorbed only where a RENDERING asks for it. Intern
/// leaves this axis alone — see the module doc — so its clause rule is the
/// axis-independent one and every real question goes to the calculator.
pub(super) const FUNCS: AxisView<super::sigs::ArrowSig> = AxisView {
    install: |d, clauses| d.funcs = clauses,
    clause_covers: |wider, narrower, _| factors_are_superset(wider, narrower),
    coverage: |_, _, _, _| Coverage::Unproven,
    // An arrow can be the whole axis (`(X) -> any` constrains nothing a
    // callable could fail), but only the calculator can say so: a clause
    // naming a closure literal is one construction, not every callable.
    clause_is_top: |_, _| false,
    top_clause: |_, _| Some(Conj::top()),
    multi_clause_saturates: |_, clauses, covers| axis_covers_its_top(covers, clauses, |d, c| d.funcs = c),
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
    if let ([p], []) = (c.pos.as_slice(), c.neg.as_slice()) {
        return p.elems.iter().any(is_empty_ty);
    }
    emptiness::tuple_clause_empty(cx, c, &mut emptiness::Memo::default())
}

fn retain_inhabited<T>(
    cx: TyCtx<'_>,
    clauses: &mut Vec<Conj<T>>,
    clause_empty: fn(TyCtx<'_>, &Conj<T>, &mut emptiness::Memo) -> bool,
) {
    clauses.retain(|clause| !clause_empty(cx, clause, &mut emptiness::Memo::default()));
}

/// Drop what the survivors already cover, then collapse to the axis top if
/// what is left covers the axis.
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
    drop_covered_clauses(cx, clauses, subtype, covers, view);
    if axis_is_saturated(cx, clauses, covers, view)
        && let Some(top) = (view.top_clause)(cx, clauses)
    {
        *clauses = vec![top];
    }
}

/// One clause decides saturation on its own — exactly, and structurally. Only
/// several clauses covering the axis BETWEEN them need the calculator, and
/// only the callable axis, which this boundary does not absorb, still does.
pub(super) fn axis_is_saturated<T: Clone + 'static>(
    cx: TyCtx<'_>,
    clauses: &[Conj<T>],
    covers: Covers<'_>,
    view: &AxisView<T>,
) -> bool {
    match clauses {
        // The axes with a single-sig top recognize it structurally, which is
        // exact and costs nothing.
        [only] if (view.clause_is_top)(cx, only) => true,
        _ => (view.multi_clause_saturates)(cx, clauses, covers),
    }
}

/// `wider ⊇ narrower` for two one-axis descriptors. Injected so the caller
/// answers through its memo; the relation itself is `Descr::is_subtype`.
pub(super) type Covers<'a> = &'a dyn Fn(&Descr, &Descr) -> bool;

/// Survivorship is threaded through the walk rather than decided pairwise
/// afterwards, which is what leaves exact duplicates with one survivor: the
/// first copy is covered by the second and goes, and the second is then
/// covered by nothing. Clauses are visited in index order, which the clause
/// sort at intern made the canonical order, so which of a mutually-covering
/// pair lives is a function of what the axis says and not of how it was built.
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

/// Whether the clauses between them denote the whole axis.
pub(super) fn axis_covers_its_top<T: Clone>(covers: Covers<'_>, clauses: &[Conj<T>], install: InstallAxis<T>) -> bool {
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
