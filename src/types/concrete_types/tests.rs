use super::bits::BasicBits;
use super::conj::Conj;
use super::dnf::is_dnf_top;
use super::sigs::{ArrowSig, ClosureLit};
use super::*;
use crate::fz_ir::FnId;
use crate::types::{MapKey, Nominals};
use std::collections::{BTreeMap, HashMap};

// (`str_t` was promoted to a public Descr constructor by fz-ul4.31.1.)
impl BasicBits {
    pub(super) const fn raw(self) -> u32 {
        self.0
    }
}

#[test]
fn top_and_bottom_render() {
    assert_eq!(Descr::any().to_string(), "any");
    assert_eq!(Descr::none().to_string(), "none");
}

#[test]
fn each_basic_constructor_renders_its_name() {
    assert_eq!(Descr::nil().to_string(), "nil");
    assert_eq!(Descr::bool_t().to_string(), "bool");
    assert_eq!(Descr::int().to_string(), "int");
    assert_eq!(Descr::float().to_string(), "float");
    assert_eq!(Descr::str_t().to_string(), "binary");
}

#[test]
fn atom_top_and_lit() {
    assert_eq!(Descr::atom_top().to_string(), "atom");
    assert_eq!(Descr::atom_lit("ok").to_string(), ":ok");
    assert_eq!(Descr::atom_lit("error").to_string(), ":error");
}

#[test]
fn type_test_atom_helpers_report_shape() {
    let finite = Descr::atom_lit("ok").union(&Descr::atom_lit("error"));
    assert_eq!(
        finite.type_test_atom_literals(),
        vec!["error".to_string(), "ok".to_string()]
    );
    assert!(!finite.type_test_atom_is_any());
    assert!(!finite.type_test_atom_is_cofinite());

    let any = Descr::atom_top();
    assert!(any.type_test_atom_is_any());
    assert!(any.type_test_atom_literals().is_empty());
}

#[test]
fn type_test_struct_names_report_impl_targets() {
    let target = Descr::opaque_of("impl-target::Range");
    assert_eq!(target.type_test_struct_names(), vec!["Range".to_string()]);

    let ordinary_opaque = Descr::opaque_of("pid");
    assert!(ordinary_opaque.type_test_struct_names().is_empty());
}

#[test]
fn tuple_constructor() {
    let t = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    assert_eq!(t.to_string(), "{int, binary}");
}

#[test]
fn list_constructor() {
    let l = Descr::list_of(Descr::int());
    assert_eq!(l.to_string(), "list(int)");
}

#[test]
fn empty_and_non_empty_list_shapes_are_disjoint() {
    let empty = Descr::empty_list();
    let non_empty = Descr::non_empty_list_of(Descr::any());
    assert_eq!(empty.to_string(), "[]");
    assert_eq!(non_empty.to_string(), "nonempty_list(any)");
    assert!(empty.intersect(&non_empty).is_empty());
    assert!(non_empty.intersect(&empty).is_empty());
}

#[test]
fn empty_union_non_empty_list_rejoins_to_possibly_empty_list() {
    let empty = Descr::empty_list();
    let non_empty = Descr::non_empty_list_of(Descr::int());
    assert_eq!(empty.union(&non_empty).to_string(), "list(int)");
    assert_eq!(non_empty.union(&empty).to_string(), "list(int)");
}

#[test]
fn arrow_constructor() {
    let f = Descr::arrow([Descr::int(), Descr::int()], Descr::int());
    assert_eq!(f.to_string(), "(int, int) -> int");
}

#[test]
fn nested_descriptors_render() {
    // list of {atom :ok, int} OR {atom :error, str}
    // (we don't have union yet, so just check one is well-formed)
    let ok = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
    assert_eq!(ok.to_string(), "{:ok, int}");
    let nested = Descr::list_of(ok);
    assert_eq!(nested.to_string(), "list({:ok, int})");
}

#[test]
fn equality_is_structural() {
    assert_eq!(Descr::int(), Descr::int());
    assert_ne!(Descr::int(), Descr::float());
    let a = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    let b = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    assert_eq!(a, b);
}

#[test]
fn looks_empty_distinguishes_none_from_others() {
    assert!(Descr::none().looks_empty());
    assert!(!Descr::any().looks_empty());
    assert!(!Descr::int().looks_empty());
    assert!(!Descr::atom_lit("ok").looks_empty());
    assert!(!Descr::tuple_of([Descr::int()]).looks_empty());
}

// ---- operations: identities ----

#[test]
fn union_identity_with_none() {
    let a = Descr::int();
    assert_eq!(a.union(&Descr::none()), a);
    assert_eq!(Descr::none().union(&a), a);
}

/// fz-sj6.1 — ∨ is idempotent. Unioning a list-typed Descr with
/// itself N times must keep exactly one clause, not N.
#[test]
fn union_idempotent_on_repeated_list_descrs() {
    let lst = Descr::list_of(Descr::int_lit(1).union(&Descr::int_lit(2)));
    let mut acc = lst.clone();
    for _ in 0..15 {
        acc = acc.union(&lst);
    }
    assert_eq!(
        acc.lists.len(),
        1,
        "expected 1 clause after 15 self-unions, got {}: {:?}",
        acc.lists.len(),
        acc
    );
    assert!(acc.is_equiv(&lst), "self-union must equal original: {} vs {}", acc, lst);
}

/// Distinct list-element types must remain distinct under dedup
/// (only EXACT-equal clauses collapse, not merge-by-shape).
#[test]
fn union_keeps_distinct_list_clauses() {
    let a = Descr::list_of(Descr::int());
    let b = Descr::list_of(Descr::float());
    let u = a.union(&b);
    assert_eq!(
        u.lists.len(),
        2,
        "list(int) ∨ list(float) must keep 2 clauses, got {}: {:?}",
        u.lists.len(),
        u
    );
}

/// fz-et8 — subsumption-based dedup at union. `list(int)` is a
/// strict subtype of `list(int|float)`, so their union must
/// collapse to the superset clause alone.
#[test]
fn union_drops_subsumed_list_clause() {
    let narrow = Descr::list_of(Descr::int());
    let wide = Descr::list_of(Descr::int().union(&Descr::float()));
    let u = narrow.union(&wide);
    assert_eq!(
        u.lists.len(),
        1,
        "list(int) ∨ list(int|float) must collapse to 1 clause, got {}: {:?}",
        u.lists.len(),
        u
    );
    assert!(
        u.is_equiv(&wide),
        "subsumed-union result must equal the superset: {} vs {}",
        u,
        wide
    );
    // Order-independence.
    let v = wide.union(&narrow);
    assert_eq!(
        v.lists.len(),
        1,
        "list(int|float) ∨ list(int) must also collapse, got {}: {:?}",
        v.lists.len(),
        v
    );
    assert!(v.is_equiv(&wide));
}

#[test]
fn intersect_identity_with_any() {
    // a ∩ any = a — every component shrinks to itself.
    for a in [Descr::int(), Descr::atom_lit("ok"), Descr::str_t()] {
        assert_eq!(a.intersect(&Descr::any()), a);
        assert_eq!(Descr::any().intersect(&a), a);
    }
}

#[test]
fn intersect_with_none_is_none() {
    let a = Descr::int().union(&Descr::atom_lit("ok"));
    assert!(a.intersect(&Descr::none()).looks_empty());
}

#[test]
fn neg_top_bottom() {
    assert!(Descr::any().neg().looks_empty());
    assert!(Descr::none().neg().looks_full());
}

// ---- basic bits ----

#[test]
fn basics_union_and_intersect() {
    let i = Descr::int();
    let f = Descr::float();
    let u = i.union(&f);
    assert!(u.ints.is_any());
    assert!(u.floats.is_any());
    assert_eq!(u.to_string(), "int | float");

    let inter = i.intersect(&f);
    assert!(inter.looks_empty());
}

#[test]
fn neg_int_top_saturates_other_kinds() {
    let n = Descr::int().neg();
    assert!(n.ints.is_none(), "ints axis flipped to empty");
    assert!(n.floats.is_any());
    assert!(n.atoms.is_any());
    assert!(is_dnf_top(&n.tuples));
}

#[test]
fn diff_self_is_empty_basic() {
    assert!(Descr::int().diff(&Descr::int()).looks_empty());
}

// ---- atom set ----

#[test]
fn atom_lits_union() {
    let a = Descr::atom_lit("ok").union(&Descr::atom_lit("error"));
    // BTreeSet ordering -> :error comes before :ok
    assert_eq!(a.to_string(), ":error | :ok");
}

#[test]
fn atom_lit_subsumed_by_atom_top() {
    let big = Descr::atom_lit("ok").union(&Descr::atom_top());
    assert!(big.atoms.is_any());
}

#[test]
fn atom_lits_intersect_disjoint_is_empty() {
    let inter = Descr::atom_lit("ok").intersect(&Descr::atom_lit("error"));
    assert!(inter.looks_empty());
}

#[test]
fn atom_lit_intersect_atom_top_is_lit() {
    let a = Descr::atom_lit("ok");
    assert_eq!(a.intersect(&Descr::atom_top()), a);
}

#[test]
fn neg_atom_lit_excludes_only_that_atom() {
    let n = Descr::atom_lit("ok").neg();
    assert!(n.atoms.cofinite);
    assert_eq!(n.atoms.set.len(), 1);
    assert!(n.atoms.set.contains("ok"));
}

// ---- DNF mechanics ----

#[test]
fn tuple_union_keeps_both_clauses() {
    let a = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
    let b = Descr::tuple_of([Descr::atom_lit("error"), Descr::str_t()]);
    let u = a.union(&b);
    assert_eq!(u.tuples.len(), 2, "union concatenates DNF clauses");
    assert_eq!(u.to_string(), "{:ok, int} | {:error, binary}");
}

#[test]
fn tuple_intersect_cross_products_clauses() {
    let a = Descr::tuple_of([Descr::int()]);
    let b = Descr::tuple_of([Descr::str_t()]);
    let inter = a.intersect(&b);
    // fz-jvo — same-arity tuple pos sigs now merge via
    // per-element intersection (TupleSig::intersect_pos),
    // collapsing to a single sig with elem-wise intersected
    // components. Semantically the result is empty (int ∩ str
    // is empty, so tuple-of-empty is empty), and structurally
    // it lives as one pos sig of length 1.
    assert_eq!(inter.tuples.len(), 1);
    assert_eq!(inter.tuples[0].pos.len(), 1);
    assert!(inter.tuples[0].neg.is_empty());
    assert!(inter.is_empty(), "tuple(int) ∩ tuple(str) is uninhabited");
}

#[test]
fn dnf_neg_empty_is_top_clause() {
    // The lists DNF on `Descr::int()` is empty (no lists in this descr).
    // ¬(empty DNF) = ¬false = true = saturated DNF.
    let n = Descr::int().neg();
    assert!(is_dnf_top(&n.lists));
    assert!(is_dnf_top(&n.tuples));
    assert!(is_dnf_top(&n.funcs));
}

#[test]
fn dnf_neg_top_is_empty() {
    // Negating Descr::any() makes every kind go from saturated to empty.
    let n = Descr::any().neg();
    assert!(n.tuples.is_empty());
    assert!(n.lists.is_empty());
    assert!(n.funcs.is_empty());
}

#[test]
fn neg_tuple_clause_produces_de_morgan_expansion() {
    // ¬{int, str} as a DNF should have two single-literal negative clauses.
    let t = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    let n = t.neg();
    // n.tuples = ¬ [Conj { pos: [{int,str}], neg: [] }]
    //          = [Conj { pos: [], neg: [{int,str}] }]
    assert_eq!(n.tuples.len(), 1);
    assert_eq!(n.tuples[0].pos.len(), 0);
    assert_eq!(n.tuples[0].neg.len(), 1);
}

// ---- combined ----

#[test]
fn union_int_and_atom_lit() {
    let d = Descr::int().union(&Descr::atom_lit("ok"));
    assert_eq!(d.to_string(), "int | :ok");
}

#[test]
fn diff_int_or_float_minus_int_is_float() {
    let either = Descr::int().union(&Descr::float());
    let only_float = either.diff(&Descr::int());
    assert_eq!(only_float, Descr::float());
}

// ---- emptiness / subtyping ----

#[test]
fn empty_basics() {
    assert!(Descr::none().is_empty());
    assert!(!Descr::any().is_empty());
    assert!(!Descr::int().is_empty());
    assert!(!Descr::atom_lit("ok").is_empty());
    assert!(Descr::int().diff(&Descr::int()).is_empty());
    assert!(Descr::int().intersect(&Descr::float()).is_empty());
}

#[test]
fn subtype_basics() {
    assert!(Descr::int().is_subtype(&Descr::int()));
    assert!(Descr::int().is_subtype(&Descr::int().union(&Descr::float())));
    assert!(!Descr::int().union(&Descr::float()).is_subtype(&Descr::int()));
    assert!(!Descr::int().is_subtype(&Descr::atom_top()));
    assert!(Descr::none().is_subtype(&Descr::int()));
    assert!(Descr::int().is_subtype(&Descr::any()));
}

#[test]
fn subtype_atoms() {
    assert!(Descr::atom_lit("ok").is_subtype(&Descr::atom_top()));
    assert!(!Descr::atom_top().is_subtype(&Descr::atom_lit("ok")));
    let either = Descr::atom_lit("ok").union(&Descr::atom_lit("error"));
    assert!(Descr::atom_lit("ok").is_subtype(&either));
    assert!(!either.is_subtype(&Descr::atom_lit("ok")));
    assert!(!Descr::atom_lit("ok").is_subtype(&Descr::atom_lit("error")));
}

#[test]
fn equiv_after_double_neg() {
    let a = Descr::int().union(&Descr::atom_lit("ok"));
    assert!(a.is_equiv(&a.neg().neg()));
}

#[test]
fn equiv_de_morgan() {
    let a = Descr::int();
    let b = Descr::atom_lit("ok");
    // ¬(a ∪ b) ≡ ¬a ∩ ¬b
    let lhs = a.union(&b).neg();
    let rhs = a.neg().intersect(&b.neg());
    assert!(lhs.is_equiv(&rhs));
    // ¬(a ∩ b) ≡ ¬a ∪ ¬b
    let lhs = a.intersect(&b).neg();
    let rhs = a.neg().union(&b.neg());
    assert!(lhs.is_equiv(&rhs));
}

// ---- tuples ----

#[test]
fn tuple_subtype_same_arity() {
    let t1 = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    let t2 = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    assert!(t1.is_subtype(&t2));
}

#[test]
fn tuple_subtype_arity_mismatch() {
    let t1 = Descr::tuple_of([Descr::int()]);
    let t2 = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    assert!(!t1.is_subtype(&t2));
    assert!(!t2.is_subtype(&t1));
}

#[test]
fn tuple_covariance_in_components() {
    // {int, str} <: {int|float, str}
    let narrow = Descr::tuple_of([Descr::int(), Descr::str_t()]);
    let wide = Descr::tuple_of([Descr::int().union(&Descr::float()), Descr::str_t()]);
    assert!(narrow.is_subtype(&wide));
    assert!(!wide.is_subtype(&narrow));
}

#[test]
fn tuple_union_distributes_over_components() {
    // {int|float, str} <: {int, str} ∪ {float, str}
    let lhs = Descr::tuple_of([Descr::int().union(&Descr::float()), Descr::str_t()]);
    let rhs = Descr::tuple_of([Descr::int(), Descr::str_t()]).union(&Descr::tuple_of([Descr::float(), Descr::str_t()]));
    assert!(lhs.is_subtype(&rhs));
    assert!(rhs.is_subtype(&lhs));
    assert!(lhs.is_equiv(&rhs));
}

// ---- lists ----

#[test]
fn list_subtype_in_element_type() {
    // list(int) <: list(int|float)
    let narrow = Descr::list_of(Descr::int());
    let wide = Descr::list_of(Descr::int().union(&Descr::float()));
    assert!(narrow.is_subtype(&wide));
    assert!(!wide.is_subtype(&narrow));
}

#[test]
fn empty_list_is_subtype_of_any_possibly_empty_list() {
    // `[]` is its own singleton shape. Since `list(T)` is the union of
    // `[]` and non-empty lists with element type T, `[]` is a subtype of
    // every possibly-empty list type and disjoint from non-empty lists.
    let empty_list = Descr::empty_list();
    assert!(empty_list.is_subtype(&Descr::list_of(Descr::int())));
    assert!(empty_list.is_subtype(&Descr::list_of(Descr::atom_top())));
    assert!(empty_list.intersect(&Descr::non_empty_list_of(Descr::any())).is_empty());
}

#[test]
fn list_union_does_not_distribute_homogeneously() {
    // Heterogeneous list types are NOT a union of homogeneous lists.
    // list({:a, :b}) ⊄ list(:a) ∪ list(:b)  — the list [:a, :b] would
    // have to live in one of the homogeneous types, but it doesn't.
    let mixed = Descr::list_of(Descr::atom_lit("a").union(&Descr::atom_lit("b")));
    let parts = Descr::list_of(Descr::atom_lit("a")).union(&Descr::list_of(Descr::atom_lit("b")));
    assert!(!mixed.is_subtype(&parts), "homogeneous lists do not cover mixed");
    // But the reverse holds:
    assert!(parts.is_subtype(&mixed));
}

// ---- arrows ----

#[test]
fn arrow_contravariance_in_input() {
    // (int|float) -> int   <:   int -> int   (wider input is subtype)
    let wider_in = Descr::arrow([Descr::int().union(&Descr::float())], Descr::int());
    let narrow_in = Descr::arrow([Descr::int()], Descr::int());
    assert!(wider_in.is_subtype(&narrow_in));
    assert!(!narrow_in.is_subtype(&wider_in));
}

#[test]
fn arrow_covariance_in_output() {
    // int -> int   <:   int -> (int|float)
    let narrow_out = Descr::arrow([Descr::int()], Descr::int());
    let wide_out = Descr::arrow([Descr::int()], Descr::int().union(&Descr::float()));
    assert!(narrow_out.is_subtype(&wide_out));
    assert!(!wide_out.is_subtype(&narrow_out));
}

#[test]
fn arrow_intersection_is_multiclause() {
    // (int -> int) ∩ (str -> str)  <:  (int|str) -> (int|str)
    // — the multi-clause function semantics. NOT equivalent because the
    // intersection knows which return type matches which input.
    let multi = Descr::arrow([Descr::int()], Descr::int()).intersect(&Descr::arrow([Descr::str_t()], Descr::str_t()));
    let combined = Descr::arrow(
        [Descr::int().union(&Descr::str_t())],
        Descr::int().union(&Descr::str_t()),
    );
    assert!(multi.is_subtype(&combined));
    assert!(
        !combined.is_subtype(&multi),
        "combined arrow loses the per-clause return refinement"
    );
}

// ---- mixed kinds ----

#[test]
fn disjoint_kinds_dont_subtype() {
    assert!(!Descr::int().is_subtype(&Descr::atom_top()));
    assert!(!Descr::atom_top().is_subtype(&Descr::int()));
    assert!(!Descr::int().is_subtype(&Descr::tuple_of([Descr::int()])));
    assert!(!Descr::list_of(Descr::int()).is_subtype(&Descr::tuple_of([Descr::int()])));
}

#[test]
fn intersection_with_disjoint_is_empty() {
    assert!(Descr::int().intersect(&Descr::atom_top()).is_empty());
    assert!(
        Descr::list_of(Descr::int())
            .intersect(&Descr::tuple_of([Descr::int()]))
            .is_empty()
    );
}

#[test]
fn ok_or_error_result_subtype() {
    // Result(int, atom) = {:ok, int} ∪ {:error, atom}
    // {:ok, int} <: Result(int, atom)
    let result_t = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()])
        .union(&Descr::tuple_of([Descr::atom_lit("error"), Descr::atom_top()]));
    let an_ok = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
    assert!(an_ok.is_subtype(&result_t));
    // {:ok, str} </: Result(int, atom)
    let bad = Descr::tuple_of([Descr::atom_lit("ok"), Descr::str_t()]);
    assert!(!bad.is_subtype(&result_t));
}

// ---- singleton types (int / float / str) ----

#[test]
fn int_lit_subtype_of_int_top() {
    assert!(Descr::int_lit(0).is_subtype(&Descr::int()));
    assert!(Descr::int_lit(42).is_subtype(&Descr::int()));
    assert!(!Descr::int().is_subtype(&Descr::int_lit(0)));
}

#[test]
fn int_lit_distinct_singletons() {
    assert!(!Descr::int_lit(0).is_subtype(&Descr::int_lit(1)));
    assert!(Descr::int_lit(0).intersect(&Descr::int_lit(1)).is_empty());
    let zero_or_one = Descr::int_lit(0).union(&Descr::int_lit(1));
    assert!(Descr::int_lit(0).is_subtype(&zero_or_one));
    assert!(zero_or_one.is_subtype(&Descr::int()));
}

#[test]
fn int_lit_diff_excludes_value() {
    // int \ {0} keeps every int except 0
    let nonzero = Descr::int().diff(&Descr::int_lit(0));
    assert!(!Descr::int_lit(0).is_subtype(&nonzero));
    assert!(Descr::int_lit(1).is_subtype(&nonzero));
}

#[test]
fn float_lit_singletons() {
    assert!(Descr::float_lit(1.5).is_subtype(&Descr::float()));
    assert!(!Descr::float_lit(1.5).is_subtype(&Descr::float_lit(2.5)));
    let pair = Descr::float_lit(1.5).union(&Descr::float_lit(2.5));
    assert_eq!(pair.to_string(), "1.5 | 2.5");
}

#[test]
fn singleton_in_tuple() {
    // {:ok, 0} <: {:ok, int} but {:ok, 0} </: {:ok, 1}
    let one = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int_lit(0)]);
    let any_ok = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
    let ok_one = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int_lit(1)]);
    assert!(one.is_subtype(&any_ok));
    assert!(!one.is_subtype(&ok_one));
}

#[test]
fn display_int_singleton() {
    assert_eq!(Descr::int_lit(42).to_string(), "42");
    assert_eq!(Descr::int_lit(0).union(&Descr::int_lit(1)).to_string(), "0 | 1");
}

// ---- maps ----

fn ak(s: &str) -> MapKey {
    MapKey::Atom(s.into())
}

#[test]
fn map_top_and_constructor() {
    assert_eq!(Descr::map_top().to_string(), "map");
    let m = Descr::map_of([(ak("name"), Descr::str_t()), (ak("age"), Descr::int())]);
    // BTreeMap orders by key, so :age comes before :name
    assert_eq!(m.to_string(), "%{:age: int, :name: binary}");
}

#[test]
fn map_subtype_open_record() {
    // %{a: int, b: str} <: %{a: int}  (more required keys = smaller set)
    let big = Descr::map_of([(ak("a"), Descr::int()), (ak("b"), Descr::str_t())]);
    let small = Descr::map_of([(ak("a"), Descr::int())]);
    assert!(big.is_subtype(&small));
    assert!(!small.is_subtype(&big));
}

#[test]
fn map_subtype_value_covariance() {
    // %{a: 0} <: %{a: int}
    let narrow = Descr::map_of([(ak("a"), Descr::int_lit(0))]);
    let wide = Descr::map_of([(ak("a"), Descr::int())]);
    assert!(narrow.is_subtype(&wide));
    assert!(!wide.is_subtype(&narrow));
}

#[test]
fn map_with_empty_value_is_empty() {
    let bad = Descr::map_of([(ak("k"), Descr::int().intersect(&Descr::str_t()))]);
    assert!(bad.is_empty());
}

#[test]
fn map_top_is_subtype_of_itself_only() {
    let top = Descr::map_top();
    assert!(top.is_subtype(&top));
    let m = Descr::map_of([(ak("a"), Descr::int())]);
    assert!(m.is_subtype(&top));
    assert!(!top.is_subtype(&m), "map ⊄ %{{a: int}}");
}

#[test]
fn basic_bits_flags_are_disjoint() {
    let bits = [BasicBits::BINARY];
    for (i, a) in bits.iter().enumerate() {
        for b in &bits[i + 1..] {
            assert_eq!(a.raw() & b.raw(), 0, "bits should be disjoint: {:?} vs {:?}", a, b);
        }
    }
    // ALL covers exactly those bits and nothing else.
    let or_all = bits.iter().fold(0u32, |acc, b| acc | b.raw());
    assert_eq!(BasicBits::ALL.raw(), or_all);
}

// ----- .20.8: display_for_diag -----

#[test]
fn display_for_diag_caps_finite_literal_sets() {
    // A literal-set with 10 distinct ints should render the first
    // 5 plus an ellipsis "+5 more".
    let mut d = Descr::none();
    for i in 1..=10 {
        d = d.union(&Descr::int_lit(i));
    }
    let s = d.display_for_diag();
    // Exactly five comma-separated int values + an ellipsis.
    let pipe_parts: Vec<&str> = s.split(" | ").collect();
    assert!(pipe_parts.len() == 6, "expected 5 ints + ellipsis, got: {}", s);
    assert!(s.contains("(+5 more)"), "expected ellipsis, got: {}", s);
}

#[test]
fn display_for_diag_handles_top_and_bottom() {
    assert_eq!(Descr::any().display_for_diag(), "any");
    assert_eq!(Descr::none().display_for_diag(), "none");
}

#[test]
fn display_for_diag_renders_union_of_basic_kinds() {
    // int union atom — both are top kinds.
    let d = Descr::int().union(&Descr::atom_top());
    let s = d.display_for_diag();
    assert!(s.contains("int"), "got {}", s);
    assert!(s.contains("atom"), "got {}", s);
    assert!(s.contains(" | "), "got {}", s);
}

#[test]
fn display_for_diag_short_set_renders_untruncated() {
    // 3 atoms — under the cap, no ellipsis.
    let d = Descr::atom_lit("a".to_string())
        .union(&Descr::atom_lit("b".to_string()))
        .union(&Descr::atom_lit("c".to_string()));
    let s = d.display_for_diag();
    assert!(!s.contains("more"), "should not truncate: {}", s);
    assert!(s.contains(":a"));
    assert!(s.contains(":b"));
    assert!(s.contains(":c"));
}

// ---- fz-ul4.27.22.8 closure_lit tests ----

fn fid(n: u32) -> FnId {
    FnId(n)
}

#[test]
fn closure_lit_round_trips_through_accessor() {
    let cl = Descr::closure_lit(fid(7), vec![Descr::int_lit(10), Descr::int_lit(20)], 1);
    let tag = cl.as_closure_lit().expect("expected closure_lit");
    assert_eq!(tag.fn_id, fid(7));
    assert_eq!(tag.captures.len(), 2);
    assert_eq!(ty_descr(&tag.captures[0]), &Descr::int_lit(10));
    assert_eq!(ty_descr(&tag.captures[1]), &Descr::int_lit(20));
}

#[test]
fn plain_arrow_has_no_closure_lit() {
    let a = Descr::arrow([Descr::any()], Descr::any());
    assert!(a.as_closure_lit().is_none());
}

#[test]
fn closure_lit_renders_with_fn_id_and_captures() {
    let cl = Descr::closure_lit(fid(3), vec![Descr::int_lit(10), Descr::int_lit(20)], 1);
    let s = format!("{}", cl);
    assert!(s.starts_with("&fn3["), "got {}", s);
    assert!(s.contains("10"), "got {}", s);
    assert!(s.contains("20"), "got {}", s);
    assert!(s.contains(" -> "), "got {}", s);
}

#[test]
fn closure_lit_equality_is_by_fn_id_and_captures() {
    let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
    let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
    let c = Descr::closure_lit(fid(3), vec![Descr::int_lit(99)], 1);
    let d = Descr::closure_lit(fid(4), vec![Descr::int_lit(10)], 1);
    assert_eq!(a, b);
    assert_ne!(a, c);
    assert_ne!(a, d);
}

#[test]
fn closure_lit_union_exact_dedups() {
    // Identical singletons unioned → single clause, identity preserved.
    let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
    let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
    let u = a.union(&b);
    assert_eq!(u, a, "exact dup union should idempote");
    assert!(u.as_closure_lit().is_some(), "still a singleton");
}

#[test]
fn closure_lit_union_different_captures_keeps_both_clauses() {
    // Different captures with same FnId → two clauses today (precision
    // collapse is the responsibility of 22.9's resolve_closure_return).
    let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
    let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(20)], 1);
    let u = a.union(&b);
    assert_eq!(u.funcs.len(), 2, "expected two clauses: {}", u);
    // No longer a single-clause singleton — accessor returns None.
    assert!(u.as_closure_lit().is_none());
}

#[test]
fn closure_lit_union_different_fn_ids_keeps_both_clauses() {
    let a = Descr::closure_lit(fid(3), vec![], 1);
    let b = Descr::closure_lit(fid(4), vec![], 1);
    let u = a.union(&b);
    assert_eq!(u.funcs.len(), 2, "expected two clauses: {}", u);
    assert!(u.as_closure_lit().is_none());
}

#[test]
fn closure_lit_intersect_same_fn_narrows_captures() {
    // Same FnId, captures intersect elementwise.
    // int ∩ int_lit(10) = int_lit(10).
    let a = Descr::closure_lit(fid(3), vec![Descr::int()], 1);
    let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
    let i = a.intersect(&b);
    let tag = i.as_closure_lit().expect("expected singleton after intersect");
    assert_eq!(tag.fn_id, fid(3));
    assert_eq!(ty_descr(&tag.captures[0]), &Descr::int_lit(10));
}

#[test]
fn closure_lit_intersect_different_fn_ids_is_empty() {
    let a = Descr::closure_lit(fid(3), vec![], 1);
    let b = Descr::closure_lit(fid(4), vec![], 1);
    let i = a.intersect(&b);
    assert!(
        i.is_empty(),
        "different-FnId closure_lits ∧ should be bottom: got {}",
        i
    );
}

#[test]
fn closure_lit_preserves_captures_for_recursive_spec_key() {
    // Closure captures are part of the closure value identity and ABI;
    // recursive spec-key widening preserves them while widening call args.
    let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
    let w = a.widen_for_recursive_spec_key();
    let tag = w
        .as_closure_lit()
        .expect("recursive spec-key widening should preserve singleton");
    assert_eq!(tag.fn_id, fid(3));
    assert_eq!(
        ty_descr(&tag.captures[0]),
        &Descr::int_lit(10),
        "recursive spec-key widening should preserve closure capture identity"
    );
}

// ---- opaque type tests ----

#[test]
fn opaque_renders_name() {
    let pid = Descr::opaque_of("pid");
    assert_eq!(pid.to_string(), "pid");
}

#[test]
fn opaque_is_not_subtype_of_underlying() {
    let pid = Descr::opaque_of("pid");
    let int = Descr::int();
    assert!(!pid.is_subtype(&int), "pid should NOT be a subtype of integer");
}

#[test]
fn underlying_is_not_subtype_of_opaque() {
    let pid = Descr::opaque_of("pid");
    let int = Descr::int();
    assert!(!int.is_subtype(&pid), "integer should NOT be a subtype of pid");
}

#[test]
fn opaque_is_subtype_of_itself() {
    let pid = Descr::opaque_of("pid");
    assert!(pid.is_subtype(&pid), "pid should be a subtype of itself");
}

// ------------------------------------------------------------------
// fz-axu.2 (K1) — brands axis
// ------------------------------------------------------------------

#[test]
fn brand_of_is_non_empty_and_distinguishable() {
    let utf8 = Descr::brand_of("utf8");
    assert!(!utf8.is_empty(), "brand_of must not be empty");
    assert!(!utf8.looks_full(), "brand_of must not look full");
    // Only the brands axis is populated.
    assert!(utf8.basic.is_empty());
    assert!(utf8.atoms.is_none());
    assert!(utf8.ints.is_none());
    assert!(utf8.opaques.is_none(), "brands and opaques are distinct axes");
    assert!(utf8.vars.is_none());
    assert!(!utf8.brands.is_none(), "brands axis must carry the tag");
}

#[test]
fn brand_is_subtype_of_itself() {
    let utf8 = Descr::brand_of("utf8");
    assert!(utf8.is_subtype(&utf8), "utf8 ⊆ utf8");
}

#[test]
fn two_distinct_brands_do_not_overlap() {
    let a = Descr::brand_of("utf8");
    let b = Descr::brand_of("ascii");
    let i = a.intersect(&b);
    assert!(i.is_empty(), "utf8 ∩ ascii must be empty: got {}", i);
}

#[test]
fn brand_union_with_any_becomes_any() {
    let utf8 = Descr::brand_of("utf8");
    let u = utf8.union(&Descr::any());
    assert!(u.looks_full(), "utf8 ∪ any must be any: got {}", u);
}

#[test]
fn brand_is_disjoint_from_same_name_opaque() {
    // Brands and opaques live in different axes — even if the tag
    // text matches, they don't overlap. K4's is_subtype rule reads
    // the inner; K1 only proves the lattice keeps them separate.
    let b = Descr::brand_of("X");
    let o = Descr::opaque_of("X");
    let i = b.intersect(&o);
    assert!(i.is_empty(), "brand(X) ∩ opaque(X) must be empty");
}

#[test]
fn brand_renders_finite_as_bare_name() {
    // Matches the opaque-display convention: finite singletons render
    // just the tag; the "brand" keyword shows up only in cofinite
    // forms (e.g. `brand \ {utf8}`).
    let utf8 = Descr::brand_of("utf8");
    assert_eq!(format!("{}", utf8), "utf8");
    // Cofinite case: ¬utf8 still belongs to the brands axis at top.
    let cofinite = utf8.neg();
    let s = format!("{}", cofinite);
    assert!(s.contains("brand \\ {utf8}"), "cofinite rendering: {}", s);
}

#[test]
fn any_contains_all_brands() {
    let any = Descr::any();
    assert!(any.brands.is_any(), "Descr::any().brands must be universe");
    let utf8 = Descr::brand_of("utf8");
    assert!(utf8.is_subtype(&any), "brand(utf8) ⊆ any");
}

#[test]
fn brand_singleton_extracts_the_tag() {
    let utf8 = Descr::brand_of("utf8");
    assert_eq!(utf8.as_brand_singleton(), Some("utf8"));
    let two = utf8.union(&Descr::brand_of("ascii"));
    assert_eq!(two.as_brand_singleton(), None, "multi-tag set has no singleton");
    assert_eq!(Descr::any().as_brand_singleton(), None, "cofinite has no singleton");
    assert_eq!(
        Descr::int().as_brand_singleton(),
        None,
        "non-brand axes don't yield a brand singleton"
    );
}

// fz-axu.5 (K4) — brand-aware subtype rule. A minted brand value
// (brands={B} ∧ structural T) is a subtype of T when brand_inners
// ratifies that B's inner is structurally T.

fn brand_inners(items: &[(&str, Descr)]) -> HashMap<String, Descr> {
    items.iter().map(|(n, d)| (n.to_string(), d.clone())).collect()
}

fn no_inners() -> HashMap<String, Descr> {
    HashMap::new()
}

// fz-bsx.1 — brand-erased (runtime representation) disjointness.

#[test]
fn erase_nominal_discharges_brand_to_inner() {
    // A minted brand is a pure tag (basic empty); erasure must REPLACE it
    // with its inner, not clear it (clearing would collapse to `none`).
    let inners = brand_inners(&[("utf8", Descr::str_t())]);
    let utf8 = Descr::brand_of("utf8");
    assert!(
        utf8.intersect(&Descr::str_t()).is_empty(),
        "pure tag ∩ binary is empty (the bug)"
    );
    assert!(
        utf8.erase_nominal(Nominals::new(&inners, &no_inners()))
            .is_equiv(&Descr::str_t()),
        "erase(utf8) must be binary",
    );
}

#[test]
fn value_disjoint_utf8_vs_binary_is_false() {
    // The core fix: a utf8 and an unbranded binary can be byte-equal.
    let inners = brand_inners(&[("utf8", Descr::str_t())]);
    let utf8 = Descr::brand_of("utf8");
    assert!(
        utf8.intersect(&Descr::str_t()).is_empty(),
        "brand-AWARE: disjoint (correct for typing)",
    );
    assert!(
        !utf8.value_disjoint(&Descr::str_t(), Nominals::new(&inners, &no_inners())),
        "brand-BLIND: NOT disjoint — `==` must run",
    );
}

#[test]
fn value_disjoint_nested_in_tuple_is_false() {
    // The original failure: {:ok, utf8} vs {:ok, binary} nested.
    let inners = brand_inners(&[("utf8", Descr::str_t())]);
    let lhs = Descr::tuple_of([Descr::atom_lit("ok"), Descr::brand_of("utf8")]);
    let rhs = Descr::tuple_of([Descr::atom_lit("ok"), Descr::str_t()]);
    assert!(
        lhs.intersect(&rhs).is_empty(),
        "brand-AWARE: the nested brand makes the tuple clauses disjoint (the bug)",
    );
    assert!(
        !lhs.value_disjoint(&rhs, Nominals::new(&inners, &no_inners())),
        "brand-BLIND: erasure recurses into the tuple — NOT disjoint",
    );
}

#[test]
fn value_disjoint_utf8_vs_int_is_true() {
    // Soundness: erasure must NOT over-collapse. A binary is never an int,
    // so a utf8 is never == an int; the fold here is still legitimate.
    let inners = brand_inners(&[("utf8", Descr::str_t())]);
    let utf8 = Descr::brand_of("utf8");
    assert!(
        utf8.value_disjoint(&Descr::int(), Nominals::new(&inners, &no_inners())),
        "utf8 vs int stays value-disjoint",
    );
}

#[test]
fn value_disjoint_distinct_atoms_is_true() {
    // Structural disjointness survives erasure (erasure only neutralises
    // the nominal axes): :ok vs :error is still definitely unequal.
    assert!(
        Descr::atom_lit("ok").value_disjoint(&Descr::atom_lit("error"), Nominals::new(&no_inners(), &no_inners()),),
        ":ok vs :error remains value-disjoint",
    );
}

// fz-bsx.6 — soundness backstop for value-disjointness. The eq-fold and the
// dead-binop lint may collapse a comparison to a constant ONLY when the
// operands are value-disjoint, so the dangerous direction is OVER-reporting
// disjointness (folding a comparison that could be true at runtime). This
// table pins both directions across the representative shapes; the
// static->runtime link itself is locked end-to-end by the integration
// fixtures (bsx_nested_eq proves not-disjoint => runtime true on all paths;
// vr5a_* prove disjoint => false).
#[test]
fn value_disjoint_soundness_table() {
    // utf8 and ascii both refine binary; both erase to a plain binary.
    let inners = brand_inners(&[("utf8", Descr::str_t()), ("ascii", Descr::str_t())]);
    let oi = no_inners();
    let utf8 = Descr::brand_of("utf8");
    let ascii = Descr::brand_of("ascii");
    let bin = Descr::str_t();
    let int = Descr::int();
    let ok = Descr::atom_lit("ok");
    let err = Descr::atom_lit("error");
    let ok_utf8 = Descr::tuple_of([ok.clone(), utf8.clone()]);
    let ok_bin = Descr::tuple_of([ok.clone(), bin.clone()]);
    let err_inv = Descr::tuple_of([err.clone(), Descr::atom_lit("invalid")]);

    // (a, b, expect_value_disjoint, why)
    let cases: &[(&Descr, &Descr, bool, &str)] = &[
        // Different runtime kinds can never be byte/structure equal: FOLDABLE.
        (&int, &bin, true, "int vs binary"),
        (&utf8, &int, true, "utf8 (a binary) vs int"),
        (&ok, &err, true, ":ok vs :error"),
        (
            &ok_utf8,
            &err_inv,
            true,
            "{:ok,utf8} vs {:error,:invalid} — tag differs",
        ),
        // Same runtime representation once brands are erased: NOT foldable —
        // these values can be equal, `==` must run.
        (&utf8, &bin, false, "utf8 vs unbranded binary"),
        (&ascii, &utf8, false, "ascii vs utf8 — distinct brands, same bytes"),
        (&utf8, &utf8, false, "utf8 vs utf8"),
        (&ok_utf8, &ok_bin, false, "{:ok,utf8} vs {:ok,binary} — nested brand"),
    ];
    for (a, b, expect, why) in cases {
        assert_eq!(
            a.value_disjoint(b, Nominals::new(&inners, &oi)),
            *expect,
            "value_disjoint mismatch: {}",
            why
        );
        // Symmetry: disjointness is order-independent.
        assert_eq!(
            b.value_disjoint(a, Nominals::new(&inners, &oi)),
            *expect,
            "value_disjoint not symmetric: {}",
            why
        );
    }
}

#[test]
fn is_subtype_under_discharges_brand_when_inner_fits() {
    // utf8 :: refines binary. A value typed `brands={utf8} ∧ str_t`
    // is a subtype of str_t under brand_inners[utf8 → str_t].
    let inners = brand_inners(&[("utf8", Descr::str_t())]);
    let mut minted = Descr::str_t();
    minted.brands = LiteralSet::lit("utf8".to_string());
    assert!(
        !minted.is_subtype(&Descr::str_t()),
        "strict lattice keeps the brand tag — minted is NOT a subtype without K4",
    );
    assert!(
        minted.is_subtype_under(&Descr::str_t(), &inners),
        "K4 rule: brand-tagged binary IS a subtype of binary",
    );
}

#[test]
fn is_subtype_under_keeps_brand_when_inner_does_not_fit() {
    // utf8 :: refines binary. A utf8 value is NOT a subtype of int,
    // because the inner is binary, not int.
    let inners = brand_inners(&[("utf8", Descr::str_t())]);
    let mut minted = Descr::str_t();
    minted.brands = LiteralSet::lit("utf8".to_string());
    assert!(
        !minted.is_subtype_under(&Descr::int(), &inners),
        "K4 rule must not discharge the brand when the inner doesn't fit",
    );
}

#[test]
fn is_subtype_under_no_brand_inners_falls_back_to_strict() {
    // Empty brand_inners → no tag can be discharged. Behavior is
    // identical to the strict lattice.
    let inners = brand_inners(&[]);
    let mut minted = Descr::str_t();
    minted.brands = LiteralSet::lit("utf8".to_string());
    assert_eq!(
        minted.is_subtype(&Descr::str_t()),
        minted.is_subtype_under(&Descr::str_t(), &inners),
        "with no brand_inners the helper degenerates to is_subtype",
    );
}

#[test]
fn is_subtype_under_target_with_brand_restriction_still_works() {
    // utf8 ⊆ utf8: brand-aware lookup leaves the tag in place when
    // the target also restricts to that brand. Verifies the K4 rule
    // doesn't drop tags that the target still wants.
    let inners = brand_inners(&[("utf8", Descr::str_t())]);
    let mut minted = Descr::str_t();
    minted.brands = LiteralSet::lit("utf8".to_string());
    let mut target = Descr::str_t();
    target.brands = LiteralSet::lit("utf8".to_string());
    assert!(minted.is_subtype_under(&target, &inners));
    // And the inverse: a plain binary (brands=none) is NOT a utf8.
    assert!(!Descr::str_t().is_subtype_under(&target, &inners));
}

#[test]
fn brand_neg_excludes_only_that_brand() {
    let a = Descr::brand_of("utf8");
    let b = Descr::brand_of("ascii");
    let not_a = a.neg();
    assert!(!a.is_subtype(&not_a), "utf8 ⊄ ¬utf8");
    assert!(b.is_subtype(&not_a), "ascii ⊆ ¬utf8");
}

#[test]
fn two_distinct_opaques_do_not_overlap() {
    let pid = Descr::opaque_of("pid");
    let ts = Descr::opaque_of("timestamp");
    let i = pid.intersect(&ts);
    assert!(i.is_empty(), "pid ∩ timestamp should be empty: got {}", i);
}

#[test]
fn opaque_union_with_any_becomes_any() {
    let pid = Descr::opaque_of("pid");
    let u = pid.union(&Descr::any());
    assert!(u.looks_full(), "pid | any should be any: got {}", u);
}

// ------------------------------------------------------------------
// fz-try.5 — type-variable axis
// ------------------------------------------------------------------

#[test]
fn type_var_id_displays_as_alpha_indexed() {
    assert_eq!(format!("{}", TypeVarId(0)), "α0");
    assert_eq!(format!("{}", TypeVarId(7)), "α7");
    assert_eq!(format!("{:?}", TypeVarId(0)), "α0");
}

#[test]
fn type_var_id_fresh_yields_distinct_ids() {
    let a = TypeVarId::fresh();
    let b = TypeVarId::fresh();
    assert_ne!(a, b, "TypeVarId::fresh() must produce distinct ids");
}

#[test]
fn descr_var_round_trips_via_axis() {
    let v = Descr::var(TypeVarId(0));
    assert!(!v.is_empty(), "var(α0) should not be empty");
    assert!(!v.looks_full(), "var(α0) should not look full");
    // The only non-default axis is `vars` itself.
    assert!(v.basic.is_empty());
    assert!(v.atoms.is_none());
    assert!(v.ints.is_none());
    assert!(v.opaques.is_none());
    assert!(!v.vars.is_none(), "vars axis must carry the id");
}

#[test]
fn descr_var_renders_as_alpha_id() {
    let v = Descr::var(TypeVarId(3));
    assert_eq!(format!("{}", v), "α3");
}

#[test]
fn var_is_subtype_of_itself() {
    let a = Descr::var(TypeVarId(0));
    assert!(a.is_subtype(&a), "α should be a subtype of itself");
}

#[test]
fn distinct_vars_do_not_overlap() {
    let a = Descr::var(TypeVarId(0));
    let b = Descr::var(TypeVarId(1));
    let i = a.intersect(&b);
    assert!(i.is_empty(), "α0 ∩ α1 must be empty: got {}", i);
}

#[test]
fn same_var_intersection_preserves_var() {
    let a = Descr::var(TypeVarId(0));
    let i = a.intersect(&a);
    assert!(i.is_equiv(&a), "α0 ∩ α0 must equal α0: got {}", i);
}

#[test]
fn var_union_with_int_keeps_both() {
    let a = Descr::var(TypeVarId(0));
    let i = Descr::int();
    let u = a.union(&i);
    assert!(!u.is_empty());
    assert!(!u.vars.is_none(), "union must retain the type variable");
    assert!(u.ints.is_any(), "and the int axis must be saturated");
    // The union is the sum: members of α OR members of int.
    assert!(a.is_subtype(&u), "α ⊆ (α ∪ int)");
    assert!(i.is_subtype(&u), "int ⊆ (α ∪ int)");
}

#[test]
fn var_union_with_any_becomes_any() {
    let a = Descr::var(TypeVarId(0));
    let u = a.union(&Descr::any());
    assert!(u.looks_full(), "α ∪ any should be any: got {}", u);
}

#[test]
fn any_contains_all_vars() {
    // Descr::any() includes the entire vars axis (cofinite empty).
    let any = Descr::any();
    assert!(any.vars.is_any(), "Descr::any().vars must be the full universe");
    let a = Descr::var(TypeVarId(0));
    assert!(a.is_subtype(&any), "α ⊆ any");
}

#[test]
fn none_excludes_all_vars() {
    let none = Descr::none();
    assert!(none.vars.is_none(), "Descr::none().vars must be empty");
}

#[test]
fn var_neg_excludes_only_that_var() {
    // ¬α0 covers everything except α0. So α0 ⊄ ¬α0, but α1 ⊆ ¬α0.
    let a = Descr::var(TypeVarId(0));
    let b = Descr::var(TypeVarId(1));
    let not_a = a.neg();
    assert!(!a.is_subtype(&not_a), "α0 must not be a subtype of ¬α0");
    assert!(b.is_subtype(&not_a), "α1 ⊆ ¬α0 (different name)");
}

#[test]
fn var_is_not_opaque() {
    // Vars and opaques live in distinct axes — the lattice distinguishes
    // them structurally even though they share operational shape.
    let a = Descr::var(TypeVarId(0));
    let o = Descr::opaque_of("alpha");
    let i = a.intersect(&o);
    assert!(i.is_empty(), "α and opaque(\"alpha\") must not overlap");
}

// ------------------------------------------------------------------
// fz-try.6 — instantiation and σ-collection
// ------------------------------------------------------------------

fn sigma_of(bindings: &[(u32, Descr)]) -> HashMap<TypeVarId, Descr> {
    bindings.iter().map(|(id, d)| (TypeVarId(*id), d.clone())).collect()
}

#[test]
fn instantiate_preserves_lit_tag_on_arrow() {
    let lit = ClosureLit {
        kind: crate::types::CallableValueKind::Closure,
        fn_id: FnId(42),
        captures: vec![],
    };
    let arrow = Descr {
        funcs: vec![Conj::pos_of(ArrowSig {
            args: vec![Descr::var(TypeVarId(0))],
            ret: Box::new(Descr::int()),
            lit: Some(lit.clone()),
        })],
        ..Descr::none()
    };
    let result = arrow.instantiate(&sigma_of(&[(0, Descr::int())]));
    // The lit tag must survive the walk so closure-identity tracking
    // downstream still resolves to the same closure value.
    assert!(result.funcs[0].pos[0].lit.is_some());
    let preserved = result.funcs[0].pos[0].lit.as_ref().unwrap();
    assert_eq!(preserved.fn_id, lit.fn_id);
    assert_eq!(preserved.captures, lit.captures);
}

// ------------------------------------------------------------------
// fz-try.9 — algebra audit: type variables in every lattice operation
//
// Verifies that the structural lattice algebra (union, intersect, neg,
// diff, is_subtype) handles the `vars` axis correctly and composes
// with the other axes. The semantic "join law" from the design doc
// (Var ⊔ Var = Any, Var ⊔ Concrete = Concrete via substitution) is a
// distinct operation realized at substitution sites (instantiate),
// not in the structural union — see docs/descr-cleanup.md §Join law.
// ------------------------------------------------------------------

#[test]
fn algebra_audit_union_with_var_is_componentwise() {
    // Structural union: var ∪ int produces a Descr with both axes set.
    // (The design's "join with substitution" is operational and lives
    // at instantiate() — not here.)
    let a = Descr::var(TypeVarId(0));
    let u = a.union(&Descr::int());
    assert!(!u.vars.is_none(), "var axis must survive union");
    assert!(u.ints.is_any() || !u.ints.is_none(), "int axis must survive union");
    // Subtypes both witnesses.
    assert!(a.is_subtype(&u));
    assert!(Descr::int().is_subtype(&u));
}

#[test]
fn algebra_audit_union_distinct_vars_keeps_both() {
    let a = Descr::var(TypeVarId(0));
    let b = Descr::var(TypeVarId(1));
    let u = a.union(&b);
    // Both var ids are members of the union's `vars` axis.
    assert!(a.is_subtype(&u));
    assert!(b.is_subtype(&u));
}

#[test]
fn algebra_audit_intersect_preserves_var_disjointness() {
    // var(α) ∩ int = none — vars are nominally disjoint from concrete.
    let a = Descr::var(TypeVarId(0));
    let i = a.intersect(&Descr::int());
    assert!(i.is_empty(), "var ∩ int must be empty, got {}", i);
    // var(α) ∩ var(α) = var(α).
    let i2 = a.intersect(&a);
    assert!(i2.is_equiv(&a));
    // var(α) ∩ var(β) = none.
    let b = Descr::var(TypeVarId(1));
    let i3 = a.intersect(&b);
    assert!(i3.is_empty());
}

#[test]
fn algebra_audit_neg_complement_correct() {
    // ¬var(α) is the universe minus α. Its union with α is the universe.
    let a = Descr::var(TypeVarId(0));
    let nota = a.neg();
    let universe = a.union(&nota);
    assert!(
        universe.looks_full() || universe.is_equiv(&Descr::any()),
        "α ∪ ¬α must be the universe, got {}",
        universe
    );
    // α ∩ ¬α = none.
    let mt = a.intersect(&nota);
    assert!(mt.is_empty(), "α ∩ ¬α must be empty, got {}", mt);
}

#[test]
fn algebra_audit_diff_extracts_var_correctly() {
    // (α ∪ int) \ int = α (var portion remains; int portion removed).
    let mixed = Descr::var(TypeVarId(0)).union(&Descr::int());
    let just_var = mixed.diff(&Descr::int());
    assert!(
        just_var.is_equiv(&Descr::var(TypeVarId(0))),
        "(α ∪ int) \\ int should be α, got {}",
        just_var
    );
}

#[test]
fn algebra_audit_subtype_var_relationships() {
    let a = Descr::var(TypeVarId(0));
    let b = Descr::var(TypeVarId(1));
    // α ⊆ α
    assert!(a.is_subtype(&a));
    // α ⊆ any
    assert!(a.is_subtype(&Descr::any()));
    // none ⊆ α
    assert!(Descr::none().is_subtype(&a));
    // α ⊄ int (vars and ints are disjoint)
    assert!(!a.is_subtype(&Descr::int()));
    // int ⊄ α (same reason)
    assert!(!Descr::int().is_subtype(&a));
    // α ⊄ β (distinct vars, both nominal)
    assert!(!a.is_subtype(&b));
}

#[test]
fn algebra_audit_var_in_list_element() {
    // list(α) ⊆ list(any); list(α) ⊄ list(int).
    let la = Descr::list_of(Descr::var(TypeVarId(0)));
    let la_any = Descr::list_of(Descr::any());
    let la_int = Descr::list_of(Descr::int());
    assert!(la.is_subtype(&la_any), "list(α) ⊆ list(any)");
    assert!(!la.is_subtype(&la_int), "list(α) ⊄ list(int)");
}

#[test]
fn algebra_audit_instantiate_then_union_distributes() {
    // For any σ, instantiate(d1 ∪ d2, σ) ≡ instantiate(d1, σ) ∪
    // instantiate(d2, σ). Verified on a representative case.
    let d1 = Descr::var(TypeVarId(0));
    let d2 = Descr::var(TypeVarId(1));
    let sigma: HashMap<TypeVarId, Descr> = [(TypeVarId(0), Descr::int()), (TypeVarId(1), Descr::bool_t())]
        .into_iter()
        .collect();
    let lhs = d1.union(&d2).instantiate(&sigma);
    let rhs = d1.instantiate(&sigma).union(&d2.instantiate(&sigma));
    assert!(lhs.is_equiv(&rhs), "{} ≢ {}", lhs, rhs);
}

#[test]
fn algebra_audit_no_var_axis_pollution_in_concrete_round_trip() {
    // A Descr constructed without any var-axis manipulation must NOT
    // gain vars through any algebraic operation that doesn't introduce
    // them. Regression guard for accidental cross-axis bleed.
    let i = Descr::int();
    let s = Descr::str_t();
    let u = i.union(&s);
    assert!(u.vars.is_none(), "union of concrete descrs has no vars");
    let int_ = i.intersect(&s);
    assert!(int_.vars.is_none(), "intersect of concrete descrs has no vars");
    let n = i.neg();
    // ¬int has saturated vars (cofinite) — that's correct; "not int"
    // includes vars in the universe. But has_vars() reports false
    // because there are no NAMED ids.
    assert!(!n.has_vars(), "¬int has no named vars to substitute");
}

// ------------------------------------------------------------------
// fz-68x.2 — Component view API
// ------------------------------------------------------------------

fn count_components(d: &Descr) -> usize {
    d.components().count()
}

#[test]
fn components_none_yields_nothing() {
    assert_eq!(count_components(&Descr::none()), 0);
}

#[test]
fn components_any_yields_one_per_axis() {
    // 12 axes (fz-axu.22 deleted `strs`): basic, atoms, ints,
    // floats, opaques, brands, vars, tuples, lists, resources, funcs, maps.
    assert_eq!(count_components(&Descr::any()), 12);
}

#[test]
fn components_int_lit_yields_only_ints() {
    let d = Descr::int_lit(42);
    let mut found = None;
    for c in d.components() {
        match c {
            Component::Ints(v) => {
                assert!(found.is_none(), "multiple Ints components");
                found = v.singleton();
            }
            _ => panic!("unexpected component for int_lit(42)"),
        }
    }
    assert_eq!(found, Some(42));
}

#[test]
fn components_atom_lit_yields_only_atoms() {
    let d = Descr::atom_lit("ok");
    let mut seen_atom = false;
    for c in d.components() {
        match c {
            Component::Atoms(v) => {
                seen_atom = true;
                let names: Vec<&str> = v.finite().unwrap().collect();
                assert_eq!(names, vec!["ok"]);
            }
            _ => panic!("unexpected component for atom_lit"),
        }
    }
    assert!(seen_atom);
}

#[test]
fn components_tuple_of_yields_only_tuples_with_correct_arity_and_projection() {
    let d = Descr::tuple_of(vec![Descr::int_lit(1), Descr::int_lit(2)]);
    let mut seen = false;
    for c in d.components() {
        match c {
            Component::Tuples(v) => {
                seen = true;
                let arities: Vec<usize> = v.arities().collect();
                assert_eq!(arities, vec![2]);
                let elems = v.project_all(2).unwrap();
                assert_eq!(elems[0].as_int_singleton(), Some(1));
                assert_eq!(elems[1].as_int_singleton(), Some(2));
                // Out-of-band projections return None.
                assert!(v.project_all(3).is_none());
            }
            _ => panic!("unexpected component for tuple_of"),
        }
    }
    assert!(seen);
}

#[test]
fn components_list_of_yields_only_lists_with_joined_element_type() {
    let d = Descr::list_of(Descr::int());
    let mut seen = false;
    for c in d.components() {
        match c {
            Component::Lists(v) => {
                seen = true;
                let et = v.element_type();
                assert!(et.is_equiv(&Descr::int()));
            }
            _ => panic!("unexpected component for list_of"),
        }
    }
    assert!(seen);
}

#[test]
fn components_arrow_yields_funcs_and_exposes_args_ret() {
    let d = Descr::arrow(vec![Descr::int()], Descr::str_t());
    let mut seen = false;
    for c in d.components() {
        match c {
            Component::Funcs(v) => {
                seen = true;
                let arrows: Vec<_> = v.arrows().collect();
                assert_eq!(arrows.len(), 1);
                let a = arrows[0];
                assert_eq!(a.args().len(), 1);
                assert!(a.args()[0].is_equiv(&Descr::int()));
                assert!(a.ret().is_equiv(&Descr::str_t()));
                assert!(a.closure_lit().is_none());
            }
            _ => panic!("unexpected component for arrow"),
        }
    }
    assert!(seen);
}

#[test]
fn components_var_yields_only_vars_axis() {
    let d = Descr::var(TypeVarId(7));
    let mut seen = false;
    for c in d.components() {
        match c {
            Component::Vars(v) => {
                seen = true;
                let ids: Vec<TypeVarId> = v.finite().unwrap().collect();
                assert_eq!(ids, vec![TypeVarId(7)]);
            }
            _ => panic!("unexpected component for var"),
        }
    }
    assert!(seen);
}

#[test]
fn components_var_union_int_yields_both_axes() {
    // Pins the trajectory: vars and concrete coexist in a single Descr
    // (matches algebra_audit_union_int_var_keeps_both); both components
    // must surface independently.
    let d = Descr::var(TypeVarId(0)).union(&Descr::int());
    let mut saw_vars = false;
    let mut saw_ints = false;
    for c in d.components() {
        match c {
            Component::Vars(_) => saw_vars = true,
            Component::Ints(_) => saw_ints = true,
            _ => panic!("unexpected component for var ∪ int"),
        }
    }
    assert!(saw_vars && saw_ints);
}

#[test]
fn components_distinct_vars_collapse_to_one_vars_component() {
    // α ∪ β lives in a single vars-axis (finite set {α, β}). The
    // iterator yields ONE Component::Vars containing both ids — not
    // two separate var components.
    let d = Descr::var(TypeVarId(0)).union(&Descr::var(TypeVarId(1)));
    let mut count = 0;
    for c in d.components() {
        match c {
            Component::Vars(v) => {
                count += 1;
                let ids: Vec<TypeVarId> = v.finite().unwrap().collect();
                assert_eq!(ids, vec![TypeVarId(0), TypeVarId(1)]);
            }
            _ => panic!("unexpected component for var ∪ var"),
        }
    }
    assert_eq!(count, 1, "vars axis surfaces as exactly one component");
}

#[test]
fn components_binary_surfaces_as_basic_with_bits() {
    let d = Descr::str_t();
    let mut seen = false;
    for c in d.components() {
        match c {
            Component::Basic(bits) => {
                seen = true;
                assert!(bits.contains_all(BasicBits::BINARY));
            }
            _ => panic!("unexpected component for binary"),
        }
    }
    assert!(seen);
}

#[test]
fn components_map_field_lookup_joins_across_clauses() {
    // Single-clause map: open_map with one field. field() returns the value.
    let mut fields = BTreeMap::new();
    fields.insert(MapKey::Atom("k".into()), Descr::int_lit(1));
    let m = Descr::map_of(fields);
    for c in m.components() {
        if let Component::Maps(v) = c {
            let got = v.lookup(&MapKey::Atom("k".into()));
            assert_eq!(got.and_then(|d| d.as_int_singleton()), Some(1));
            // "missing" on an open_map is `any | nil`, not None.
            let missing = v.lookup(&MapKey::Atom("missing".into())).unwrap();
            assert!(Descr::nil().is_subtype(&missing));
        }
    }
}

#[test]
fn components_int_singleton_extraction_works() {
    // For wide int, singleton returns None.
    for c in Descr::int().components() {
        if let Component::Ints(v) = c {
            assert!(v.singleton().is_none());
        }
    }
    // For int_lit(42), singleton returns Some(42).
    for c in Descr::int_lit(42).components() {
        if let Component::Ints(v) = c {
            assert_eq!(v.singleton(), Some(42));
        }
    }
}
