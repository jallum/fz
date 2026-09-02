use std::collections::{BTreeMap, HashMap};
use std::mem;
use std::slice;

use super::*;
use crate::compiler2::keying::DispatchDemand;
use crate::finite_set::FiniteSet;
use crate::runtime_type_predicate::{ListShape, ListShapes, RuntimeTypePredicate};

#[test]
fn ty_is_an_integer_handle() {
    assert_eq!(mem::size_of::<Ty>(), mem::size_of::<u32>());
}

#[test]
fn factory_interns_equal_descriptors() {
    let mut t = Types::new();
    assert_eq!(t.int(), t.int());
    let a = t.int();
    let lhs = t.tuple(&[a]);
    let rhs = t.tuple(&[a]);
    assert_eq!(lhs, rhs);
}

#[test]
fn structural_children_are_interned_handles() {
    let mut t = Types::new();
    let elem = t.int();
    let tuple = t.tuple(&[elem]);
    let d = t.descr(&tuple);
    assert_eq!(d.tuples[0].pos[0].elems, vec![elem]);
}

// fz-hwn.27.5 — the backend-boundary value-template predicate.
//
// `is_value_template` is the calculator's authority on "can this position hold a
// runtime value?" An activation whose input is a value template cannot become a
// backend executable: the bare-variable value has no representation and
// materializes as `Absent`, panicking on use (the fz-hwn.23 phantom).
//
// These pins establish that the cheap SYNTACTIC predicate — bare var, or tuple
// with a bare-var field — is exactly the materializability boundary, so the
// semantic `mvar` groundness (Castagna; a var is meaningful iff `t[0/α] ≠ t`) is
// NOT needed. The reason: the only types whose runtime representation depends on
// an inner variable being ground are the two the predicate catches. Everything
// else has a representation independent of its inner vars — `list(α)` is a
// pointer, `(α)->α` is one word (fz-hwn.27.12) — so those inner vars are
// representation-irrelevant, exactly as `mvar` would conclude, but decided
// syntactically without an emptiness probe.
#[test]
fn value_template_predicate_flags_unrepresentable_positions_only() {
    let mut t = Types::new();
    let a = t.type_var(TypeVarId(0));
    let b = t.type_var(TypeVarId(1));
    let int = t.int();

    // A bare variable IS the whole value: no representation → template.
    assert!(t.is_value_template(&a), "a bare variable has no runtime representation");

    // A tuple with a bare-variable field cannot be laid out → template.
    let tuple_with_var = t.tuple(&[a, int]);
    assert!(
        t.is_value_template(&tuple_with_var),
        "a tuple with a bare-variable field cannot be laid out",
    );

    // Representable values — inner vars are representation-irrelevant (this is the
    // mvar boundary, decided syntactically). These must NOT be templates, or
    // genuine polymorphic values (lists, callables) would be wrongly pruned.
    let list_of_var = t.list(a); // a list is a pointer regardless of element type
    assert!(!t.is_value_template(&list_of_var), "list(α) is a representable pointer");

    let poly_callable = t.arrow(&[a], a); // (α)->α is one word — fz-hwn.27.12
    assert!(!t.is_value_template(&poly_callable), "(α)->α is one representable word");

    let tuple_of_representable = t.tuple(&[list_of_var, int]);
    assert!(
        !t.is_value_template(&tuple_of_representable),
        "a tuple of representable fields is representable",
    );

    // Ground values are never templates.
    assert!(!t.is_value_template(&int), "a ground scalar is representable");
    let ground_tuple = t.tuple(&[int, int]);
    assert!(!t.is_value_template(&ground_tuple), "a ground tuple is representable");

    // `key_is_value_template` lifts the predicate to an activation's input vector:
    // a key is unrepresentable iff ANY input position is a template. This is the
    // shape of the real fz-hwn.23 phantom — distinct bare-var inputs `(a0, a1)`.
    assert!(
        t.key_is_value_template(&[a, b]),
        "an activation with bare-variable inputs is the fz-hwn.23 phantom",
    );
    assert!(
        !t.key_is_value_template(&[list_of_var, int]),
        "an activation of representable inputs is a real backend executable",
    );
}

#[test]
fn repeated_subtype_comparisons_are_memoized_by_type_id() {
    let mut t = Types::new();
    let int = t.atom();
    let lit = t.atom_lit("ok");

    let before = t.comparison_cache_stats();
    assert!(t.is_subtype(&lit, &int));
    let after_first = t.comparison_cache_stats();
    assert_eq!(
        after_first.misses,
        before.misses + 1,
        "the first subtype comparison should compute and cache the answer"
    );
    assert_eq!(after_first.hits, before.hits);

    assert!(t.is_subtype(&lit, &int));
    let after_second = t.comparison_cache_stats();
    assert_eq!(
        after_second.misses, after_first.misses,
        "repeating the same id comparison should not rewalk structure"
    );
    assert_eq!(
        after_second.hits,
        after_first.hits + 1,
        "repeating the same id comparison should hit the cache"
    );
    assert_eq!(
        after_second.entries, after_first.entries,
        "a cache hit should not add another entry"
    );
}

#[test]
fn runtime_type_predicate_projects_integer_kind() {
    // Numbers are presence bits: the predicate is a kind check, never a
    // value-membership set, from this pipeline. Constants are compared as
    // values by the matcher.
    let mut t = Types::new();
    let forty_two = t.int_lit(42);
    let predicate = t.runtime_type_predicate(&forty_two);
    assert_eq!(
        predicate,
        RuntimeTypePredicate {
            ints: FiniteSet::any(),
            ..RuntimeTypePredicate::none()
        }
    );
}

/// Both structural axes project their contents: a tuple's positions, and a
/// list's HEAD.
///
/// Both used to erase them. `{:cont, int}` and `{:halt, int}` were one "a
/// 2-tuple" question until fz-kdt.119 gave the tuple axis one sub-predicate
/// per position per clause; `[int]` and `[:ok]` were one "a non-empty list"
/// question until fz-kdt.107 step 3 gave the list axis one head question per
/// cons-admitting clause. In both cases the coarse reading the other callers
/// want -- arities, shapes -- is still answerable beside the fine one.
///
/// The list half is a ONE-SIDED FILTER and this states both sides of it:
/// `[:false | :true]` against `[int]` is a real separation, because a head
/// outside the question proves the whole homogeneous list outside the surface;
/// `[int]` against `[int | :ok]` is NOT, because a head inside it says nothing
/// about the tail no test reads.
#[test]
fn runtime_type_predicate_projects_tuple_positions_and_list_heads() {
    let mut t = Types::new();
    let empty_list_ty = t.empty_list();
    let empty_list = t.runtime_type_predicate(&empty_list_ty);
    assert_eq!(
        empty_list,
        RuntimeTypePredicate {
            lists: ListShapes::exact(FiniteSet::lit(ListShape::Empty), Vec::new()),
            ..RuntimeTypePredicate::none()
        },
        "[] admits no cons cell, so it puts no head question",
    );

    let int = t.int();
    let atom = t.atom();
    let int_list = t.list(int);
    let atom_list = t.list(atom);
    assert_ne!(
        t.runtime_type_predicate(&int_list),
        t.runtime_type_predicate(&atom_list),
        "a list test reads the first element, so list(int) and list(atom) are two questions",
    );

    let false_atom = t.atom_lit("false");
    let true_atom = t.atom_lit("true");
    let ok_atom = t.atom_lit("ok");
    let bools = t.union(false_atom, true_atom);
    let bool_list = t.list(bools);
    let bools_ask = t.runtime_type_predicate(&bool_list);
    let ints_ask = t.runtime_type_predicate(&int_list);
    assert!(
        !bools_ask.overlaps_on_an_erasing_axis(&ints_ask),
        "[:false | :true] and [int] have DISJOINT heads, and disjoint heads are the one \
         separation a head load can claim",
    );

    assert!(
        ints_ask.lists.is_exact() && ints_ask.lists.heads().len() == 1,
        "one head question per cons-admitting clause, which is what keeps the clauses correlated",
    );

    let ints_oks = t.union(int, ok_atom);
    let mixed_list = t.list(ints_oks);
    let mixed_ask = t.runtime_type_predicate(&mixed_list);
    assert!(
        ints_ask.overlaps_on_an_erasing_axis(&mixed_ask),
        "[int] and [int | :ok] OVERLAP at the head and differ only in a tail no test reads, \
         so a seat may not claim separation there -- claiming it seats [int] first and hands \
         [1, :ok] to a body that reads every element as an int",
    );
    assert!(
        ints_ask.contained_in(&mixed_ask) && !mixed_ask.contained_in(&ints_ask),
        "and the narrower head is still the narrower test",
    );

    let tuple_ty = t.tuple(&[int, atom]);
    let tuple = t.runtime_type_predicate(&tuple_ty);
    assert_eq!(*tuple.tuples.arities(), FiniteSet::lit(2));
    assert!(tuple.tuples.is_exact());
    assert_eq!(
        tuple.tuples.shapes(),
        [vec![t.runtime_type_predicate(&int), t.runtime_type_predicate(&atom)]],
        "each position carries its own question",
    );

    let cont = t.atom_lit("cont");
    let halt = t.atom_lit("halt");
    let cont_int = t.tuple(&[cont, int]);
    let halt_int = t.tuple(&[halt, int]);
    let either = t.union(cont_int, halt_int);
    let either_predicate = t.runtime_type_predicate(&either);
    assert_eq!(
        either_predicate.tuples.shapes().len(),
        2,
        "a two-clause union is two shapes: joining them position-wise would admit {{:cont, _}} \
         and {{:halt, _}} crossed with each other's payloads",
    );
    assert!(
        !t.runtime_type_predicate(&cont_int)
            .overlaps(&t.runtime_type_predicate(&halt_int)),
        "and the tags separate, which is the whole point",
    );
}

#[test]
fn runtime_type_predicate_projects_named_structs_and_widens_unknown_opaques() {
    let mut t = Types::new();
    let named_ty = t.opaque_of("impl-target::box");
    let named = t.runtime_type_predicate(&named_ty);
    assert_eq!(
        named,
        RuntimeTypePredicate {
            named_structs: FiniteSet::lit("box".to_string()),
            ..RuntimeTypePredicate::none()
        }
    );

    let mystery = t.opaque_of("mystery");
    let widened = t.runtime_type_predicate(&mystery);
    assert_eq!(widened, RuntimeTypePredicate::any());
}

#[test]
fn runtime_type_predicate_keeps_named_struct_identity_out_of_plain_map_kind() {
    let mut t = Types::new();
    let named = t.opaque_of("impl-target::Range");
    let any = t.any();
    let tuple = t.tuple(&[any, any, any]);
    let first = t.atom_lit("first");
    let last = t.atom_lit("last");
    let step = t.atom_lit("step");
    let structural_map = t.map(&[
        (MapKey::Atom("first".to_string()), first),
        (MapKey::Atom("last".to_string()), last),
        (MapKey::Atom("step".to_string()), step),
    ]);
    let structural = t.union(tuple, structural_map);
    let range_value = t.union(named, structural);
    let range_predicate = t.runtime_type_predicate(&range_value);
    let map_top = t.map_top();
    let map_predicate = t.runtime_type_predicate(&map_top);

    assert_eq!(
        range_predicate.named_structs,
        FiniteSet::lit("Range".to_string()),
        "a struct value should keep its named runtime identity even though it also has structural field evidence",
    );
    assert!(
        !range_predicate.maps,
        "a named struct's structural map evidence must not make it a plain runtime map predicate",
    );
    assert!(
        !range_predicate.overlaps(&map_predicate),
        "protocol matching must not select the Map implementation for a Range struct value",
    );
}

#[test]
fn symmetric_comparisons_share_one_cache_entry() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();

    let before = t.comparison_cache_stats();
    assert!(t.is_disjoint(&int, &atom));
    let after_first = t.comparison_cache_stats();
    assert_eq!(after_first.misses, before.misses + 1);

    assert!(t.is_disjoint(&atom, &int));
    let after_second = t.comparison_cache_stats();
    assert_eq!(
        after_second.misses, after_first.misses,
        "the reversed disjointness query should reuse the symmetric comparison"
    );
    assert_eq!(after_second.hits, after_first.hits + 1);
}

macro_rules! key_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn key_var_count_counts_top_level_vars() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let int_top = t.int();
                let mixed = t.union(int_top, beta);
                assert_eq!(t.key_var_count(&[alpha, mixed]), 2);
            }

            #[test]
            fn key_subsumes_with_binds_pure_vars() {
                let mut t = $ctor;
                let mut sigma = HashMap::new();
                let int = t.int();
                let alpha = t.type_var(TypeVarId(0));
                assert!(t.key_subsumes_with(&int, &alpha, &mut sigma));
                assert_eq!(sigma.get(&TypeVarId(0)), Some(&int));
            }

            #[test]
            fn key_list_subsumes_threads_one_substitution_across_positions() {
                let mut t = $ctor;
                let int = t.int();
                let atom = t.atom();
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));

                // Distinct template vars are instantiated by any ground pair.
                assert!(t.key_list_subsumes(&[int, atom], &[alpha, beta]));
                // A recurring template var binds once and must agree everywhere:
                // `[α, α]` is instantiated only when both positions match.
                assert!(t.key_list_subsumes(&[int, int], &[alpha, alpha]));
                assert!(
                    !t.key_list_subsumes(&[int, atom], &[alpha, alpha]),
                    "a recurring template var must not accept disagreeing positions",
                );
                // A ground template names one runtime shape — only itself instantiates it.
                assert!(t.key_list_subsumes(&[int, atom], &[int, atom]));
                assert!(!t.key_list_subsumes(&[atom, int], &[int, atom]));
                // Arity must match.
                assert!(!t.key_list_subsumes(&[int], &[alpha, beta]));
            }

            #[test]
            fn key_has_vars_distinguishes_ground_lists_from_templates() {
                let mut t = $ctor;
                let int = t.int();
                let atom = t.atom();
                let alpha = t.type_var(TypeVarId(0));
                assert!(!t.key_has_vars(&[int, atom]));
                assert!(t.key_has_vars(&[int, alpha]));
            }

            #[test]
            fn key_subsumes_with_leaves_sigma_empty_for_non_pure_var_keys() {
                let mut t = $ctor;
                let mut sigma = HashMap::new();
                let int = t.int();
                let alpha = t.type_var(TypeVarId(0));
                let int_top = t.int();
                let union_key = t.union(int_top, alpha);
                assert!(t.key_subsumes_with(&int, &union_key, &mut sigma));
                assert!(sigma.is_empty());
            }

            #[test]
            fn key_is_strictly_more_specific_recognizes_strict_subtype_keys() {
                let mut t = $ctor;
                let atom = t.atom();
                let atom_lit = t.atom_lit("ok");
                assert!(t.key_is_strictly_more_specific(slice::from_ref(&atom_lit), slice::from_ref(&atom)));
                assert!(!t.key_is_strictly_more_specific(slice::from_ref(&atom), slice::from_ref(&atom_lit)));
            }

            #[test]
            fn default_bool_lit_uses_reserved_atom_literals() {
                let mut t = $ctor;
                let true_lit = t.bool_lit(true);
                let false_lit = t.bool_lit(false);
                assert_eq!(t.as_atom_singleton(&true_lit).as_deref(), Some("true"));
                assert_eq!(t.as_atom_singleton(&false_lit).as_deref(), Some("false"));
            }

            #[test]
            fn default_cpointer_is_builtin_opaque() {
                let mut t = $ctor;
                let ptr = t.cpointer();
                assert_eq!(t.opaque_singleton(&ptr).as_deref(), Some("cpointer"));
            }

            #[test]
            fn default_is_equivalent_recognizes_mutual_subtypes() {
                let mut t = $ctor;
                let true_lit = t.bool_lit(true);
                let false_lit = t.bool_lit(false);
                let bool_union = t.union(true_lit, false_lit);
                let bool_t = t.bool();
                assert!(t.is_equivalent(&bool_union, &bool_t));
            }
        }
    };
}

macro_rules! seam_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn list_element_type_projects_list_axis() {
                let mut t = $ctor;
                let elem = t.int();
                let list = t.list(elem.clone());
                let projected = t.list_element_type(&list);
                assert!(t.is_equivalent(&projected, &elem));
            }

            #[test]
            fn list_element_type_defaults_to_any_without_list_axis() {
                let mut t = $ctor;
                let int = t.int();
                let projected = t.list_element_type(&int);
                assert!(t.is_top(&projected));
            }

            #[test]
            fn has_list_shape_distinguishes_list_axis_from_runtime_projection_fallback() {
                let mut t = $ctor;
                let int = t.int();
                let list = t.list(int.clone());
                assert!(t.has_list_shape(&list));
                assert!(!t.has_list_shape(&int));
            }

            #[test]
            fn list_element_type_projects_empty_list_as_none() {
                let mut t = $ctor;
                let empty = t.empty_list();
                let projected = t.list_element_type(&empty);
                assert!(t.is_empty(&projected));
            }

            #[test]
            fn list_element_type_of_an_unconstrained_list_is_any() {
                // `any`'s list fragment is the unconstrained conjunction: a
                // value flowing here may be ANY cons cell, so its head is
                // `any` — never the empty type. Conflating "unconstrained"
                // with "exact empty list" manufactured `none` heads under a
                // root's earned-any inputs and dead-dropped live calls.
                let mut t = $ctor;
                let any = t.any();
                let projected = t.list_element_type(&any);
                assert!(t.is_top(&projected));
            }

            #[test]
            fn tuple_projections_fall_back_to_any() {
                let mut t = $ctor;
                let int = t.int();
                let comps = t.tuple_projections(&int, 2);
                assert_eq!(comps.len(), 2);
                assert!(comps.iter().all(|ty| t.is_top(ty)));
            }

            #[test]
            fn value_lane_repr_collapses_every_list_shape_to_one_lane() {
                // A `Value` lane is one boxed reference word: a list's
                // empty/non-empty refinement and element type do not change its
                // representation. So a clause returning a narrow `[int]` and a
                // function whose joined return is `[int] | []` must share one
                // lane, or destination-passing can't fold the result.
                let mut t = $ctor;
                let int = t.int();
                let non_empty = t.non_empty_list(int.clone()); // [int]
                let proper = t.list(int.clone()); // [int] | []
                let empty = t.empty_list(); // []
                let float = t.float();
                let float_list = t.list(float);

                let canon = t.value_lane_repr(non_empty);
                assert_eq!(t.value_lane_repr(proper), canon, "[int] and [int]|[] share a lane");
                assert_eq!(t.value_lane_repr(empty), canon, "[] shares the list lane");
                assert_eq!(t.value_lane_repr(float_list), canon, "element type does not split the lane");

                // Non-list values keep their own representation.
                assert_eq!(t.value_lane_repr(int), int, "a scalar is its own lane");
            }

            #[test]
            fn value_lane_repr_collapses_every_callable_to_one_lane() {
                // A callable value is one word — a code pointer or a closure ref —
                // regardless of signature, arity, identity, or captures. So every
                // callable shares one `Value` lane, exactly as every list does.
                // This is what keeps an opaque join of same-signature functions
                // (`add_a | add_b`) from splitting across lanes (fz-hwn.27.12).
                let mut t = $ctor;
                let int = t.int();
                let a0 = t.type_var(TypeVarId(0));
                let a1 = t.type_var(TypeVarId(1));

                let unary = t.arrow(&[int], int); // (int) -> int
                let binary = t.arrow(&[int, int], int); // (int, int) -> int
                let poly = t.arrow(&[a0, a1], a0); // (a0, a1) -> a0
                let join = t.union(unary, binary); // (int)->int | (int,int)->int

                let canon = t.value_lane_repr(unary);
                assert_eq!(t.value_lane_repr(binary), canon, "arity does not split the callable lane");
                assert_eq!(t.value_lane_repr(poly), canon, "signature/vars do not split the lane");
                assert_eq!(t.value_lane_repr(join), canon, "an opaque join shares the one callable lane");

                // A callable lane is its own class, distinct from a scalar.
                assert_ne!(canon, t.value_lane_repr(int), "callables do not share the scalar lane");
            }

            #[test]
            fn tuple_projections_project_tuple_shape() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let ok = t.atom_lit("ok");
                let tuple = t.tuple(&[one.clone(), ok.clone()]);
                let comps = t.tuple_projections(&tuple, 2);
                assert_eq!(comps, vec![one, ok]);
            }

            #[test]
            fn map_field_lookup_returns_known_field_type() {
                let mut t = $ctor;
                let forty_two = t.int_lit(42);
                let map = t.map(&[(MapKey::Atom("ok".to_string()), forty_two.clone())]);
                let field = t
                    .map_field_lookup(&map, &MapKey::Atom("ok".to_string()))
                    .expect("known field");
                assert!(t.is_equivalent(&field, &forty_two));
            }

            #[test]
            fn refine_map_field_overlays_field_type() {
                let mut t = $ctor;
                let map = t.map_top();
                let value = t.int_lit(7);
                let refined = t.refine_map_field(&map, &MapKey::Atom("n".to_string()), &value);
                let field = t
                    .map_field_lookup(&refined, &MapKey::Atom("n".to_string()))
                    .expect("refined field");
                assert!(t.is_subtype(&value, &field));
                assert!(!t.is_empty(&field));
            }

            #[test]
            fn as_map_key_recognizes_atom_singletons_only() {
                // Int keys ride the lowering as values (LoweredMapKey); the
                // lattice holds no numeric singletons to project.
                let mut t = $ctor;
                let ok = t.atom_lit("ok");
                let seven = t.int_lit(7);
                let wide = t.atom();
                assert!(matches!(
                    t.as_map_key(&ok),
                    Some(MapKey::Atom(name)) if name == "ok"
                ));
                assert!(t.as_map_key(&seven).is_none());
                assert!(t.as_map_key(&wide).is_none());
            }

        }
    };
}

macro_rules! semantic_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            fn sigma_of<T>(bindings: impl IntoIterator<Item = (u32, T)>) -> Sigma<T> {
                bindings.into_iter().map(|(id, ty)| (TypeVarId(id), ty)).collect()
            }

            #[test]
            fn arrow_join_return_union_of_clauses() {
                let mut t = $ctor;
                let int_arg = t.int();
                let int_ret = t.int();
                let int_arrow = t.arrow(&[int_arg], int_ret);
                let str_arg = t.str_t();
                let bool_ret = t.bool();
                let bool_arrow = t.arrow(&[str_arg], bool_ret.clone());
                let callable = t.union(int_arrow, bool_arrow);
                let got = t.arrow_join_return(&callable);
                let int = t.int();
                let want = t.union(int, bool_ret);
                assert!(t.is_equivalent(&got, &want));
            }

            #[test]
            fn arrow_join_return_top_is_any() {
                let mut t = $ctor;
                let any = t.any();
                let got = t.arrow_join_return(&any);
                assert!(t.is_top(&got));
            }

            #[test]
            fn arrow_join_return_empty_is_any() {
                let mut t = $ctor;
                let int = t.int();
                let got = t.arrow_join_return(&int);
                assert!(t.is_top(&got));
            }

            #[test]
            fn value_disjoint_erases_embedded_brand_correctly() {
                // mint_brand embeds the inner's structural axes; erasing the brand
                // just clears the brands field — no external map needed.
                let mut t = $ctor;
                let str_inner = t.str_t();
                let int = t.int();
                let utf8 = t.mint_brand(str_inner, "utf8");
                let plain = t.str_t();
                // utf8 and int are structurally different runtime kinds — value-disjoint.
                assert!(t.is_value_disjoint(&utf8, &int));
                // utf8 and plain binary share the same runtime kind after erasing brands — NOT value-disjoint.
                assert!(!t.is_value_disjoint(&utf8, &plain));
            }

            #[test]
            fn has_vars_distinguishes_concrete_from_polymorphic() {
                let mut t = $ctor;
                let int = t.int();
                let any = t.any();
                let var = t.type_var(TypeVarId(0));
                assert!(!t.has_vars(&int));
                assert!(!t.has_vars(&any));
                assert!(t.has_vars(&var));
            }

            #[test]
            fn instantiate_replaces_top_level_var() {
                let mut t = $ctor;
                let pattern = t.type_var(TypeVarId(0));
                let int = t.int();
                let sigma = sigma_of([(0, int.clone())]);
                let result = t.instantiate(&pattern, &sigma);
                assert!(t.is_equivalent(&result, &int));
            }

            #[test]
            fn instantiate_is_identity_when_no_vars_match() {
                let mut t = $ctor;
                let pattern = t.type_var(TypeVarId(0));
                let int = t.int();
                let sigma = sigma_of([(1, int)]);
                let result = t.instantiate(&pattern, &sigma);
                assert!(t.is_equivalent(&result, &pattern));
            }

            #[test]
            fn instantiate_walks_into_lists() {
                let mut t = $ctor;
                let var = t.type_var(TypeVarId(0));
                let list_of_var = t.list(var);
                let int = t.int();
                let sigma = sigma_of([(0, int.clone())]);
                let result = t.instantiate(&list_of_var, &sigma);
                let list_of_int = t.list(int);
                assert!(t.is_equivalent(&result, &list_of_int));
            }

            #[test]
            fn instantiate_walks_into_tuples() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let tuple = t.tuple(&[alpha, beta]);
                let int = t.int();
                let str_t = t.str_t();
                let sigma = sigma_of([(0, int.clone()), (1, str_t.clone())]);
                let result = t.instantiate(&tuple, &sigma);
                let expected = t.tuple(&[int, str_t]);
                assert!(t.is_equivalent(&result, &expected));
            }

            #[test]
            fn instantiate_walks_into_arrow_args_and_ret() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let arrow = t.arrow(&[alpha], beta);
                let int = t.int();
                let bool_t = t.bool();
                let sigma = sigma_of([(0, int.clone()), (1, bool_t.clone())]);
                let result = t.instantiate(&arrow, &sigma);
                let expected = t.arrow(&[int], bool_t);
                assert!(t.is_equivalent(&result, &expected));
            }

            #[test]
            fn collect_subst_binds_top_level_var_to_witness() {
                let mut t = $ctor;
                let pattern = t.type_var(TypeVarId(0));
                let witness = t.int();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&pattern, &witness, &mut sigma);
                assert_eq!(sigma.len(), 1);
                assert!(t.is_equivalent(&sigma[&TypeVarId(0)], &witness));
            }

            #[test]
            fn collect_subst_is_noop_on_concrete_pattern() {
                let mut t = $ctor;
                let pattern = t.int();
                let witness = t.int();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&pattern, &witness, &mut sigma);
                assert!(sigma.is_empty());
            }

            #[test]
            fn collect_subst_then_instantiate_is_identity_on_concrete_args() {
                let mut t = $ctor;
                let pat_arg = t.type_var(TypeVarId(0));
                let pat_ret = t.type_var(TypeVarId(0));
                let witness = t.int();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&pat_arg, &witness, &mut sigma);
                let resolved_ret = t.instantiate(&pat_ret, &sigma);
                assert!(t.is_equivalent(&resolved_ret, &witness));
            }

            #[test]
            fn collect_subst_distinct_vars_bind_independently() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let int = t.int();
                let bool_t = t.bool();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&alpha, &int, &mut sigma);
                t.collect_instantiation_subst(&beta, &bool_t, &mut sigma);
                assert_eq!(sigma.len(), 2);
                assert!(t.is_equivalent(&sigma[&TypeVarId(0)], &int));
                assert!(t.is_equivalent(&sigma[&TypeVarId(1)], &bool_t));
            }

            #[test]
            fn tuple_field_projection_skips_impossible_mixed_arity_conjunctions() {
                let mut t = $ctor;
                let done_tuple = {
                    let tag = t.atom_lit("done");
                    let payload = t.int();
                    t.tuple(&[tag, payload])
                };
                let halted_tuple = {
                    let tag = t.atom_lit("halted");
                    let payload = t.int();
                    t.tuple(&[tag, payload])
                };
                let suspended_tuple = {
                    let tag = t.atom_lit("suspended");
                    let payload = t.int();
                    let continuation = t.int();
                    t.tuple(&[tag, payload, continuation])
                };
                let outcomes = {
                    let two = t.union(done_tuple, halted_tuple);
                    t.union(two, suspended_tuple)
                };
                let two_tuple = {
                    let a = t.any();
                    let b = t.any();
                    t.tuple(&[a, b])
                };
                let narrowed = t.intersect(outcomes, two_tuple);
                let first = t.tuple_field_type(&narrowed, 0);
                let expected = {
                    let done = t.atom_lit("done");
                    let halted = t.atom_lit("halted");
                    t.union(done, halted)
                };
                assert!(
                    t.is_equivalent(&first, &expected),
                    "projecting a 2-tuple narrowing must ignore impossible 3-tuple conjunctions, got {}",
                    t.display(&first)
                );
            }

            #[test]
            fn refine_widen_collapses_int_literals_to_int() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let int = t.int();
                let w_lits = t.refine_widen(&one, &two);
                let w_lit_base = t.refine_widen(&one, &int);
                let w_base = t.refine_widen(&int, &int);
                assert!(t.is_equivalent(&w_lits, &int));
                assert!(t.is_equivalent(&w_lit_base, &int));
                assert!(t.is_equivalent(&w_base, &int));
            }

            #[test]
            fn refine_widen_keeps_mismatched_callable_identities_apart() {
                // Pairwise arrow-merging is an economy, not a law: it is
                // only valid when the two clauses describe the same callable
                // value. Distinct fn refs flowing into one slot (a case that
                // yields add_a on one arm and add_b on the other) must
                // survive as two identity-bearing clauses, or downstream
                // closure callsites become unresolvable opaque callables.
                let mut t = $ctor;
                let a = t.fn_ref_lit(ClosureTarget(11), 2);
                let b = t.fn_ref_lit(ClosureTarget(12), 2);
                let w = t.refine_widen(&a, &b);
                let union = t.union(a, b);
                assert!(
                    t.is_equivalent(&w, &union),
                    "mismatched closure lits widen to their union, got {}",
                    t.display(&w)
                );
            }

            #[test]
            fn refine_widen_collapses_float_literals_to_float() {
                let mut t = $ctor;
                let a = t.float_lit(1.0);
                let b = t.float_lit(2.0);
                let float = t.float();
                let w = t.refine_widen(&a, &b);
                assert!(t.is_equivalent(&w, &float));
            }

            #[test]
            fn refine_widen_recurses_into_list_elements() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let int = t.int();
                let l1 = t.list(one);
                let l2 = t.list(two);
                let lint = t.list(int);
                let w = t.refine_widen(&l1, &l2);
                assert!(t.is_equivalent(&w, &lint));
            }

            #[test]
            fn refine_widen_merges_empty_and_non_empty_list_shapes() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let non_empty = t.non_empty_list(int.clone());
                let expected = t.list(int);
                let widened = t.refine_widen(&empty, &non_empty);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn union_keeps_normalized_list_evidence_when_rejoined_with_empty_list() {
                let mut t = $ctor;
                let elem = t.type_var(TypeVarId(0));
                let empty = t.empty_list();
                let non_empty = t.non_empty_list(elem);
                let proper = t.union(empty.clone(), non_empty);
                let rejoined = t.union(proper.clone(), empty.clone());

                assert!(
                    t.is_equivalent(&rejoined, &proper),
                    "rejoining {} with {} lowered or widened the list evidence to {}",
                    t.display(&proper),
                    t.display(&empty),
                    t.display(&rejoined)
                );
                assert!(
                    !t.is_equivalent(&rejoined, &empty),
                    "rejoining normalized list evidence collapsed to exact empty list"
                );

                let predicate = t.runtime_type_predicate(&rejoined);
                assert_eq!(
                    *predicate.lists.shapes(),
                    FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty])
                );
            }

            #[test]
            fn convergence_class_unifies_all_list_shapes_but_separates_other_families() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let nonempty = t.non_empty_list(int.clone());
                let list = t.list(int.clone());
                let empty_class = t.convergence_class(&empty);
                let nonempty_class = t.convergence_class(&nonempty);
                let list_class = t.convergence_class(&list);
                assert!(t.is_equivalent(&empty_class, &nonempty_class));
                assert!(t.is_equivalent(&nonempty_class, &list_class));
                let joined = t.union(empty, nonempty);
                let joined_class = t.convergence_class(&joined);
                assert!(
                    t.is_equivalent(&joined_class, &list_class),
                    "empty | non-empty list unions should share the recursive list convergence class"
                );

                let tagged = t.tuple(&[int.clone(), int.clone()]);
                let tagged_class = t.convergence_class(&tagged);
                assert!(!t.is_equivalent(&tagged_class, &list_class));

                let int_class = t.convergence_class(&int);
                assert!(!t.is_equivalent(&int_class, &list_class));
            }

            #[test]
            fn convergence_class_collapses_nested_list_and_callable_runtime_detail() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let nonempty = t.non_empty_list(int.clone());
                let cont = t.atom_lit("cont");
                let halt = t.atom_lit("halt");
                let callable_a = t.arrow(std::slice::from_ref(&int), cont);
                let callable_b = t.arrow(std::slice::from_ref(&int), halt);
                let tuple_a = t.tuple(&[empty, callable_a]);
                let tuple_b = t.tuple(&[nonempty, callable_b]);

                let class_a = t.convergence_class(&tuple_a);
                let class_b = t.convergence_class(&tuple_b);

                assert!(
                    t.is_equivalent(&class_a, &class_b),
                    "ignored recursive tuple slots should collapse nested list/callable detail while preserving tuple family"
                );
            }

            #[test]
            fn convergence_collapse_widens_only_non_dispatch_slots_of_the_arrow() {
                // The dispatch KEY of a recursive activation is a whole-arrow
                // collapse of its precise evidence arrow (fz-hwn.27.7): a
                // non-dispatch list slot widens to its ADDRESSED convergence
                // class so the recursive ascent settles, while dispatch slots and
                // the result are preserved exactly. Here slot 0 dispatches and
                // slot 1 does not, so slot 1's `list(int)` collapses to
                // `list(a1_e)` — a resolvable element address var at the slot's
                // structural address, not the path-blind `list(any)`
                // (fz-f98.14.10.2). Breadth is still one address per position so
                // fz-y6w termination holds.
                let mut t = $ctor;
                let int = t.int();
                let list_int = t.list(int.clone());
                let arrow = t.arrow(&[list_int.clone(), list_int.clone()], int.clone());
                let collapsed = t.convergence_collapse(arrow, &[DispatchDemand::Whole, DispatchDemand::Ignore]);

                let params = t.arrow_params(&collapsed);
                let ret = t.arrow_join_return(&collapsed);
                assert_eq!(t.display(&params[0]), "[int]");
                assert_eq!(t.display(&params[1]), "[a1_e]");
                assert_eq!(t.display(&ret), "int");
            }

            #[test]
            fn convergence_collapse_list_shape_keeps_element_but_not_recursive_list_shape() {
                let mut t = $ctor;
                let int = t.int();
                let non_empty = t.non_empty_list(int.clone());
                let list_int = t.list(int);
                let joined_list_family = t.union(list_int, non_empty);
                let sentinel = t.none();
                let arrow = t.arrow(&[joined_list_family], sentinel.clone());
                let collapsed = t.convergence_collapse(
                    arrow,
                    &[DispatchDemand::ListShape(Box::new(DispatchDemand::Whole))],
                );

                let expected = t.arrow(&[list_int], sentinel);
                assert!(
                    t.is_equivalent(&collapsed, &expected),
                    "recursive list-shape dispatch should converge joined list-family shape while preserving demanded element type"
                );
            }

            #[test]
            fn convergence_collapse_preserves_nested_dispatch_field_and_collapses_payload() {
                let mut t = $ctor;
                let elem = t.type_var(TypeVarId(0));
                let payload = t.list(elem);
                let tag = t.atom_lit("cont");
                let state = t.tuple(&[tag, payload]);
                let sentinel = t.none();
                let arrow = t.arrow(&[state], sentinel);
                let mut fields = BTreeMap::new();
                fields.insert(0, DispatchDemand::Whole);
                let collapsed = t.convergence_collapse(arrow, &[DispatchDemand::TupleFields(fields)]);

                // The dispatch tag (field 0) is preserved exactly; the ignored
                // payload (field 1) collapses to its ADDRESSED class — the list
                // element addressed at `[Param(0), Field(1), Elem]`, displayed
                // `a0_1_e` — not the path-blind `list(any)` (fz-f98.14.10.2).
                let params = t.arrow_params(&collapsed);
                assert_eq!(
                    t.display(&params[0]),
                    "{:cont, [a0_1_e]}",
                    "nested dispatch demand should preserve the tag and collapse the payload to its addressed class: {}",
                    t.display(&collapsed)
                );
                let _ = sentinel;
            }

            #[test]
            fn convergence_collapse_tuple_union_arrow_roundtrips_through_address_inputs() {
                // A multi-alternative tagged union slot collapsed by the recursive
                // dispatch-key mint MUST round-trip through `address_inputs` (the
                // canonical addresser, fz-hwn.27): the collapsed arrow is already
                // canonically addressed, so re-addressing it is the identity. This
                // fails if `convergence_collapse` omits the per-variant `Variant(k)`
                // discriminator that `address_inputs` inserts when alternatives > 1
                // (fz-go4.18.3.2.1).
                let mut t = $ctor;
                let elem = t.type_var(TypeVarId(0));
                let payload = t.list(elem); // [T]
                let cont = {
                    let tag = t.atom_lit("cont");
                    t.tuple(&[tag, payload])
                };
                let halt = {
                    let tag = t.atom_lit("halt");
                    t.tuple(&[tag, payload])
                };
                let union = t.union(cont, halt); // {:cont,[T]} | {:halt,[T]}
                let sentinel = t.none();
                let arrow = t.arrow(&[union], sentinel);
                let mut fields = BTreeMap::new();
                fields.insert(0, DispatchDemand::Whole); // tag dispatches, payload ignored
                let collapsed = t.convergence_collapse(arrow, &[DispatchDemand::TupleFields(fields)]);

                let params = t.arrow_params(&collapsed);
                let readdressed = t.address_inputs(&params);
                assert_eq!(
                    readdressed, params,
                    "collapsed union slot must be canonically addressed (round-trip): {} vs {}",
                    t.display(&readdressed[0]),
                    t.display(&params[0]),
                );
            }

            #[test]
            fn evidence_collapse_only_widens_variable_non_dispatch_payloads() {
                let mut t = $ctor;
                let int = t.int();
                let concrete = t.list(int.clone());
                let var = t.type_var(TypeVarId(0));
                let variable = t.list(var);
                let collapsed = t.convergence_collapse_evidence_inputs(
                    &[concrete, variable],
                    &[DispatchDemand::Ignore, DispatchDemand::Ignore],
                );

                let any = t.any();
                let list_any = t.list(any);
                assert!(
                    t.is_equivalent(&collapsed[0], &concrete),
                    "concrete non-dispatch evidence should stay precise"
                );
                assert!(
                    t.is_equivalent(&collapsed[1], &list_any),
                    "variable non-dispatch evidence should converge to list(any)"
                );
            }

            #[test]
            fn refine_widen_recurses_into_tuple_fields() {
                let mut t = $ctor;
                let empty = t.empty_list();
                let int = t.int();
                let non_empty = t.non_empty_list(int.clone());
                let two = t.int_lit(2);
                let one = t.int_lit(1);
                let lhs = t.tuple(&[empty, two]);
                let rhs = t.tuple(&[non_empty, one]);
                let list_int = t.list(int.clone());
                let expected = t.tuple(&[list_int, int]);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_recurses_into_resource_payloads() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let int = t.int();
                let lhs = t.resource(one);
                let rhs = t.resource(two);
                let expected = t.resource(int);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_recurses_into_arrow_returns_and_unions_args() {
                let mut t = $ctor;
                let int = t.int();
                let float = t.float();
                let empty = t.empty_list();
                let one = t.int_lit(1);
                let lhs_ret = t.tuple(&[empty, one]);
                let lhs = t.arrow(slice::from_ref(&int), lhs_ret);
                let non_empty = t.non_empty_list(int.clone());
                let two = t.int_lit(2);
                let rhs_ret = t.tuple(&[non_empty, two]);
                let rhs = t.arrow(slice::from_ref(&float), rhs_ret);
                let union = t.union(int.clone(), float);
                let list_int = t.list(int.clone());
                let ret = t.tuple(&[list_int, int]);
                let expected = t.arrow(&[union], ret);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_recurses_into_map_fields() {
                let mut t = $ctor;
                let key = MapKey::Atom("value".to_string());
                let int = t.int();
                let empty = t.empty_list();
                let one = t.int_lit(1);
                let lhs_value = t.tuple(&[empty, one]);
                let lhs = t.map(&[(key.clone(), lhs_value)]);
                let non_empty = t.non_empty_list(int.clone());
                let two = t.int_lit(2);
                let rhs_value = t.tuple(&[non_empty, two]);
                let rhs = t.map(&[(key.clone(), rhs_value)]);
                let list_int = t.list(int.clone());
                let expected_value = t.tuple(&[list_int, int]);
                let expected = t.map(&[(key, expected_value)]);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_falls_back_to_union_for_incompatible_fields_monotonically() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let tuple = t.tuple(&[empty.clone(), int.clone()]);
                let prev = t.union(int, tuple.clone());
                let observed = tuple;
                let widened = t.refine_widen(&prev, &observed);
                assert!(t.is_subtype(&prev, &widened));
                assert!(t.is_subtype(&observed, &widened));
            }

            #[test]
            fn refine_widen_keeps_int_and_float_apart_no_number_rung() {
                let mut t = $ctor;
                let i = t.int_lit(1);
                let f = t.float_lit(2.0);
                let int = t.int();
                let float = t.float();
                let union = t.union(int, float);
                let any = t.any();
                let widened = t.refine_widen(&i, &f);
                assert!(t.is_equivalent(&widened, &union));
                assert!(!t.is_equivalent(&widened, &any));
            }

            #[test]
            fn refine_widen_any_absorbs() {
                let mut t = $ctor;
                let int = t.int();
                let any = t.any();
                let widened = t.refine_widen(&int, &any);
                assert!(t.is_equivalent(&widened, &any));
            }

            #[test]
            fn widen_for_recursive_spec_key_preserves_list_element_shape() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let elems = t.union(one, two);
                let list = t.non_empty_list(elems);
                let widened = t.widen_for_recursive_spec_key(&list);
                let int = t.int();
                let expected = t.non_empty_list(int);
                assert!(
                    t.is_equivalent(&widened, &expected),
                    "recursive-spec widening should keep the list axis while widening element literals, got {}",
                    t.display(&widened),
                );
            }

            #[test]
            fn numeric_literals_in_type_position_mean_their_kind() {
                // The lattice cannot express a numeric singleton: a literal
                // constructor yields the kind itself, and no singleton is
                // ever observable. Atoms keep their singletons.
                let mut t = $ctor;
                let one = t.int_lit(1);
                let int = t.int();
                assert!(t.is_equivalent(&one, &int));
                assert_eq!(t.as_int_singleton(&one), None);
                let pi = t.float_lit(2.5);
                let float = t.float();
                assert!(t.is_equivalent(&pi, &float));
                assert_eq!(t.as_float_singleton(&pi), None);
                assert!(!t.is_singleton_lit(&one));
                let ok = t.atom_lit("ok");
                assert!(t.is_singleton_lit(&ok));
            }

            #[test]
            fn widen_for_recursive_spec_key_preserves_callable_surface_shape() {
                let mut t = $ctor;
                let entries = {
                    let one = t.int_lit(1);
                    let two = t.int_lit(2);
                    t.union(one, two)
                };
                let zero = t.int_lit(0);
                let callable = {
                    let lit = t.fn_ref_lit(ClosureTarget(19), 2);
                    let surface = t.arrow(&[entries, zero], zero);
                    t.intersect(lit, surface)
                };
                let widened = t.widen_for_recursive_spec_key(&callable);
                let clauses = t
                    .callable_value_clauses(&widened)
                    .expect("widened callable clauses");
                let clause = clauses.into_iter().next().expect("widened callable clause");
                let int = t.int();
                assert!(
                    t.is_equivalent(&clause.args[0], &int),
                    "recursive-spec widening should widen callable arg literals to integer, got {}",
                    t.display(&clause.args[0]),
                );
                assert!(
                    t.is_equivalent(&clause.args[1], &int),
                    "recursive-spec widening should widen the accumulator literal to integer, got {}",
                    t.display(&clause.args[1]),
                );
                assert!(
                    t.is_equivalent(&clause.ret, &int),
                    "recursive-spec widening should widen the callable return literal to integer, got {}",
                    t.display(&clause.ret),
                );
            }
        }
    };
}

macro_rules! closure_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn erase_closure_identity_preserves_callable_surface_shape() {
                let mut t = $ctor;
                let capture = t.int_lit(10);
                let lit = t.closure_lit(ClosureTarget(3), vec![capture], 2);
                let erased = t.erase_closure_identity(&lit);
                assert!(t.closure_lit_parts(&erased).is_none());
                let clauses = t
                    .callable_clauses(&erased)
                    .expect("erased closure should remain callable");
                assert_eq!(clauses.len(), 1);
                assert_eq!(clauses[0].args.len(), 2);
                assert!(clauses[0].closure.is_none());
            }

            #[test]
            fn callable_value_clauses_apply_surface_to_closure_vars() {
                let mut t = $ctor;
                let closure = t.fn_ref_lit(ClosureTarget(3), 1);
                let int = t.int();
                let nil = t.nil();
                let surface = t.arrow(&[int], nil);
                let refined = t.intersect(closure, surface);
                let clauses = t
                    .callable_value_clauses(&refined)
                    .expect("refined callable should expose value clauses");
                assert_eq!(clauses.len(), 1);
                let clause = &clauses[0];
                assert!(clause.closure.is_some(), "value clauses should preserve closure identity");
                assert!(t.is_integer(&clause.args[0]), "the surface should specialize the closure arg");
                assert!(t.is_nil(&clause.ret), "the surface should specialize the closure return");
            }

            #[test]
            fn refine_widen_same_fn_ref_preserves_closure_identity() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let nil = t.nil();
                let fn_ref = t.fn_ref_lit(ClosureTarget(3), 1);
                let one_surface = t.arrow(&[one], nil);
                let two_surface = t.arrow(&[two], nil);
                let a = t.intersect(fn_ref, one_surface);
                let b = t.intersect(fn_ref, two_surface);
                let widened = t.refine_widen(&a, &b);
                let clauses = t
                    .callable_value_clauses(&widened)
                    .expect("same-target fn-ref widen should stay callable");
                assert_eq!(clauses.len(), 1);
                let clause = &clauses[0];
                assert!(
                    clause.closure.is_some(),
                    "same-target fn-ref widen should preserve callable identity instead of erasing to an opaque surface"
                );
                assert!(
                    t.is_integer(&clause.args[0]),
                    "same-target fn-ref widen should widen literal arg observations through the preserved callable clause"
                );
                assert!(t.is_nil(&clause.ret));
            }

            #[test]
            fn refine_widen_same_closure_target_preserves_widened_captures() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let a = t.closure_lit(ClosureTarget(3), vec![one], 1);
                let b = t.closure_lit(ClosureTarget(3), vec![two], 1);
                let widened = t.refine_widen(&a, &b);
                let parts = t
                    .closure_lit_parts(&widened)
                    .expect("same-target closure widen should preserve closure identity");
                assert_eq!(parts.target, ClosureTarget(3));
                assert_eq!(parts.captures.len(), 1);
                assert!(
                    t.is_integer(&parts.captures[0]),
                    "same-target closure widen should widen captures elementwise through the preserved closure literal"
                );
            }

            #[test]
            fn closure_lit_intersect_same_fn_narrows_captures() {
                let mut t = $ctor;
                let int = t.int();
                let ten = t.int_lit(10);
                let a = t.closure_lit(ClosureTarget(3), vec![int], 1);
                let b = t.closure_lit(ClosureTarget(3), vec![ten], 1);
                let narrowed = t.intersect(a, b);
                let parts = t
                    .closure_lit_parts(&narrowed)
                    .expect("same-target closure meet should stay a singleton");
                assert_eq!(parts.target, ClosureTarget(3));
                assert_eq!(parts.captures.len(), 1);
                assert_eq!(
                    parts.captures[0], ten,
                    "same-target closure meet should narrow captures elementwise"
                );
            }

            #[test]
            fn closure_lit_intersect_different_fn_ids_is_empty() {
                let mut t = $ctor;
                let a = t.closure_lit(ClosureTarget(3), Vec::new(), 1);
                let b = t.closure_lit(ClosureTarget(4), Vec::new(), 1);
                let intersection = t.intersect(a, b);
                assert!(
                    t.is_empty(&intersection),
                    "different closure identities should have an empty meet"
                );
            }

            #[test]
            fn display_distinguishes_fn_ref_from_closure_on_same_fn_id() {
                // fz-go4.18.28.14 audit finding: `ArrowSig`'s `lit: Option<ClosureLit>`
                // is part of its `Eq`/`Hash` identity via `kind` + `fn_id` +
                // `captures` (see `ClosureLit`'s doc comment in sigs.rs), but the
                // old `format_arrow_clause` only ever rendered `lit.fn_id`,
                // discarding `kind` and `captures` entirely. A `FnRef` lit and a
                // `Closure` lit sharing one `fn_id` (`t.fn_ref_lit` and
                // `t.closure_lit` both key their `args`/`ret` template vars off the
                // same `fn_id`, so those match too) are distinct interned `Ty`s
                // that used to render to the identical string.
                let mut t = $ctor;
                let fn_ref = t.fn_ref_lit(ClosureTarget(3), 1);
                let closure = t.closure_lit(ClosureTarget(3), Vec::new(), 1);
                assert_ne!(
                    fn_ref, closure,
                    "a FnRef lit and a Closure lit on the same fn_id must intern to distinct Tys"
                );
                assert_ne!(
                    t.display(&fn_ref),
                    t.display(&closure),
                    "distinct ArrowSig identities (FnRef vs Closure on the same fn_id) must not collide on display(), \
                     got fn_ref={} closure={}",
                    t.display(&fn_ref),
                    t.display(&closure)
                );
            }

            #[test]
            fn display_distinguishes_closure_lits_by_captures_on_same_fn_id() {
                // Same audit finding, the other axis of `ClosureLit` identity:
                // two `Closure` lits on the same `fn_id` with different
                // `captures` are distinct by `ArrowSig`'s `Eq`/`Hash` (captures
                // participate elementwise), but the old renderer never looked at
                // `captures` at all, so both collapsed to the same `#{fn_id}`
                // string.
                let mut t = $ctor;
                let one = t.atom_lit("one");
                let two = t.atom_lit("two");
                let closure_a = t.closure_lit(ClosureTarget(3), vec![one], 1);
                let closure_b = t.closure_lit(ClosureTarget(3), vec![two], 1);
                assert_ne!(
                    closure_a, closure_b,
                    "closures over the same fn_id with different captures must intern to distinct Tys"
                );
                assert_ne!(
                    t.display(&closure_a),
                    t.display(&closure_b),
                    "distinct capture sets on the same fn_id must not collide on display(), \
                     got closure_a={} closure_b={}",
                    t.display(&closure_a),
                    t.display(&closure_b)
                );
            }

            #[test]
            fn display_fn_ref_lit_rendering_is_unchanged() {
                // The common, non-colliding case (a bare `FnRef` lit, which per
                // `ClosureLit`'s invariant always carries empty `captures`) keeps
                // its original `(args) -> ret#{fn_id}` rendering — the fix only
                // adds a disambiguating suffix to `Closure` lits.
                let mut t = $ctor;
                let fn_ref = t.fn_ref_lit(ClosureTarget(3), 1);
                let rendered = t.display(&fn_ref);
                assert!(
                    rendered.ends_with("#3"),
                    "FnRef lit rendering should be unchanged, plain `#{{fn_id}}` suffix, got {}",
                    rendered
                );
            }

            #[test]
            fn tuple_contract_meet_keeps_a_single_specialized_tuple_shape() {
                let mut t = $ctor;
                let any = t.any();
                let suspended_tag = t.atom_lit("suspended");
                let continuation_surface = t.arrow(&[], any);
                let captured = t.atom_lit("captured");
                let payload = t.atom_lit("payload");
                let continuation = t.closure_lit(ClosureTarget(7), vec![captured], 0);
                let observed = t.tuple(&[suspended_tag, payload, continuation]);
                let contract = t.tuple(&[suspended_tag, any, continuation_surface]);

                let refined = t.intersect(observed, contract);
                let fields = t
                    .tuple_lit_elems(&refined)
                    .expect("tuple meets should collapse to one tuple shape, not a conjunction of tuple clauses");
                assert_eq!(fields.len(), 3);

                let repeated = t.intersect(refined, contract);
                assert_eq!(
                    repeated, refined,
                    "meeting the same tuple contract again should stay stable"
                );
            }

            #[test]
            fn intersect_preserves_concrete_suspended_return_when_it_is_already_within_contract() {
                let mut t = $ctor;
                let any = t.any();
                let list_any = t.list(any);
                let cont_tag = t.atom_lit("cont");
                let halt_tag = t.atom_lit("halt");
                let suspend_tag = t.atom_lit("suspend");
                let done_tag = t.atom_lit("done");
                let halted_tag = t.atom_lit("halted");
                let suspended_tag = t.atom_lit("suspended");
                let reducer_surface = {
                    let cont = t.tuple(&[cont_tag, any]);
                    let halt = t.tuple(&[halt_tag, any]);
                    let suspend = t.tuple(&[suspend_tag, any]);
                    let states = t.union(cont, halt);
                    let states = t.union(states, suspend);
                    t.arrow(&[any, any], states)
                };
                let continuation_surface = t.arrow(&[], any);
                let continuation = {
                    let lit = t.closure_lit(ClosureTarget(7), vec![list_any, any, reducer_surface], 0);
                    t.intersect(lit, continuation_surface)
                };
                let done = t.tuple(&[done_tag, any]);
                let halted = t.tuple(&[halted_tag, any]);
                let suspended = t.tuple(&[suspended_tag, any, continuation]);
                let observed = {
                    let two = t.union(done, halted);
                    t.union(two, suspended)
                };

                let contract = {
                    let done = t.tuple(&[done_tag, any]);
                    let halted = t.tuple(&[halted_tag, any]);
                    let suspended = t.tuple(&[suspended_tag, any, continuation_surface]);
                    let two = t.union(done, halted);
                    t.union(two, suspended)
                };

                assert!(
                    t.is_subtype(&observed, &contract),
                    "the concrete suspended-return shape should already satisfy its declared contract: observed={} contract={}",
                    t.display(&observed),
                    t.display(&contract),
                );

                let refined = t.intersect(observed, contract);
                assert_eq!(
                    refined, observed,
                    "intersecting a subtype with its contract should be an identity, not a larger conjunction"
                );

                let repeated = t.intersect(refined, contract);
                assert_eq!(repeated, observed, "repeating the same contract meet should stay stable");
            }
        }
    };
}

macro_rules! impl_types_conformance_tests {
    ($key_mod:ident, $shape_mod:ident, $semantic_mod:ident, $closure_mod:ident, $ctor:expr) => {
        key_helper_conformance_tests!($key_mod, $ctor);
        seam_helper_conformance_tests!($shape_mod, $ctor);
        semantic_helper_conformance_tests!($semantic_mod, $ctor);
        closure_helper_conformance_tests!($closure_mod, $ctor);
    };
}

impl_types_conformance_tests!(
    types_key_helpers,
    types_shape_helpers,
    types_semantics,
    types_closure,
    Types::new()
);

// fz-go4.18.28.3 — tuple-clause emptiness must prune, not fan out.
//
// A tuple type minus a union of overlapping tuple negations drives
// `emptiness::phi_tuple`. Each negation below constrains exactly one coordinate
// (the others are `any`), so an unpruned phi recursion visits
// `arity ^ |negs|` leaves (4^14 here) before concluding — the shape that made
// 00277_enum_tier0_fixture burn >120s inside one `is_subtype` query. With
// empty-product and disjoint-negation pruning the same query is linear in the
// negation count. The intent captured: the ANSWERS are the emptiness semantics
// (unchanged), and the query completes in bounded time.
#[test]
fn tuple_emptiness_under_many_overlapping_negations_is_tractable() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();
    let elem = t.union(int, atom);
    let any = t.any();
    let none = t.none();
    let arity = 4;
    let big = t.tuple(&vec![elem; arity]);

    let mut cover = none;
    for i in 0..14 {
        let a = t.atom_lit(&format!("a{i}"));
        let mut elems = vec![any; arity];
        elems[i % arity] = a;
        let neg = t.tuple(&elems);
        cover = t.union(cover, neg);
    }

    let start = std::time::Instant::now();
    // `{int, int, int, int}` inhabits `big` and no negation covers it: the
    // difference is non-empty, so `big` is NOT a subtype of the cover.
    assert!(
        !t.is_subtype(&big, &cover),
        "an all-int tuple escapes every single-coordinate atom negation"
    );
    // And with a top tuple added, the cover is total: the difference IS empty.
    let full = t.tuple(&vec![any; arity]);
    let cover_full = t.union(cover, full);
    assert!(
        t.is_subtype(&big, &cover_full),
        "adding the top tuple covers everything"
    );
    assert!(
        start.elapsed() < std::time::Duration::from_secs(5),
        "tuple emptiness under many negations must be tractable, took {:?}",
        start.elapsed()
    );
}

// fz-go4.24 — the tuples axis of an interned descriptor is hygienic by
// construction: the clause product dedups (`A ∨ A = A`), drops clauses that are
// empty by construction (arity mismatch, empty coordinate — a product with an
// empty factor is `∅`), and the persistence boundary absorbs subsumed clauses
// (`A ⊆ B ⇒ A ∨ B = B`). Without this, evidence-join traffic accumulates
// garbage clauses unboundedly (00277 interned a 60-clause tuple DNF with 54
// provably-empty clauses) and every garbage clause doubles a `dnf_neg` factor.
mod tuple_dnf_hygiene {
    use super::*;

    /// The clause product of two overlapping tuple unions yields the same
    /// merged clause from symmetric pairs; idempotence collapses them and
    /// absorption drops the clause the wider survivors already contain.
    #[test]
    fn intersect_product_dedups_and_absorbs() {
        let mut t = Types::new();
        let int = t.int();
        let any = t.any();
        let str_t = t.str_t();
        let float = t.float();

        let x = t.tuple(&[int, any]);
        let y = t.tuple(&[any, int]);
        let ss = t.tuple(&[str_t, str_t]);
        let ff = t.tuple(&[float, float]);

        let a = {
            let xy = t.union(x, y);
            t.union(xy, ss)
        };
        let b = {
            let yx = t.union(y, x);
            t.union(yx, ff)
        };
        let meet = t.intersect(a, b);

        // Product pairs: X∧Y = Y∧X = {int,int} (duplicate, and subsumed by
        // both survivors), X∧X = {int,any}, Y∧Y = {any,int}; every pair
        // involving {str,str} or {float,float} has an empty coordinate.
        let d = t.descr(&meet);
        assert_eq!(
            d.tuples.len(),
            2,
            "expected exactly the two live clauses {{int,any}} and {{any,int}}, got {}",
            t.display(&meet)
        );
        let expected = t.union(x, y);
        assert!(t.is_equivalent(&meet, &expected), "hygiene must not change the set");
    }

    /// Tuples of different arity are disjoint products: their conjunction is
    /// `∅` by construction and must not persist as a multi-pos clause.
    #[test]
    fn arity_mismatched_tuple_intersection_persists_no_clause() {
        let mut t = Types::new();
        let int = t.int();
        let one = t.tuple(&[int]);
        let two = t.tuple(&[int, int]);
        let meet = t.intersect(one, two);
        assert!(t.descr(&meet).tuples.is_empty(), "∅ must persist no tuple clause");
        assert!(t.is_empty(&meet));

        // A mixed-arity union intersect keeps exactly the matching arity.
        let three = t.tuple(&[int, int, int]);
        let a = t.union(one, two);
        let b = t.union(two, three);
        let meet = t.intersect(a, b);
        assert_eq!(t.descr(&meet).tuples.len(), 1);
        assert!(t.is_equivalent(&meet, &two));
    }

    /// `∏Aᵢ ∩ ∏Bᵢ = ∏(Aᵢ∩Bᵢ)`: one empty coordinate empties the product, so
    /// the merged clause is dropped instead of persisting provably-empty.
    #[test]
    fn empty_coordinate_tuple_intersection_persists_no_clause() {
        let mut t = Types::new();
        let int = t.int();
        let str_t = t.str_t();
        let a = t.tuple(&[int, int]);
        let b = t.tuple(&[str_t, int]);
        let meet = t.intersect(a, b);
        assert!(t.descr(&meet).tuples.is_empty(), "∅ must persist no tuple clause");
        assert!(t.is_empty(&meet));
    }

    /// Absorption at union: `A ⊆ B ⇒ A ∨ B = B`. Near-duplicate evidence-join
    /// clauses collapse instead of accumulating across fixpoint iterations.
    #[test]
    fn union_absorbs_subsumed_tuple_clauses() {
        let mut t = Types::new();
        let int = t.int();
        let str_t = t.str_t();
        let any = t.any();
        let narrow = t.tuple(&[int, int]);
        let wide_elem = t.union(int, str_t);
        let wide = t.tuple(&[wide_elem, any]);

        let joined = t.union(narrow, wide);
        assert_eq!(t.descr(&joined).tuples.len(), 1, "narrow ⊆ wide ⇒ narrow ∨ wide = wide");
        assert!(t.is_equivalent(&joined, &wide));

        // Symmetric order: the wider clause survives regardless of position.
        let joined = t.union(wide, narrow);
        assert_eq!(t.descr(&joined).tuples.len(), 1);
        assert!(t.is_equivalent(&joined, &wide));
    }
}

// fz-go4.25 — list-clause emptiness: exact-empty evidence must survive the
// positive elem fold.
//
// A list clause's positive fold tracks the element type of the NONEMPTY
// fragment of the intersection. An exact-empty sig (`elem: None`) admits no
// nonempty lists, so once one is folded the nonempty fragment is proven void
// — a later `elem: Some(_)` sig must not resurrect it. The old fold's single
// `Option<Descr>` cell used `None` for both "no evidence yet" and "fragment
// proven empty" (the unknown-is-not-none conflation), so
// `[exact_empty, list(int)]` folded to `Some(int)` and the clause
// `pos=[exact_empty, list(int)], neg=[list(atom)]` — which denotes ∅, since
// the positive intersection is exactly `{[]}` and `list(atom)` covers `[]` —
// was judged non-empty. Conservative direction only, but it poisons
// subtype/disjoint answers built on it.
//
// The tests drive the clause shapes through the public Ty algebra:
// `difference` uses the raw descriptor ops, so double negation stacks two
// positive sigs into one clause without the MergeSig collapse that
// `Types::intersect` applies.
mod list_clause_emptiness_matrix {
    use super::*;

    /// `pos=[p1, p2]` as ONE list clause: `p1 ∩ ¬¬p2` — the raw descriptor
    /// intersection concatenates positive sigs instead of merging them.
    fn stacked_pos(t: &mut Types, p1: Ty, p2: Ty) -> Ty {
        let any = t.any();
        let not_p2 = t.difference(any, p2);
        t.difference(p1, not_p2)
    }

    #[test]
    fn exact_empty_then_elem_sig_keeps_empty_evidence() {
        let mut t = Types::new();
        let int = t.int();
        let atom = t.atom();
        let e = t.empty_list();
        let li = t.list(int);
        let la = t.list(atom);

        // pos=[exact_empty, list(int)] denotes exactly {[]}: non-empty…
        let mixed = stacked_pos(&mut t, e, li);
        assert!(!t.is_empty(&mixed), "[] ∩ list(int) = {{[]}} is inhabited");
        // …and {[]} ⊆ list(atom) (which allows []), so the difference is ∅.
        let bad = t.difference(mixed, la);
        assert!(
            t.is_empty(&bad),
            "([] ∩ list(int)) \\ list(atom) = {{[]}} \\ list(atom) = ∅"
        );
        assert!(
            t.is_subtype(&mixed, &la),
            "[] ∩ list(int) = {{[]}} is a subtype of list(atom)"
        );
    }

    #[test]
    fn elem_sig_then_exact_empty_keeps_empty_evidence() {
        // Same clause, opposite fold order — pins the (inhabited, exact-empty)
        // arm as well as the (empty-evidence, elem) arm.
        let mut t = Types::new();
        let int = t.int();
        let atom = t.atom();
        let e = t.empty_list();
        let li = t.list(int);
        let la = t.list(atom);

        let mixed = stacked_pos(&mut t, li, e);
        assert!(!t.is_empty(&mixed), "list(int) ∩ [] = {{[]}} is inhabited");
        let bad = t.difference(mixed, la);
        assert!(
            t.is_empty(&bad),
            "(list(int) ∩ []) \\ list(atom) = {{[]}} \\ list(atom) = ∅"
        );
    }

    #[test]
    fn empty_list_minus_empty_list_is_empty() {
        // The audit's structurally-identical pair: P ∧ ¬P. The DNF builder's
        // hygiene drop already catches this shape; the answer is pinned here
        // so the semantic layer stays honest if that drop ever moves.
        let mut t = Types::new();
        let e = t.empty_list();
        let d = t.difference(e, e);
        assert!(t.is_empty(&d), "[] \\ [] = ∅");

        // Non-structural variant that reaches list_clause_empty: [] minus a
        // DIFFERENT sig that still covers [].
        let atom = t.atom();
        let la = t.list(atom);
        let d2 = t.difference(e, la);
        assert!(t.is_empty(&d2), "[] \\ list(atom) = ∅ (list(atom) allows [])");
    }

    // SOUNDNESS guards: the fix may only flip answers empty-ward for
    // genuinely-empty sets. These pin inhabited neighbors of the fixed cases
    // as non-empty — evidence that inhabited fragments are never dropped.
    #[test]
    fn inhabited_neighbors_stay_non_empty() {
        let mut t = Types::new();
        let int = t.int();
        let atom = t.atom();
        let e = t.empty_list();
        let li = t.list(int);
        let la = t.list(atom);
        let nea = t.non_empty_list(atom);

        // {[]} minus only the NONEMPTY atom lists keeps []: inhabited.
        let mixed = stacked_pos(&mut t, e, li);
        let keeps_nil = t.difference(mixed, nea);
        assert!(
            !t.is_empty(&keeps_nil),
            "{{[]}} \\ non_empty_list(atom) still contains []"
        );

        // list(int) \ list(atom) keeps every nonempty int list: inhabited.
        let ints_escape = t.difference(li, la);
        assert!(!t.is_empty(&ints_escape), "list(int) \\ list(atom) contains [1]");

        // And the fully-covered nonempty case still collapses: empty.
        let nei = t.non_empty_list(int);
        let covered = t.difference(nei, li);
        assert!(t.is_empty(&covered), "non_empty_list(int) \\ list(int) = ∅");
    }
}

mod smoke {
    use super::*;

    fn smoke_primitives_distinct(t: &mut Types) {
        let i = t.int();
        let f = t.float();
        let a = t.atom();
        assert!(t.is_disjoint(&i, &f), "int vs float must be disjoint");
        assert!(t.is_disjoint(&i, &a), "int vs atom must be disjoint");
        assert!(t.is_disjoint(&f, &a), "float vs atom must be disjoint");
        assert!(!t.is_disjoint(&i, &i), "int must overlap itself");
    }

    fn smoke_union_idempotent(t: &mut Types) {
        let i = t.int();
        let u = t.union(i, i);
        assert!(t.is_equivalent(&u, &i));
    }

    fn smoke_intersect_idempotent(t: &mut Types) {
        let i = t.int();
        let x = t.intersect(i, i);
        assert!(t.is_equivalent(&x, &i));
    }

    fn smoke_complement_involution(t: &mut Types) {
        let i = t.int();
        let once = t.complement(i);
        let twice = t.complement(once);
        assert!(t.is_equivalent(&twice, &i));
    }

    fn smoke_de_morgan(t: &mut Types) {
        let i = t.int();
        let f = t.float();
        let u = t.union(i, f);
        let lhs = t.complement(u);
        let ni = t.complement(i);
        let nf = t.complement(f);
        let rhs = t.intersect(ni, nf);
        assert!(t.is_equivalent(&lhs, &rhs));
    }

    fn smoke_subtype_reflexive(t: &mut Types) {
        let i = t.int();
        assert!(t.is_subtype(&i, &i));
    }

    fn smoke_int_lit_in_int(t: &mut Types) {
        // A literal in type position means its kind: int_lit IS int. The
        // lattice cannot express a numeric singleton, by design.
        let i = t.int();
        let lit = t.int_lit(42);
        assert!(t.is_subtype(&lit, &i));
        assert!(t.is_subtype(&i, &lit));
    }

    fn smoke_nil_in_atom(t: &mut Types) {
        let n = t.nil();
        let a = t.atom();
        assert!(t.is_subtype(&n, &a));
    }

    fn smoke_top_bottom(t: &mut Types) {
        let top = t.any();
        let bot = t.none();
        assert!(t.is_top(&top));
        assert!(t.is_empty(&bot));
        assert!(!t.is_top(&bot));
        assert!(!t.is_empty(&top));
    }

    fn smoke_tuple_element_disjoint(t: &mut Types) {
        let i = t.int();
        let a = t.atom();
        let ti = t.tuple(&[i]);
        let ta = t.tuple(&[a]);
        assert!(t.is_disjoint(&ti, &ta));
    }

    fn smoke_arrow_contravariance(t: &mut Types) {
        let any = t.any();
        let i = t.int();
        let wide = t.arrow(&[any], i);
        let arg = i;
        let narrow = t.arrow(slice::from_ref(&arg), i);
        assert!(t.is_subtype(&wide, &narrow));
    }

    fn smoke_list_covariance(t: &mut Types) {
        let i = t.int();
        let lit = t.int_lit(42);
        let l_lit = t.list(lit);
        let l_int = t.list(i);
        assert!(t.is_subtype(&l_lit, &l_int));
        assert!(t.is_subtype(&l_lit, &l_lit));
    }

    fn smoke_core_predicates(t: &mut Types) {
        let one = t.int_lit(1);
        let int = t.int();
        let float = t.float();
        let resource = t.resource(int);
        let nil = t.nil();
        let bool_t = t.bool();
        let atom_lit = t.atom_lit("ok");
        let atom = t.atom();
        let top = t.any();
        let bot = t.none();

        assert!(t.is_integer(&one));
        assert!(t.is_integer(&int));
        assert!(!t.is_integer(&float));
        assert!(
            !t.is_integer(&resource),
            "resource(integer) must stay a boxed resource value, not collapse into the raw integer lane",
        );
        assert!(t.is_floating(&float));
        assert!(!t.is_floating(&int));
        assert!(t.is_nil(&nil));
        assert!(!t.is_nil(&top));
        assert!(t.is_bool(&bool_t));
        assert!(!t.is_bool(&atom_lit));
        assert!(t.is_atom_type(&nil));
        assert!(t.is_atom_type(&bool_t));
        assert!(t.is_atom_type(&atom));
        assert!(!t.is_atom_type(&int));
        assert!(t.is_top(&top));
        assert!(t.is_empty(&bot));
    }

    fn smoke_display_renders(t: &mut Types) {
        let i = t.int();
        let s = t.display(&i);
        assert_eq!(s, "int", "display should name the integer axis, not collapse it to any");
    }

    macro_rules! impl_smoke_suite {
        ($impl_name:ident, $ctor:expr) => {
            mod $impl_name {
                use super::*;

                #[test]
                fn primitives_distinct() {
                    smoke_primitives_distinct(&mut $ctor);
                }

                #[test]
                fn union_idempotent() {
                    smoke_union_idempotent(&mut $ctor);
                }

                #[test]
                fn intersect_idempotent() {
                    smoke_intersect_idempotent(&mut $ctor);
                }

                #[test]
                fn complement_involution() {
                    smoke_complement_involution(&mut $ctor);
                }

                #[test]
                fn de_morgan() {
                    smoke_de_morgan(&mut $ctor);
                }

                #[test]
                fn subtype_reflexive() {
                    smoke_subtype_reflexive(&mut $ctor);
                }

                #[test]
                fn int_lit_in_int() {
                    smoke_int_lit_in_int(&mut $ctor);
                }

                #[test]
                fn nil_in_atom() {
                    smoke_nil_in_atom(&mut $ctor);
                }

                #[test]
                fn top_bottom() {
                    smoke_top_bottom(&mut $ctor);
                }

                #[test]
                fn tuple_element_disjoint() {
                    smoke_tuple_element_disjoint(&mut $ctor);
                }

                #[test]
                fn arrow_contravariance() {
                    smoke_arrow_contravariance(&mut $ctor);
                }

                #[test]
                fn list_covariance() {
                    smoke_list_covariance(&mut $ctor);
                }

                #[test]
                fn core_predicates() {
                    smoke_core_predicates(&mut $ctor);
                }

                #[test]
                fn display_renders() {
                    smoke_display_renders(&mut $ctor);
                }
            }
        };
    }

    impl_smoke_suite!(types, Types::new());
}

/// fz-kdt.80 — the interned DNF carries no exact-duplicate clause on any axis.
///
/// The activation key is supposed to be a join homomorphism: keying the union
/// of two evidence rows must give the same key as keying either row, whenever
/// the key language cannot tell them apart. `erase_closure_identity` is the
/// step that makes two branded closures indistinguishable — and the union it
/// erases carries one funcs clause per brand. Erasing the brands in place
/// leaves `A ∨ A`, which interns as a DIFFERENT `Ty` than `A` unless the
/// persistence boundary collapses it.
mod erased_closure_dnf_hygiene {
    use super::*;
    use crate::compiler2::identity::{ActivationKey, FunctionId, RootId};

    /// Two closures over one declared surface, differing only in brand.
    fn branded_pair(t: &mut Types) -> (Ty, Ty) {
        let int = t.int();
        let nil = t.nil();
        let surface = t.arrow(&[int], nil);
        let left = t.closure_lit(ClosureTarget(3), vec![], 1);
        let right = t.closure_lit(ClosureTarget(4), vec![], 1);
        let left = t.intersect(left, surface);
        let right = t.intersect(right, surface);
        (left, right)
    }

    #[test]
    fn erasing_two_brands_of_one_surface_leaves_one_funcs_clause() {
        let mut t = Types::new();
        let (left, right) = branded_pair(&mut t);
        let joined = t.union(left, right);
        assert_eq!(
            t.descr(&joined).funcs.len(),
            2,
            "the brands are distinguishable before erasure, so the union keeps both clauses"
        );

        let erased = t.erase_closure_identity(&joined);
        assert_eq!(
            t.descr(&erased).funcs.len(),
            1,
            "A ∨ A = A: erasing the only distinguishing field must not leave two copies, got {}",
            t.display(&erased)
        );
        assert_eq!(
            erased,
            t.erase_closure_identity(&left),
            "and the collapsed union must be the very same interned id as either erased arm"
        );
    }

    #[test]
    fn the_activation_key_of_an_erased_union_is_the_key_of_each_arm() {
        let mut t = Types::new();
        let (left, right) = branded_pair(&mut t);
        let joined = t.union(left, right);

        let key_of = |t: &mut Types, ty: Ty| {
            let erased = t.erase_closure_identity(&ty);
            ActivationKey::from_inputs(RootId::for_test(0), FunctionId::for_test(0), &[erased], t)
        };
        let left_key = key_of(&mut t, left);
        let right_key = key_of(&mut t, right);
        let joined_key = key_of(&mut t, joined);

        assert_eq!(left_key, right_key, "same surface, erased brand: one key");
        assert_eq!(
            joined_key, left_key,
            "the key must be a join homomorphism where the key language cannot see the difference"
        );
    }
}

/// fz-kdt.105 — a union's interned identity is its DENOTATION, not the order
/// its clauses arrived in.
///
/// `dnf_union` concatenates clause lists, so `A ∨ B` and `B ∨ A` reach the
/// interner as two different `Vec<Conj<_>>` and hash to two different `Descr`s.
/// Two `Ty`s for one set means the ACTIVATION KEY built from them differs too,
/// so which specializations exist becomes a function of the scheduler's arrival
/// order rather than of the program. The shape below is the one the reduce
/// bridge actually joins: `{:cont, list(int)} | {:halt, int}`.
mod union_clause_order {
    use super::*;
    use crate::compiler2::identity::{ActivationKey, FunctionId, RootId};

    fn cont_and_halt(t: &mut Types) -> (Ty, Ty) {
        let int = t.int();
        let ints = t.list(int);
        let cont = t.atom_lit("cont");
        let halt = t.atom_lit("halt");
        let cont_arm = t.tuple(&[cont, ints]);
        let halt_arm = t.tuple(&[halt, int]);
        (cont_arm, halt_arm)
    }

    #[test]
    fn a_union_interns_to_one_type_whichever_arm_arrives_first() {
        let mut t = Types::new();
        let (cont, halt) = cont_and_halt(&mut t);
        let forward = t.union(cont, halt);
        let backward = t.union(halt, cont);
        assert_eq!(
            forward,
            backward,
            "one denotation, one interned id: got {} vs {}",
            t.display(&forward),
            t.display(&backward)
        );
    }

    #[test]
    fn the_activation_key_of_a_union_does_not_depend_on_arm_order() {
        let mut t = Types::new();
        let (cont, halt) = cont_and_halt(&mut t);
        let forward = t.union(cont, halt);
        let backward = t.union(halt, cont);

        // `from_inputs` addresses its inputs, and the addresser numbers a tuple
        // union's alternatives by CLAUSE POSITION (`AddrStep::Variant`), so one
        // key for both arms is also the assertion that the variant numbering —
        // and every `a0_uK_…` var name derived from it — follows canonical
        // order rather than arrival order.
        let key_of =
            |t: &mut Types, ty: Ty| ActivationKey::from_inputs(RootId::for_test(0), FunctionId::for_test(0), &[ty], t);
        let forward_key = key_of(&mut t, forward);
        let backward_key = key_of(&mut t, backward);
        assert_eq!(
            forward_key, backward_key,
            "the specialization a callee gets must be a function of the type it is passed, \
             not of which branch the scheduler ran first"
        );
    }
}
