use std::collections::HashMap;
use std::mem;
use std::slice;

use super::*;
use crate::runtime_type_predicate::{ListShape, ObservedSet, RuntimeTypePredicate};

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
            ints: ObservedSet::any(),
            ..RuntimeTypePredicate::none()
        }
    );
}

#[test]
fn runtime_type_predicate_projects_tuple_and_list_shapes() {
    let mut t = Types::new();
    let empty_list_ty = t.empty_list();
    let empty_list = t.runtime_type_predicate(&empty_list_ty);
    assert_eq!(
        empty_list,
        RuntimeTypePredicate {
            lists: ObservedSet::lit(ListShape::Empty),
            ..RuntimeTypePredicate::none()
        }
    );

    let int = t.int();
    let atom = t.atom();
    let tuple_ty = t.tuple(&[int, atom]);
    let tuple = t.runtime_type_predicate(&tuple_ty);
    assert_eq!(
        tuple,
        RuntimeTypePredicate {
            tuple_arities: ObservedSet::lit(2),
            ..RuntimeTypePredicate::none()
        }
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
            named_structs: ObservedSet::lit("box".to_string()),
            ..RuntimeTypePredicate::none()
        }
    );

    let mystery = t.opaque_of("mystery");
    let widened = t.runtime_type_predicate(&mystery);
    assert_eq!(widened, RuntimeTypePredicate::any());
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

            #[test]
            fn alpha_normalize_vars_collapses_alpha_equivalent_callable_shapes() {
                let mut t = $ctor;
                let lhs_a = t.type_var(TypeVarId(10));
                let lhs_b = t.type_var(TypeVarId(11));
                let lhs_ret = t.type_var(TypeVarId(12));
                let lhs = t.arrow(&[lhs_a.clone(), lhs_b, lhs_a], lhs_ret);
                let rhs_a = t.type_var(TypeVarId(30));
                let rhs_b = t.type_var(TypeVarId(31));
                let rhs_ret = t.type_var(TypeVarId(32));
                let rhs = t.arrow(&[rhs_a.clone(), rhs_b, rhs_a], rhs_ret);

                let lhs = t.alpha_normalize_vars(&lhs);
                let rhs = t.alpha_normalize_vars(&rhs);
                assert!(
                    t.is_equivalent(&lhs, &rhs),
                    "alpha-equivalent callable shapes should normalize to the same type: lhs={} rhs={}",
                    t.display(&lhs),
                    t.display(&rhs)
                );
            }

            #[test]
            fn alpha_normalize_vars_preserves_shared_var_structure() {
                let mut t = $ctor;
                let repeated_var = t.type_var(TypeVarId(10));
                let repeated = t.arrow(
                    &[repeated_var.clone(), repeated_var.clone()],
                    repeated_var,
                );
                let distinct_a = t.type_var(TypeVarId(20));
                let distinct_b = t.type_var(TypeVarId(21));
                let distinct = t.arrow(&[distinct_a.clone(), distinct_b], distinct_a);

                let repeated = t.alpha_normalize_vars(&repeated);
                let distinct = t.alpha_normalize_vars(&distinct);
                assert!(
                    !t.is_equivalent(&repeated, &distinct),
                    "alpha-normalization must preserve equality structure: repeated={} distinct={}",
                    t.display(&repeated),
                    t.display(&distinct)
                );
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

                let tagged = t.tuple(&[int.clone(), int.clone()]);
                let tagged_class = t.convergence_class(&tagged);
                assert!(!t.is_equivalent(&tagged_class, &list_class));

                let int_class = t.convergence_class(&int);
                assert!(!t.is_equivalent(&int_class, &list_class));
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
