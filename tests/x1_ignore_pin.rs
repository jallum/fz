//! A resumed continuation frame is popped only when no ref capture names one
//! of its slots. A build with the `x1_ignore_pin` feature pops it without
//! asking, so a program that reads such a slot after the pop reads reused
//! memory and prints something else.
//!
//! Each fixture below changed its output or its exit code under that build
//! when a number captured by a continuation was carried as a reference. Run
//! with `cargo test --features x1_ignore_pin --test x1_ignore_pin`: every one
//! must print its expected output and exit 0 on `run`.
//! The feature changes what the compiler emits, so no other test runs under it.
#![cfg(feature = "x1_ignore_pin")]

use fz_fixture_metadata::parse_fixture_metadata;
use std::fs;
use std::path::Path;
use std::process::Command;

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");

/// The fixtures whose results the pin once protected.
const FIXTURES: [&str; 62] = [
    "00234_large_int_send_receive",
    "00240_large_int_from_spawn",
    "00241_pinned_ref_receive",
    "00242_spawn_tagged_receive",
    "00244_out_of_order_receive",
    "00245_receive_map_pattern",
    "00247_selective_refs_stress",
    "00290_spawn_send_receive",
    "00291_spawn_child_receive",
    "00472_spawn_lambda_receive",
    "00512_spawn_send_receive",
    "00513_spawn_new_fn_resume",
    "00521_relay_process",
    "00570_actor_ring",
    "00629_enum_max_min_zip_with_agree_with_elixir",
    "00642_clause_bodies_run_every_line_in_order",
    "00758_a_switch_takes_its_value_from_the_next_token_or_after_an_equals",
    "00759_a_switch_whose_value_does_not_fit_or_that_is_not_strict_is_invalid",
    "00760_a_double_dash_ends_the_switches_and_a_lone_dash_is_positional",
    "00761_a_repeated_switch_keeps_its_last_value_unless_it_is_kept",
    "00763_a_count_switch_counts_its_occurrences",
    "00764_a_float_switch_reads_a_whole_float",
    "00765_names_are_kebab_case_and_aliases_expand_in_clusters",
    "00861_a_struct_is_a_map_with_a_module_under_its_struct_key",
    "00863_a_map_naming_a_module_is_read_and_updated_as_that_struct",
    "00910_many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued",
    "00911_two_processes_pass_a_large_list_back_and_forth_and_each_message_crosses_in_one_gift",
    "01124_a_closure_call_that_never_returns_asks_nothing_of_the_boxed_return",
    "01160_enum_functions_take_any_enumerable_as_in_elixir",
    "01166_a_map_built_in_one_call_over_thirty_two_keys_reads_like_any_other",
    "01174_uniq_keeps_the_first_of_each_value_over_many_distinct_values",
    "01199_macro_escape_turns_a_value_into_the_quoted_code_that_rebuilds_it",
    "01261_a_pid_and_a_reference_are_map_keys_and_set_members",
    "01281_a_large_map_is_built_updated_thinned_and_read_back_by_single_puts",
    "01425_callable_union_capture_containment",
    "01430_closure_environment_identity",
    "01439_concurrency_ping_pong",
    "01465_equality_widening_and_identity",
    "01547_mixed_numeric_comparison",
    "01556_multi_relay",
    "01563_nested_tuple_producer",
    "01586_receive_guard_clauses",
    "01587_receive_interleaved_tuple_arity",
    "01588_receive_list_cons_pattern",
    "01589_receive_map_heap_keys",
    "01591_receive_mixed_constructors",
    "01593_receive_shared_tuple_arity",
    "01594_receive_unconstructed_tuple_arity",
    "01614_source_struct_pattern_fields",
    "01629_term_ordering",
    "01630_three_process_chain",
    "01746_a_thrown_exited_or_raised_number_is_not_boxed",
    "01747_a_sent_number_is_not_boxed_from_send_to_receive",
    "01771_a_map_pattern_finds_a_one_word_key_in_a_map_past_the_flat_limit",
    "01772_concat_and_escape_keep_an_improper_list_as_in_elixir",
    "01773_a_map_is_walked_as_the_list_of_its_entries",
    "01818_bitwise_defines_band_bor_bxor_bnot_bsl_and_bsr_and_a_guard_may_call_them",
    "01880_ja-a_call_builds_a_continuation_only_when_its_callee_needs_a_frame",
    "01884_a_receive_with_only_an_after_clause_waits_then_runs_it",
    "01944_unicode_util_takes_the_next_codepoint_and_grapheme_cluster_of_chardata",
    "01947_map_key_order_puts_every_integer_before_every_float",
    "01965_a_grapheme_cluster_over_chardata_with_a_binary_tail_compiles",
];

#[test]
fn every_fixture_the_pin_once_protected_runs_the_same_with_the_pin_ignored() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures");
    for stem in FIXTURES {
        let source = root.join(format!("{stem}.fz"));
        let text = fs::read_to_string(&source).unwrap_or_else(|e| panic!("read {}: {e}", source.display()));
        let args = parse_fixture_metadata(&text)
            .unwrap_or_else(|e| panic!("{stem}: {e:?}"))
            .map(|metadata| metadata.matrix.args)
            .unwrap_or_default();
        let output = Command::new(FZ2_BIN)
            .arg("run")
            .arg(&source)
            .args(&args)
            .output()
            .expect("invoke fz2 run");
        let sidecar = root.join(format!("{stem}.expected.txt"));
        let expected = fs::read_to_string(&sidecar).unwrap_or_default();
        assert!(
            output.status.success(),
            "{stem}: exited {:?}; stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout), expected, "{stem}");
    }
}
