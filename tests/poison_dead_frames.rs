//! A continuation frame that has resumed is dead. A build with the
//! `poison_dead_frames` feature marks every released frame dead (null code
//! pointer, unused kind bytes, an impossible raw word) instead of giving it
//! back to the heap, so a native path that reads a frame after its resume
//! fails loudly.
//!
//! Run with `cargo test --features poison_dead_frames --test poison_dead_frames`.
//! The feature changes what the compiler emits, so no other test runs under it.
#![cfg(feature = "poison_dead_frames")]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, id};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");

/// Programs whose native paths cover each way a continuation resumes: a map
/// and a filter that build two hundred thousand pending frames each, a try/rescue, a receive
/// that parks and is woken by a matching reply, a large list passed between
/// two processes, a tail loop that yields on its reduction budget, and two long bodies whose
/// steps share one frame that no step may release.
const FIXTURES: [&str; 9] = [
    "fixtures/01293_enum_map_over_two_hundred_thousand_elements_does_not_overflow_the_stack",
    "fixtures/01294_enum_filter_over_four_hundred_thousand_elements_does_not_overflow_the_stack",
    "fixtures/00803_rescue_and_after_together_rescue_once_and_run_after_once",
    "fixtures/00901_a_matched_reply_is_gifted_by_the_sender_and_grafted_by_the_parent",
    "fixtures/00241_pinned_ref_receive",
    "fixtures/00911_two_processes_pass_a_large_list_back_and_forth_and_each_message_crosses_in_one_gift",
    "fixtures2/behavior/fib_tailrec",
    "fixtures/01253_a_thousand_sequential_calls_sum_their_results",
    "fixtures/01255_a_body_frame_is_not_given_back_while_later_steps_still_read_it",
];

fn source(stem: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("{stem}.fz"))
}

fn expected(stem: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("{stem}.expected.txt"));
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn run(stem: &str) -> Output {
    Command::new(FZ2_BIN)
        .arg("run")
        .arg(source(stem))
        .output()
        .expect("invoke fz2 run")
}

fn build_and_run(stem: &str) -> Output {
    let binary = std::env::temp_dir().join(format!("fz_poison_{}_{}", id(), stem.rsplit('/').next().unwrap()));
    let build = Command::new(FZ2_BIN)
        .arg("build")
        .arg(source(stem))
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("invoke fz2 build");
    assert!(
        build.status.success(),
        "{stem}: build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let output = Command::new(&binary).output().expect("run built binary");
    let _ = fs::remove_file(&binary);
    output
}

fn assert_prints_expected(stem: &str, path: &str, output: &Output) {
    assert!(
        output.status.success(),
        "{stem} ({path}): exited {:?}; stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        expected(stem),
        "{stem} ({path})"
    );
}

#[test]
fn every_native_path_runs_the_matrix_programs_with_dead_frames_poisoned() {
    for stem in FIXTURES {
        assert_prints_expected(stem, "run", &run(stem));
        assert_prints_expected(stem, "build", &build_and_run(stem));
    }
}

/// The control: the same build, asked to read each continuation's outer
/// continuation after its frame is released, fails. That is what the poison
/// catches, so the passing test above means no path reads a frame after it
/// resumes.
#[test]
fn reading_the_outer_continuation_after_the_release_fails_under_poison() {
    let stem = FIXTURES[0];
    let output = Command::new(FZ2_BIN)
        .env("FZ_POISON_LATE_OUTER_READ", "1")
        .arg("run")
        .arg(source(stem))
        .output()
        .expect("invoke fz2 run");
    assert!(
        !output.status.success(),
        "{stem}: a late read of a released frame must fail, but it printed {:?}",
        String::from_utf8_lossy(&output.stdout)
    );
}
