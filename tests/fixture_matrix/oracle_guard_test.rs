//! A regen refuses an oracle that answers twice differently, and refuses to
//! run without naming the fixture.

use super::*;

pub(super) fn two_agreeing_runs_yield_that_output() {
    let (dir, fixture, _) = oracle_regen_fixture("agree", None);
    let answer = oracle_guard::require_one_answer(&fixture, "x\n".into(), "x\n".into());
    assert_eq!(answer, Ok("x\n".to_string()));
    let _ = fs::remove_dir_all(dir);
}

pub(super) fn two_differing_runs_fail_naming_the_fixture_and_both_outputs() {
    let (dir, fixture, _) = oracle_regen_fixture("differ", None);
    let failure = oracle_guard::require_one_answer(&fixture, "%{a: 1, b: 2}\n".into(), "%{b: 2, a: 1}\n".into())
        .expect_err("differing runs must fail");
    assert!(failure.contains("regen.fz"), "names the fixture: {failure}");
    assert!(failure.contains("%{a: 1, b: 2}"), "shows the first output: {failure}");
    assert!(failure.contains("%{b: 2, a: 1}"), "shows the second output: {failure}");
    let _ = fs::remove_dir_all(dir);
}

pub(super) fn a_regen_that_differs_between_runs_leaves_the_golden_alone() {
    let (dir, fixture, header) = oracle_regen_fixture("flaky", Some("old\n"));
    let oracle = dir.join("regen.oracle.exs");
    let counter = dir.join("runs");
    // Each run counts itself in a file beside the fixture and prints its count,
    // so the second regen run always differs from the first.
    fs::write(
        &oracle,
        format!(
            "path = {:?}\nn = case File.read(path) do\n  {{:ok, text}} -> String.to_integer(text) + 1\n  _ -> 1\nend\nFile.write!(path, Integer.to_string(n))\nIO.puts(n)\n",
            counter.display().to_string()
        ),
    )
    .expect("write counting oracle");
    let failure = verify_oracle_pair(&fixture, &header, &oracle, OracleMode::Regen)
        .failure
        .expect("two differing runs must refuse");
    assert!(failure.contains("regen.fz"), "names the fixture: {failure}");
    assert!(failure.contains("answered twice differently"), "{failure}");
    assert_eq!(
        fs::read_to_string(fixture.sidecar_path("expected.txt")).expect("golden"),
        "old\n"
    );
    let _ = fs::remove_dir_all(dir);
}

pub(super) fn a_regen_without_a_named_fixture_is_refused() {
    let failure = oracle_guard::require_named_fixture_for_regen(OracleMode::Regen, None).expect_err("refused");
    assert!(failure.contains("ORACLE_FIXTURE"), "{failure}");
    assert_eq!(
        oracle_guard::require_named_fixture_for_regen(OracleMode::Regen, Some("01174_x")),
        Ok(())
    );
    assert_eq!(
        oracle_guard::require_named_fixture_for_regen(OracleMode::Check, None),
        Ok(())
    );
    assert_eq!(
        oracle_guard::require_named_fixture_for_regen(OracleMode::Verify, None),
        Ok(())
    );
}
