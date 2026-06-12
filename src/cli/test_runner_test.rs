use super::*;

// PICKED: test macro with passing assert runs without error
#[test]
fn passing_test_runs_clean() {
    let src = r#"
test(:test_one) do
  assert(1 + 1 == 2)
end
"#;
    run_str(src).expect("test should pass");
}

// PICKED: test macro with failing assert surfaces as error result
#[test]
fn failing_test_returns_err() {
    let src = r#"
test(:test_bad) do
  assert(1 + 1 == 3)
end
"#;
    let r = run_str(src);
    assert!(r.is_err(), "expected failure, got {:?}", r);
}

// PICKED: multiple test blocks; one failure makes overall result an error
#[test]
fn multiple_tests_some_fail() {
    let src = r#"
test(:test_a) do
  assert(true)
end
test(:test_b) do
  assert(:x == :x)
end
test(:test_c) do
  assert(1 == 2)
end
"#;
    let r = run_str(src);
    assert!(r.is_err(), "expected at least one failure");
}

// PICKED: fn test_*() convention is discovered and run like test macro
#[test]
fn convention_style_test_fn_also_discovered() {
    // Skipping the macro: a hand-written `fn test_*() do ... end` is
    // also picked up.
    let src = r#"
fn test_plain() do
  assert(true)
end
"#;
    run_str(src).expect("test should pass");
}

// DROP: no tests defined is a no-op; no language behaviour exercised
#[test]
fn no_tests_is_a_noop() {
    let src = "fn helper(x), do: x + 1";
    run_str(src).expect("no tests, no error");
}

// -- fz-ndf.10 telemetry --

// DROP: telemetry event counts for test runner, infrastructure not language
#[test]
fn telemetry_capture_observes_passing_run() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let src = r#"
test(:test_one) do
  assert(1 + 1 == 2)
end
test(:test_two) do
  assert(:x == :x)
end
"#;
    run_through(&tel, src).expect("tests should pass");

    assert_eq!(cap.count(&["fz", "test", "run_starting"]), 1);
    assert_eq!(cap.count(&["fz", "test", "passed"]), 2);
    assert_eq!(cap.count(&["fz", "test", "failed"]), 0);
    let summary = cap.last(&["fz", "test", "summary"]).unwrap();
    assert!(matches!(summary.measurements.get("total"), Some(Value::U64(2))));
    assert!(matches!(summary.measurements.get("failures"), Some(Value::U64(0))));
}

// DROP: telemetry events for failing test, infrastructure not language
#[test]
fn telemetry_capture_observes_failing_test() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let src = r#"
test(:test_ok) do
  assert(true)
end
test(:test_bad) do
  assert(1 == 2)
end
"#;
    let _ = run_through(&tel, src);
    assert_eq!(cap.count(&["fz", "test", "passed"]), 1);
    assert_eq!(cap.count(&["fz", "test", "failed"]), 1);
    let failure = cap.last(&["fz", "test", "failed"]).unwrap();
    assert!(matches!(failure.metadata.get("name"), Some(Value::Str(_))));
    assert!(matches!(failure.metadata.get("message"), Some(Value::Str(_))));
}

// DROP: telemetry no_tests_found event, infrastructure not language
#[test]
fn telemetry_capture_observes_no_tests_found() {
    use crate::telemetry::{Capture, ConfiguredTelemetry};
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());
    run_through(&tel, "fn helper(x), do: x + 1").expect("no tests");
    assert_eq!(cap.count(&["fz", "test", "no_tests_found"]), 1);
    assert_eq!(cap.count(&["fz", "test", "summary"]), 0);
}
