use crate::cli::test_runner::run_str;
use crate::ir_interp::extern_call::tests_support::{DTOR_FIRED, DTOR_LAST_PAYLOAD};
use crate::ir_interp::extern_call::tests_support_lock;
use std::sync::atomic::Ordering;

/// fz-swt.7 acceptance — interp BIF round-trip.
///
/// User-level fz source declares a wrapper around a C extern and uses
/// `make_resource(payload, &wrapper/1)`. The interp BIF walks the
/// closure's IR body, resolves the extern symbol to the C fn pointer
/// in `tests_support`, allocates an off-heap Resource, and returns a
/// `TAG_RESOURCE` stub. The process heap is dropped at test
/// scope exit; MSO sweep invokes the dtor on the payload exactly once.
#[test]
fn make_resource_bif_round_trip() {
    let _g = tests_support_lock().lock().unwrap_or_else(|e| e.into_inner());
    DTOR_FIRED.store(0, Ordering::Relaxed);
    DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

    let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_make_resource() do
  r = make_resource(42, &dwrap/1)
  assert(true)
end
"#;
    run_str(src).expect("test_runner run_str succeeded");

    assert_eq!(
        DTOR_FIRED.load(Ordering::Relaxed),
        1,
        "dtor must fire exactly once after process heap drop"
    );
    // fz-4mk — the dtor body runs as ordinary fz code through
    // dispatched closure; the extern's `:: integer` marshal class
    // unboxes the payload before the C fn sees it. So the C dtor
    // receives the unboxed int 42, not the external word bits.
    assert_eq!(
        DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
        42,
        "dtor (called via fz dispatch + extern unboxing) receives the unboxed int payload"
    );
}

/// fz-swt.9 acceptance — aliasing inside a single process.
///
/// `r2 = r1` copies the resource value; both names refer to the
/// same on-heap stub which holds a single refcount edge to the
/// off-heap Resource. The dtor must fire **exactly once** when the
/// process heap drops — not zero times (we'd be leaking the
/// payload), and not twice (we'd be double-freeing).
#[test]
fn aliasing_in_one_process_fires_dtor_once() {
    let _g = tests_support_lock().lock().unwrap_or_else(|e| e.into_inner());
    DTOR_FIRED.store(0, Ordering::Relaxed);
    DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

    let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_alias_once() do
  r1 = make_resource(7, &dwrap/1)
  r2 = r1
  r3 = r2
  # Three names, one off-heap Resource. Until heap drop, refcount is 1.
  assert(true)
end
"#;
    run_str(src).expect("test_runner run_str succeeded");

    assert_eq!(
        DTOR_FIRED.load(Ordering::Relaxed),
        1,
        "aliasing three bindings must still produce exactly one dtor call",
    );
    // fz-4mk — dtor dispatches as fz code, extern unboxes (see
    // make_resource_bif_round_trip).
    assert_eq!(
        DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
        7,
        "dtor receives the unboxed int payload",
    );
}

/// fz-swt.9 acceptance — two *distinct* `make_resource` calls each
/// fire their dtor exactly once. Confirms we're counting allocations,
/// not bindings, and that the MSO sweep walks the chain correctly
/// when it contains more than one Resource stub.
#[test]
fn two_distinct_resources_each_fire_once() {
    let _g = tests_support_lock().lock().unwrap_or_else(|e| e.into_inner());
    DTOR_FIRED.store(0, Ordering::Relaxed);
    DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

    let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_two_resources() do
  a = make_resource(11, &dwrap/1)
  b = make_resource(22, &dwrap/1)
  assert(true)
end
"#;
    run_str(src).expect("test_runner run_str succeeded");

    assert_eq!(
        DTOR_FIRED.load(Ordering::Relaxed),
        2,
        "two distinct make_resource calls must each fire their dtor once",
    );
}

/// fz-swt.8 acceptance — `.value` round-trip through the interp.
///
/// `get/1` lives in module `R` (the declaring module of the opaque
/// alias `t`) and returns `h.value`. The test invokes it from a
/// `test_*` fn — also in `R` — to satisfy the opaque-visibility
/// gate. The handle is constructed via `make_resource(99, ...)`;
/// after `.value` the interp must read back the raw `99` payload.
#[test]
fn value_accessor_round_trip_in_interp() {
    let _g = tests_support_lock().lock().unwrap_or_else(|e| e.into_inner());
    DTOR_FIRED.store(0, Ordering::Relaxed);
    DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

    // Note: test fns must live at top level (the test_runner only
    // discovers `test_*` fns by their FINAL segment). We therefore
    // keep the dtor wrapper, the resource ctor wrapper, the
    // accessor and the assertion at top-level too, and rely on
    // the opaque alias being a top-level (unqualified) tag — its
    // visibility gate trivially passes (no owner module). This
    // exercises the runtime read path (`fz_map_get` recognising
    // `TAG_RESOURCE`) end-to-end; the visibility gate is
    // covered by the planner-side unit tests above.
    // Declaring module `R` wraps the opaque alias + accessor; the
    // dtor wrapper and the `test_*` entry stay at top level (the
    // test_runner only discovers `test_*` fns by their FINAL
    // segment, and item-macros inside a `defmodule` body produce
    // bare-named fns per fz-ul4.16.5). `get_value` lives inside
    // `R`, where the visibility gate accepts the `.value` access.
    // `test_value_round_trip` calls `R.get_value` from top level
    // — visibility is irrelevant on the call site, only on the
    // `.value` syntax itself.
    let src = r#"
defmodule R do
  @type t :: opaque resource(integer)

  fn get_value(h), do: h.value
end

extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)

fn test_value_round_trip() do
  r = make_resource(99, &dwrap/1)
  assert(R.get_value(r) == 99)
end
"#;
    run_str(src).expect("test_runner run_str succeeded");
    // Verify the dtor fired exactly once with payload 99 once the process heap
    // dropped with its owning runtime.
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1, "dtor fires once on heap drop",);
    // fz-4mk — see make_resource_bif_round_trip; dtor sees unboxed.
    assert_eq!(
        DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
        99,
        "dtor receives the unboxed int payload",
    );
}
