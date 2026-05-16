# Running loom verification (fz-q8d.3)

`fz-runtime` carries a loom model-checker test that exhaustively
verifies the `SharedBin` retain/release atomic ordering. By default the
loom dep is dormant (the `[target.'cfg(loom)'.dependencies]` table only
activates under the `loom` cfg) and the test module is gated behind
`#[cfg(all(test, loom))]`. Default `cargo test` builds compile against
`std::sync::atomic` and run zero loom checks.

## Run

```bash
RUSTFLAGS="--cfg loom" cargo test --release -p fz-runtime loom_
```

The `--release` flag is essential: loom enumerates O(thousands) of
interleavings and the debug build is roughly an order of magnitude
slower. The `loom_` filter restricts to the `loom_tests::*` module so
the rest of the test suite (which references `std` atomic orderings
that loom doesn't model) is skipped.

## What it verifies

Two child threads each call `shared_bin_retain` followed by
`shared_bin_release` on the same SharedBin; the "main" thread issues
the final release. For every legal thread interleaving loom can
produce, the test asserts:

  * The destructor fires exactly once (no missed-free, no double-free).
  * The destructor only fires when refcount transitions to zero (no
    UAF: every retain/release pair is balanced; no premature drop).

Failures surface as panics during `loom::model`'s iteration. A passing
run is silent.

## Scope

This is not a CI gate (loom runs are slow; the verification is a
one-time correctness witness, not a continuous check). Re-run before
any commit that changes `procbin::shared_bin_retain` or
`procbin::shared_bin_release` — those are the only two functions whose
ordering claims the model covers.
