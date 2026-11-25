# Working on fz

[README.md](README.md) shows how to build `fz2` and run a program. This file
covers the test suite, CI and the repository's hooks.

## Running the tests

Run the whole test suite:

```sh
cargo test --workspace
```

The repository's Cargo configuration defaults to compact output: passing tests
print progress characters instead of individual names, followed by each test
binary's summary. Failure diagnostics and compiler warnings remain visible.
Existing test commands work unchanged, including fixture tests and doctests.
Use `cargo --config term.quiet=false test --workspace -- --format pretty` to
restore individual test names (the custom fixture harness also defaults to terse);
`-- --nocapture` still exposes test output when investigating a test.

To suppress passing-test progress too, use [cargo-nextest](https://nexte.st/docs/installation/)
and run doctests separately:

```sh
cargo nextest run --workspace --show-progress none --color never
cargo test --workspace --doc
```

The repository's nextest defaults suppress individual passing results and
successful-test output. Failed tests print their captured diagnostics immediately,
once, and the final summary lists failures. Avoid `--nocapture` when keeping
output compact. Add `--no-fail-fast` to finish the suite after a failure.

## Fixtures

A fixture is a small `.fz` program in `fixtures/` with its expected output
beside it. Fixture tests run each one across every execution path that applies
(JIT, interpreter, AOT executable) and compare the output. A fixture is more
than a sample file — it is a tiny promise about the language. If quicksort
works in the JIT but not in AOT, the fixture matrix catches it.

Fixture conventions — how each fixture pins its claim — are explained in
[.agent/docs/fixtures.md](.agent/docs/fixtures.md).

## CI

CI runs formatting, clippy, rustdoc, a security audit, doctests, and workspace
tests on pull requests. Pushes to `main` and `develop` run the workspace tests
under coverage and enforce the threshold; only `main` updates the published
coverage badge.

## Pre-commit hook

A tracked pre-commit hook lives in [`.githooks/`](.githooks/). It formats
the staged Rust with `cargo fmt --all`, re-stages it, then runs
`cargo check --all` and `cargo clippy --workspace --all-targets -- -D warnings`.
The lint set itself lives in the workspace manifest, so the hook and CI both
enforce the same ownership/cloning policy without carrying a second copy of
the lint list. A clippy complaint aborts the commit before it ever reaches CI.
Git looks for hooks in `.git/hooks` by default, so enable the tracked
directory once per clone:

```sh
git config core.hooksPath .githooks
```
