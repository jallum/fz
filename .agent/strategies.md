# Strategies

Strategies are reusable ways of attacking a class of problems.

Docs in [docs.md](docs.md) explain how subsystems work. Strategies explain how
to work a problem when the subsystem is not yet doing the right thing.

Use this index when you need a concrete debugging and repair loop rather than a
subsystem model.

- [Paper First](strategies/paper-first.md)
  **Use when** a problem is too noisy to reason about directly: a wrong
  result, more work than the input warrants, or many symptoms at once. Shrink
  it to one question you can answer by hand, answer it from first
  principles, watch the system answer it, and fix the first place the two
  differ. Then return to the original and take the next question.

- [Red-Test Worklist](strategies/red-test-worklist.md)
  **Use when** a branch carries many failing or hanging tests at once.
  Disable them all behind a greppable marker so the suite is green, then
  re-enable one at a time -- judging each test's intent against its
  assertions -- so every new red is caused by the change in front of you.

- [Profile a Compilation](strategies/profile-a-compilation.md)
  **Use when** a door is slow on a program that should be cheap, or a fixture
  lane trips the matrix's wall-clock guard. Capture a `--log-telemetry`
  stream, distill it with `tools/distill-telemetry.exs` into where the work
  went (by kind, by subject, by re-run and by the fact that woke each
  re-run), corroborate the magnitude with a sample of the plain binary, then
  name the mechanism and take it to Paper First.
