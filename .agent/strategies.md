# Strategies

Strategies are reusable ways of attacking a class of problems.

Docs in [docs.md](docs.md) explain how subsystems work. Strategies explain how
to work a problem when the subsystem is not yet doing the right thing.

Use this index when you need a concrete debugging and repair loop rather than a
subsystem model.

- [Output Contract Loop](strategies/output-contract-loop.md)
  Start from the desired externally-visible result, work a small example on
  paper, make the signal loud with telemetry, pin it with tests, trace the
  root cause backwards, then repair the data model from the bottom up.

- [Red-Test Worklist](strategies/red-test-worklist.md)
  When a branch carries many failing/hanging tests, disable them all behind a
  greppable marker to make the suite green, then re-enable one at a time --
  judging each test's intent against its assertions -- so every new red is
  unmistakably caused by the change in front of you.

- [Profile a Compilation](strategies/profile-a-compilation.md)
  Capture a `--log-telemetry` stream on the slow door, distill it with
  `tools/distill-telemetry.exs` into where the time went (by kind, by subject,
  by re-run and by the fact that woke each re-run), corroborate the magnitude
  with a sample of the plain binary, then name the mechanism and find its
  ticket.
