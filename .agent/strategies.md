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
