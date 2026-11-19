# The machine floor: what a program costs in instructions, and what it should cost

`tools/floor` measures run-time code in instructions per iteration and sets it
beside hand-written machine code for the same loop and beside the BEAM.

## The parts

- `programs/NN_name.exs` — one small program per operation. Each is valid
  Elixir and valid fz: `elixir` runs the file and `fz2 build` compiles the same
  file. `main` reads an iteration count from its first argument and prints one
  result.
- `measure.sh` — instructions per iteration for each side, as the slope of
  "instructions retired" between two run lengths, so start-up cancels. fz is
  run once per length; the BEAM three times per length, lowest kept. It
  refuses a row whose two sides print different results.
- `targets/targets.s` — hand-written arm64 for the loop of a program: the code
  the compiler should emit. Each instruction is annotated with the fact that
  licenses it. `targets/harness.c` builds binaries in the layout the targets
  read and checks every target against plain C over random inputs.
- `targets.sh` — builds the targets, runs that check, and prints each target's
  instructions per iteration. `targets.sh test` stops after the check.
- `report.sh` — the one command: per program, fz's count, its target, how far
  fz is above the target, and the BEAM.
- `trace.sh` / `trace.py` — single-steps one steady-state iteration of a
  compiled program under lldb and prints every instruction, summed by the
  function it ran in.

## Conventions

- A program names its target on a `# target: NAME` line. A program with no such
  line has no hand-written target and its row shows `-`.
- `# n: N1 N2` sets both sides' run lengths and `# fz-n: N1 N2` fz's alone, for
  a program whose cost grows with its result.
- Build output, run logs and traces go to `target/floor`.
- The scripts are zsh and read counts from macOS `/usr/bin/time -l`; the
  targets are arm64. `tests/floor_targets_test.rs` runs the targets' check on
  that platform and checks every `# target:` name on all of them.
- Counts taken on a development machine are for iterating. A pass or fail
  judgement is taken on the quiet bench machine.

## Reading a row

    program                               fz   target    above      beam
    02a_byte_size_small                 94.3     12.0     82.3      43.2

Every count includes the loop itself: `00_empty` is the loop with nothing in
it, on each side. The target of `02a` is 12 because the target's loop is 10 and
`byte_size` of a proven binary is two instructions more.
