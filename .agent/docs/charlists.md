# Charlists

fz has no charlist type. A list of integers is a list of integers, and text is
a binary (`<<>>`, UTF-8). There is no separate "list of codepoints" value with
its own identity, no `'...'` literal, and no `~c` sigil — the lexer does not
treat single quotes specially.

## Rendering

The value renderer behind `dbg` and inspection prints a list of integers as a
list. `[5, 3, 1]` renders as `[5, 3, 1]`; `[42]` renders as `[42]`. The renderer
never emits charlist syntax (`~c"..."`) for any value.

This is the one place fz's rendering differs from Elixir's `IO.inspect` on the
same data. Elixir prints a list whose every element is a printable codepoint
(`?\s` through `?~`) as a charlist: `IO.inspect([42])` prints `~c"*"`, while
`IO.inspect([5, 3, 1])` prints `[5, 3, 1]` (1, 3, and 5 are control codepoints,
so it stays a list).

## Fixtures

A fixture whose golden comes from Elixir (see [fixtures](fixtures.md)) and that
builds an all-printable integer list mismatches on rendering alone. Such
fixtures use element sets with at least one non-printable codepoint — a small
control value, or a value above 126 — or non-integer elements, so Elixir renders
a plain list that fz reproduces exactly.
