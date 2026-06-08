# Charlists

fz has no charlist type. A list of integers is a list of integers, and text is
a binary (`<<>>`, UTF-8). There is no separate "list of codepoints" value with
its own identity. There is no `'...'` literal: the lexer has no rule for the
single-quote byte, so `'` lands in the catch-all arm and raises a lex error
(`unexpected character '\''`). There is no `~c`: the lexer tokenizes `~c` like
any lowercase sigil into `Tok::Sigil("c")`, and the parser rejects every sigil
with `unsupported sigil ~c`. A double-quoted `"..."` is the only text literal and
lexes to `Tok::Binary`.

## Rendering

The value renderer is `any_value::debug` in the runtime crate. `render_value`
and `render` dispatch on a value's `ValueKind`/heap tag and produce the printed
form. Every print path shares it: the `fz_dbg_value_ref` extern that backs
`dbg`, the IR interpreter, and the REPL all call the same `render_value`. The
decision is purely payload-driven, reading only the tagged bits and heap layout,
never the type system's brand axis, so the interpreter, JIT, and AOT paths agree
on output without sharing type information at runtime.

`render_list` walks the cons cells and renders each head with
`render_typed_list_head`. An `INT` head renders as its decimal digits, so a list
of integers renders as a list of integers and nothing else: `[5, 3, 1]` renders
as `[5, 3, 1]`, and `[42]` renders as `[42]`. There is no codepoint-printability
branch anywhere in list rendering, so the renderer never emits charlist syntax
(`~c"..."`) for any value. An improper tail renders as `[h | t]`.

A binary takes the other shape. `render_bitstring` prints a byte-aligned, valid,
printable (`is_printable_utf8`) UTF-8 binary as a quoted string `"..."`, and
anything else as the `<<...>>` byte-list form.

## Difference from Elixir

This is the one place fz's rendering differs from Elixir's `IO.inspect` on the
same data. Elixir prints a list whose every element is a printable codepoint
(`?\s`/32 through `?~`/126) as a charlist: `IO.inspect([42])` prints `~c"*"`,
while `IO.inspect([5, 3, 1])` prints `[5, 3, 1]` (1, 3, and 5 are control
codepoints, so it stays a list). fz prints `[42]` and `[5, 3, 1]` both as plain
lists.

## Fixtures

A fixture whose golden comes from Elixir (see [fixtures](fixtures.md)) and that
builds an all-printable integer list mismatches on rendering alone: Elixir emits
`~c"..."`, fz emits the plain list. Such fixtures use element sets with at least
one non-printable codepoint — a small control value, or a value above 126 — or
non-integer elements, so Elixir renders a plain list that fz reproduces exactly.
