# Charlist Divergence (authorized, fz-g58)

Decision (fz-g58.0.3): for the duration of the fz-g58 epic (Elixir-parity
List/Enum/Enumerable), **charlists are out of scope** as an explicit, authorized
divergence from Elixir. Tracked for a future plan in epic **fz-3bg**.

## What fz does not have

fz has no charlist type. The lexer has no single-quote (`'...'`) handling and
no `~c` sigil, and there is no "list of integer codepoints" value with charlist
identity. fz strings are binaries (`<<>>` / UTF-8), as in modern Elixir.

## What is therefore excluded from fz-g58

- `'...'` charlist literals and the `~c` sigil.
- The charlist-only `List` functions: `to_atom/1`, `to_existing_atom/1`,
  `to_integer/1,2`, `to_float/1`, `to_string/1`, `to_charlist/1`,
  `ascii_printable?/2`. (fz-g58.7.4 lands the rest of `List` without these.)
- `++` over charlists as charlists (the operator still works on plain lists).

The full term/binary surface of `List` and `Enum` is unaffected — only the
charlist-specific corner is deferred.

## The concrete fact this protects oracle fixtures from

Elixir's `IO.inspect` renders a list whose every element is a printable
codepoint (roughly `?\s..?~`) as a charlist literal, not a list:

    iex> IO.inspect([42])      #=> ~c"*"
    iex> IO.inspect([5, 3, 1]) #=> [5, 3, 1]   (1/3/5 are control codepoints)

fz, having no charlist rendering, prints `[42]`. So an oracle fixture (see
[fixtures](fixtures.md)) that sorts or builds an all-printable integer list
would diverge purely on rendering, not on Enum/List semantics.

**Policy for fz-g58 fixtures:** do not use all-printable integer lists in oracle
goldens. Pick element sets that include at least one non-printable codepoint
(e.g. a small control value like `1`, `2`, `3`, or a value `> 126`), or use
non-integer elements, so Elixir renders a plain list.

## Revisiting

When charlists are wanted, epic fz-3bg adds the literal syntax, the codepoint
rendering rule above, and the charlist-only `List` functions, at which point the
fixture policy here can be relaxed.
