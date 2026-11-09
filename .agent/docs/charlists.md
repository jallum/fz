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
and `render_with_limit` dispatch on a value's `ValueKind`/heap tag and produce
the printed form. Every print path shares it: `IO.inspect/1` and `dbg/1` (which
is `IO.inspect/1`) through `Kernel.inspect/1`, the IR interpreter, and the REPL
all call `render_value`, which means `Limit::DEFAULT` (100, Elixir's
`%Inspect.Opts{}.limit`); `Kernel.inspect/2` reaches `render_with_limit`
through `fz_inspect/2`. The decision is purely payload-driven, reading only the
tagged bits and heap layout, never the type system's brand slot, so the
interpreter, JIT, and AOT paths agree on output without sharing type
information at runtime.

A `Renderer` carries the process and the remaining `Limit`. Each element of a
list, tuple, map entry, keyword entry or bitstring byte costs one before it is
rendered, and what it renders inside spends from the same budget; once the
budget is spent, `...` replaces the elements left. Numbers, atoms, strings,
charlists, ranges and closures cost nothing of their own.

A list renders in one of three shapes, decided from its cells. A non-empty list
whose every element is an integer in 7..=13, 27 or 32..=126
(`List.ascii_printable?/1`) renders as `~c"..."` with the string escapes:
`[104, 105]` is `~c"hi"`, `[7, 104]` is `~c"\ah"`. Any other integer list, such
as `[0]`, `[128]` or `[126, 127]`, stays a list. A list whose every element is a
two-tuple with a non-alias atom key renders as a keyword list, `[a: 1]`.
Every other list renders its elements. A list's tail is always a list or `[]`,
so there is no improper form to print.

The `~c"..."` text has no source form in fz: the lexer rejects every sigil, so
the renderer prints text the language cannot read back.

An atom renders as `Macro.inspect_atom(:literal, atom)` does. `nil`, `true` and
`false` print bare. An atom whose name `module_name::alias_spelling` recognises
prints as its alias: `Elixir` followed by `.`-separated segments that each
start with an ASCII capital letter and continue with ASCII letters, digits or
`_`. The module name `Foo.Bar` is the atom `Elixir.Foo.Bar` and prints
`Foo.Bar`. An identifier (a letter or `_`, then letters, digits, `_` or `@`,
then at most one `?` or `!`) and the operators and special forms Elixir leaves
unquoted print as `:name`, `:+`, `:<>`. Every other atom prints quoted through
the string escaper: `:"foo bar"`, `:"1abc"`, `:"Elixir.lower"`. As a keyword
key the same classes print `name:`, `"foo bar":`, `+:`.

`Renderer::keyword_key` is the one place
that decides keyword style, for lists and maps alike: a key can head a keyword
entry when it is an atom that is not under `Elixir.`. A map whose every key
can prints `%{a: 1}`; any other map prints `%{k => v}`, in the map's own
order. A two-tuple keyed by an alias is never a keyword entry, so `[{Foo, 1}]`
prints as a list of tuples, as in Elixir.

A binary takes the other shape. `Renderer::bitstring` prints a byte-aligned,
valid, printable (`is_printable_utf8`) UTF-8 binary as a quoted string `"..."`,
which ignores the limit, and anything else as `<<...>>`: one element per byte,
trailing bits as `n::size(k)`. One escaper, `escape_for_display`, writes
strings, quoted atoms and charlists with Elixir's escapes: `\a \b \t \n \v \f
\r \e \d \\ \"`, `\#{`, and `\uXXXX` for the invisible and lookalike
codepoints.

## Difference from Elixir

Floats, ranges, closures (`#fn<n/a>`) and struct bodies (`{...}`) keep their
own forms; closures are an opaque identity no other runtime reproduces. Map
order is the map's own: Erlang orders atom keys by atom index, and fz by name,
so a multi-key atom-keyed map is not comparable with Elixir's output.

## Fixtures

A fixture whose golden comes from Elixir (see [fixtures](fixtures.md)) matches
it on charlists: an all-printable integer list prints `~c"..."` on both sides.
