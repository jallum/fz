# Source Syntax Front Doors

`src/parser` is now lexer-only. It owns `lexer.rs`, `Tok`, `Token`, token
spans, spacing metadata, and lexer telemetry. The old AST-building
`Parser`/`items.rs`/`expressions.rs`/`patterns.rs` path has been deleted.

Compiler2 parses source in `src/compiler2/frontdoor.rs`. That front door consumes
the shared lexer tokens and produces `QuotedSourceRoot` values directly, rather
than first building old `ast::Program` / `ast::Item` trees. Runtime bootstrap
sources in `lib/*.fz` also enter compiler2 through this
quoted-source path.

Keep this boundary crisp:

- Add token-shape changes in `src/parser/lexer.rs` and `lexer_test.rs`.
- Add source grammar changes in `src/compiler2/frontdoor.rs` and
  `frontdoor_test.rs`.
- Do not revive `Parser::new`, `parse_program`, `parse_prelude`, or
  `parse_expr_eof`; old callers should move to compiler2 quoted source.

## An atom is a colon and a name

The lexer reads a colon that begins a token as an atom when what follows is an
identifier (`:ok`), a quoted name (`:"a b"`) or an operator spelling Elixir
accepts unquoted (`:+`, `:<>`, `:%{}`, `:..//`; the table is `OPERATOR_ATOMS`
in `lexer.rs`). The longest spelling wins, so `:===` is one atom. A colon after
an identifier never begins a token: `a: -1` is a keyword key, and `::` is
always the double colon, so `x :: integer` and `<<x::8>>` do not read as atoms.
A colon with none of those after it is the bare `Colon` token (`+: 2` in an
import filter).

## A file's top level takes any expression

`parse_program` reads a file with `parse_file_item`; a `defmodule` body, a
protocol body and every other item list read with `parse_item`. Both accept the
same definition items (`def`-family macro calls, `defmodule`, `alias`,
`import`, `require`, `@`-attributes, ...). Only the file's top level also
accepts any other expression as an item, so `Distill.main(argv)`, `x = 1`, `42`
and `if ... do ... end` parse there, and the same line inside a `defmodule`
fails with `does not yet parse ... at item position`.

The parser cannot tell a statement from a macro call (`def`, `test` and user
macros all lex as plain identifiers), so it does not try: a call-shaped item is
a `ScopeForm::MacroCall` and a non-call item (a literal) is a
`ScopeForm::Statement`. Expansion decides, per `pipeline.md` "A file's
top-level expressions are its `main/0`".

## Identifiers and atoms are read by Unicode class

The lexer reads characters, not bytes, for names. A name, atom or keyword key
starts with `_`, an ASCII letter, or a non-ASCII `XID_Start` character, and
continues with `XID_Continue` characters (`unicode-ident`). A non-ASCII
character is a name character only when UTS 39 allows it in identifiers
(`unicode-security`, identifier status Inclusion or Recommended), which is how
Elixir builds its set: the ligature U+FB01, the ordinal indicator U+00AA,
Bopomofo U+3105 and U+0115 are `XID_Start` or `XID_Continue` and are not name
characters (`unexpected character`). The micro sign U+00B5 is a name character
that `read_ident` folds into Greek small mu U+03BC before the NFC and script
checks, so `µ` and `μ` are one variable, atom and keyword key; `source_word`
rejects a name holding U+00B5.

A name takes one `?` or `!` as its last character and ends there: `a?b` is the
name `a?` followed by the name `b`, `a??` is `a?` followed by a `?` that quotes
nothing, and `:a?b` is the atom `:a?` followed by `b`. A variable or function
name cannot start with an uppercase or titlecase letter outside ASCII
(`unexpected character`); an atom (`:Élan`) or keyword key (`Élan: 1`) can, and
so can the allowed titlecase letters U+1FA8 to U+1FAF. Whether a word is an
alias is decided by its first character as written: an ASCII uppercase letter
starts an alias even when NFC composes it into a non-ASCII letter. An alias
holds ASCII letters, digits and underscores only: its first other character, a
non-ASCII character or a `?` or `!` mark, is reported as `invalid character`.
An atom or keyword key spelled like an alias may end in a mark (`:Ab?`,
`[Ab?: 1]`). `source_word` applies the same classes to a quoted name, so the
macro surface and the lexer agree on what one source word is.

Unquoted names, atoms and keyword keys are spelled in NFC
(`unicode-normalization`), so `cafe` plus U+0301 and the single character `é`
are one variable and one atom. `read_ident` is the one place that normalizes;
spans keep the source text as written. Quoted atoms (`:"café"`) and strings keep
the spelling they were written with. `source_word` accepts only a name that is
already NFC, because source text cannot produce a word token spelled otherwise.

A name draws its letters and digits from one script, as Elixir checks it
(`invalid mixed-script identifier found: aа`). The check runs on the NFC
spelling, on each `_`-separated chunk alone, so `hello_мир` is accepted and
`aа` (Latin plus Cyrillic) is not. Script sets are the UTS 39 augmented script
sets (`unicode-security`): Han, Hiragana and Katakana together are Japanese,
Han and Hangul together are Korean, and ASCII digits and `_` belong to every
script, while a non-ASCII digit belongs to its own script. Greek small mu
(`μ`) belongs to every script, and so does a character that UTS 39 restricts
from identifiers when NFC composition produces one; Elixir 1.19 accepts such
a composed name (`e` plus U+0306 is `ĕ`, U+0115). Quoted atoms and strings are
not checked. `read_ident` and `source_word` share `is_single_script`.

## Newline continuation is grammar-owned, not a parser lookahead

Physical newlines are first-class `Tok::Newline` tokens. Whether a newline
ends a statement or continues the previous expression falls out of which
token is on either side of it — the frontdoor parser never peeks past a
newline to guess intent.

- **Trailing eol** (operator/`.` at the END of a line): each infix
  production in `FrontDoorParser::parse_bp` calls `skip_newlines()` right
  after consuming its operator, before parsing the right-hand side. Every
  `Tok::Dot`-consuming production does the same right after consuming the
  dot: `finish_remote_target` and `finish_closure_call` (value/call access),
  `parse_alias_expr` (alias-path chains, e.g. `Foo.\n  Bar`), and
  `parse_upper_path` (the shared path parser behind
  `alias`/`import`/`require`/`defmodule`/protocol module paths). Dot
  consumes trailing eol by construction regardless of what it's chaining —
  this is ordinary trailing-position grammar, unconditional, no
  classification needed. `parse_alias_expr`'s loop guard additionally uses
  `peek_non_newline_from` to look past a newline run before committing to
  consume the dot, since an alias-path dot only continues the chain when an
  uppercase segment follows (unlike remote access, which continues
  unconditionally after any dot).
- **Leading eol** (operator at the START of a line): the lexer decides.
  `parser::lexer::is_infix_only_continuation` classifies each operator/`.`
  token by whether its grammar production can *only* ever be infix/postfix
  (it has no unary/prefix form). `Lexer::tokenize` drops any run of
  `Tok::Newline` immediately preceding such a token, so the parser sees it
  glued to the prior expression exactly as if it had been written on one
  line — no `Tok::Newline` ever reaches `parse_bp` for these. `Tok::Minus`
  and `Tok::Percent` are excluded from that set on purpose: both are dual
  prefix/infix in fz — `parse_prefix` accepts `-` as unary negation and `%`
  as a `%Foo{...}` struct literal, while `infix_bp` gives them subtraction
  and modulo — so a `-` or `%` leading a fresh physical line always starts a
  *new* statement (mirrors Elixir's tokenizer, where a prefix-capable
  operator never swallows a preceding eol; `%` has no modulo in Elixir, so
  that dual role is fz-specific). `Tok::Plus` stays infix-only at a line start
  (a leading `+` continues the previous expression), yet the front door's
  prefix parser accepts a `+` inside an expression as unary plus, the call
  `+(n)`, as it does `-`.
- **Statement/`eoe` separation**: a `Tok::Newline` that reaches `parse_bp`'s
  Pratt loop matches none of its arms, so the loop returns the completed
  left-hand side. Every newline-delimited sequence then calls
  `require_newline_or_terminator`: another expression, item, or clause is legal
  only after a physical newline; an enclosing `end`/`else`/`after` may follow
  immediately. Spaces alone are never a statement separator, so `a = 1 2` is
  rejected at the `2` instead of becoming a block whose extra expression can
  be discarded downstream. Inline grammar such as call arguments, lambdas,
  and trailing `do` blocks remains inside `parse_bp` and its sub-productions
  before the sequence boundary is checked. A block with multiple separated
  statements is wrapped in `__block__`. The keyword-list parser preserves this
  ownership: it consumes newlines only when the next non-newline token is its
  comma or closing delimiter. A newline after a no-parens keyword call is left
  for the enclosing block, so the next call remains a separate statement.

There is no `starts_expr_continuation` / `peek_after_newlines`-style
lookahead in the parser. Continuation vs. new-statement is a static,
per-token fact resolved once at tokenize time (leading position) or an
ordinary grammar rule (trailing position) — never a runtime guess about
what a future token "looks like".

## Boolean operators

`||`, `&&` and `!` lex as `Tok::OrOr`, `Tok::AndAnd` and `Tok::Bang`. The Pratt
table gives `||` the binding power of `or` and `&&` that of `and`; `!` and `not`
share one prefix reader (`parse_prefix_operator`) that binds tighter than every
binary operator. All six read as ordinary `{:op, meta, args}` calls.

`and`, `or` and `not` are language operators: the body lowering rewrites each
into a `case` whose miss arm halts with `BadBooleanError` (non-boolean left
operand of `and`/`or`) or `ArgumentError` (`not` of a non-boolean). The miss arm
stays in the lowered body even where the operand's type is a boolean, as it does
for any exhaustive `case`. `||`, `&&` and `!` are
`Kernel` macros (`lib/kernel.fz`) over `nil`/`false` patterns, so they answer
the deciding value. `and`, `or` and `not` stay legal in guards, where a
non-boolean operand fails the guard as any guard error does; the three guard
evaluators (`ir_interp/dispatch_exec.rs`, `jobs/native.rs`,
`native_codegen/receive.rs`) apply the same strictness.

## Macros in guards

Every guard is expanded with `QuotedExpansionCtx::expand_guard`: the guard of a
function head (`jobs/source.rs`), and the guard of every `when` call the
expander reaches (`case`, `receive` and `fn` clauses). A macro that
expands inside a guard keeps working when its expansion is something dispatch
evaluates (operators, literals, variables, function calls, as decided by
`jobs::is_guard_expr`). Any other expansion is refused at the macro call, in
Elixir's words: ``invalid expression in guard, `||` is not allowed in guards``.
This is the one check; `||`, `&&` and `!` are refused by it because they expand
to a `case`.

A `defmacro` head is an ordinary expression, so an operator head such as
`defmacro left || right` parses the same way as a named head
(`parse_defmacro_head`); `quoted_surface::definable_operator_arity` lists the
operators a module may define.

## `when` and trailing `do` belong to expression grammar

`when` is a reserved operator token, but it is not definition grammar. The
front door's Pratt table is its one binary parse authority: it is
right-associative, weaker than `=` and `::`, and stronger than the comma and
clause boundaries owned by enclosing productions. A guarded definition, case
pattern, `with` pattern, or single-argument anonymous clause therefore receives
the same `{:when, meta, [left, guard]}` expression shape. The anonymous-function
reader only packages the distinct multi-argument clause shape
`{:when, meta, [arg1, ..., guard]}` after the expression parser has parsed the
guard; it does not own `when` precedence. The `when` following an `extern`
return type remains a different production: it introduces type-variable
constraints, not a guard expression.
A comma after that return type begins the other tail, `raises: Alias, message:
"text"` (`parse_extern_raises`), which names the exception a failing extern
raises; see [externs](externs.md).

Anonymous-function clause heads own the boundary immediately before that
guard. `fn -> body end`, `fn pattern -> body end`, and `fn left, right -> body
end` are one parameter-list family; parenthesized heads remain valid. A bare
list continues through commas and stops before clause-level `when` or `->`, so
`fn left, right when left < right -> left end` wraps one guard around both
parameters. This boundary is deliberately distinct from unparenthesized call
arguments, whose ordinary Pratt expression reader may consume `when` as an
infix operator.

A trailing `do ... end` block belongs to the outermost unparenthesized call.
While the parser reads that call's no-parens arguments, nested unmatched calls
may not consume the block; after the arguments are complete, the outer call
appends one fresh `[do: body]` argument. `, do:` remains ordinary keyword-call
syntax: `outer value: 1, do: 42` has one `[value: 1, do: 42]` argument, while
`def head, do: body` has the already-parsed head followed by that keyword-list
argument.

Every matched delimiter reopens local block ownership for its contents and
restores the enclosing suppression when it closes. Thus
`outer(inner() do body end)` and `outer (inner() do body end)` give the block
to `inner`, as do nested calls inside call arguments and container literals;
`outer inner() do body end` gives it to `outer`.

Whitespace also keeps Elixir's call/grouping distinction: `callee(arg)` is a
parenthesized call, while `callee (arg)` is a no-parens call whose first
argument is the grouped expression `(arg)`. This lets an ordinary identifier
macro receive operator heads such as
`def (left :: integer) + (right :: integer), do: left + right` without a
definition-only operand parser.

## Special forms are ordinary calls

`if`, `case`, `cond`, `with`, `receive`, `quote`, and `unquote` are plain
identifiers to the lexer and the frontdoor Pratt parser. Nothing in
`parse_prefix` or `parse_bp_tail` knows their names; each reaches
`finish_call`, `parse_no_parens_args`, and `attach_trailing_do` the same way
any other call does, so all three call spellings work for all of them:
`case x do ... end`, `case x, do: ...`, and `case(x, do: ...)`. A user
`defmacro` gets the identical treatment — a macro call may take a trailing
`do ... end` (with `else`/`after` sections) exactly as `if` or `case` can,
and receives it as the same `[do: ..., else: ..., after: ...]` keyword-list
argument a built-in special form receives. Only `fn`, `do`, `end`, `else`,
`after`, `when`, `not`, `and`, `or`, and `in` stay reserved; a program may
name a variable or function `if`, `case`, or `receive`, matching Elixir.

Shape rules — `case` needing `->` clauses, `if` needing a `do` section, and
so on — are not parser concerns. They live in `quoted_function.rs`'s
`decode_*` functions, which run after macro expansion and see the same
`[do: ..., else: ...]` shape whether the call came from a built-in form, a
user macro, or a manually built `quote`.

`decode_named_expr` only hands a call to one of these decoders once its
shape clears a minimal bar: a trailing keyword-list argument that actually
holds a `do:` entry, and, for the clause-bodied forms (`case`, `cond`,
`receive`), a `do:` value that itself looks like a clause list. A call
named `if`, `case`, `cond`, `with`, `receive`, or `quote` that falls short
of this — the wrong arity, no keyword list at all, or a keyword list
missing `do:` — is not that special form after all, whatever its name, and
decodes as the ordinary call it looks like, the same way `if(true)` (wrong
arity) always has. It then fails later, at lowering, as an unresolved
callee, matching Elixir's own "undefined function" for a same-shaped
mismatch, rather than as a decode error blamed on the special form's
decoder. This shape bar lives once at the dispatch site, not duplicated
inside each decoder.

## One parser for every trailing `do ... end`

`attach_trailing_do` parses every trailing block the same way, through
`parse_do_block`: a `do` section, an optional `else` section, and an
optional `after` section, each ending at the next section keyword or `end`.
Each section is decided independently by `parse_do_section`, using the same
rule Elixir uses: parse the section's first statement, then look for a
following `->`. Finding one turns the whole section into a list of
`pattern -> body` clauses (`finish_clause_list`, which hands them to the
one clause-list reader below); anything else makes it an
ordinary block, wrapping more than one statement in `__block__`. This one
rule is what lets `if`, `case`, `cond`, `with`, and `receive` share a single
do-block reader despite each wanting a different section shape — `case`'s
`do` is always clause-shaped because its first statement is always a
pattern followed by `->`, while `if`'s `do` is always block-shaped because
it never is. A parenthesized grouping `(...)` gets the same clause check
when it holds one bare clause, e.g. `case(1, do: (1 -> 1))`.

## One clause-list reader

`fn`, the clause-shaped do-sections (`case`, `cond`, `receive`,
`with ... else`) and the parenthesized `(a -> b)` form all read their clauses
through `parse_clause_list`. Only the head differs: `fn` heads are parameter
lists (`parse_param_head`), the others are one pattern expression.

A clause body may span several lines, and Elixir's rule decides which lines
belong to which clause: a line starts a new clause only when it is itself
`head ->`; every other line joins the body of the clause above it. A body of
one line stays a bare expression, and a body of several is a `__block__`,
built by `parse_block_lines`, the same reader that builds every other block.

Each line is read once and classified by the token that follows it
(`parse_clause_line`). A pattern line is a head exactly when `->` follows it.
A parameter line is a head when `,`, `when` or `->` follows its first
expression, or when it opens with a parenthesis group followed by `when` or
`->`; no body line can continue that way. The first clause of a list is
always a head, so a plain line before it keeps the head's own error. A line
that is neither a body line nor a head is reported where it ends, and two
clauses on one line are reported as a missing newline.

## A no-parens call's own comma is not always its own

`parse_no_parens_args` stops at a comma when `comma_bound` is set, so that
`f(a, b)`'s no-parens-call argument `b` cannot swallow the comma that
belongs to `f`'s own argument list. This flag is inherited through ordinary
expression parsing, so an argument, list/tuple/map element, or keyword-entry
value is comma-bound by the outer construct that contains it. Anything with
its *own* unambiguous close token — a grouping `(...)`,
an anonymous-function clause body, or a `do ... end` block — resets it with
`with_comma_unbound` on entry: nothing inside can be mistaken for a sibling
of whatever comma-separated list happens to contain it, so a bare `if cond,
do: a, else: b` works as a lambda's clause body or inside a `do` block even
when that lambda or block is itself one comma-separated argument or tuple
element. A bare no-parens call used directly as a list, tuple, or call-argument
*element* still needs parentheses around its own `do:`/`else:` tail, matching
Elixir: `{:cont, if(x, do: a, else: b)}`, not `{:cont, if x, do: a, else: b}`.

## String escapes

Strings, heredocs, quoted atoms and character literals read escapes with one
function, `Lexer::read_escape`, which returns the character an escape denotes;
a string appends its UTF-8 encoding. The escapes are `\n \t \r \s \0 \a \b \d \e
\f \v \\ \" \' \#` and the two unicode forms: `\uHHHH` (exactly four hex digits)
and `\u{H...}` (one to six). `"caf\u00e9"` and `"caf\u{e9}"` are both `"café"`,
and `"\u{1F600}"` is four bytes. A malformed form (`\u`, `\u12`, `\u{}`,
`\u{41`, seven digits) reports `invalid Unicode escape character, expected
\uHHHH or \u{H*}` and a surrogate or a value above `10FFFF` reports `invalid or
reserved Unicode code point`; both underline the escape from its backslash.
Any other escaped character is an `unknown escape` error, where Elixir would
take it literally. A combining character can be written as an escape
(`"e\u0301"`) instead of as bytes.

## Character literals

`?` starts a character literal, a `Tok::Int` holding the code point of the
one character or escape after it: `?a` is 97, `?é` is 233, `?😀` is 128512,
`??` is 63, `?\n` is 10, `?\s` is 32, `?\\` is 92. The escapes are the shared
ones above except the unicode forms: `?\u` is an error, as in Elixir, where the
character is written itself. Whitespace right after the `?` (space, tab,
newline, carriage return) is an error naming the escape to write, where Elixir
accepts it with a warning. A `?` at the end of input is an error. A name that
ends in `?` keeps it (`ready? ?a` is a name and a literal), because names are
read before a `?` can start a token. A combining mark after a literal is a
separate, unexpected character.

## Heredocs are string literals

`"""` opens a heredoc, which lexes to a single `Tok::Binary` holding its lines
with the closing delimiter's indentation stripped. It is a string LITERAL, not
a raw string, so it carries both of a literal's behaviours:

- **Escapes are processed.** Source `one\"two` stores `one"two`. A lone `"`
  needs no escape, since only `"""` terminates the heredoc, so a backslash that
  should survive into the text has to be doubled: `"{\\"a\\": 1}"` in the source
  stores `"{\"a\": 1}"`.
- **Interpolation runs.** `"a#{1 + 1}b"` inside a heredoc stores `a2b`.
  `\#{x}` suppresses it and stores `#{x}`; `dbg` re-escapes a literal `#{` when
  it renders, so a round trip looks doubled and is not.

Both apply to `@doc """ ... """` and `@moduledoc """ ... """`, which take the
same string token. Documentation that quotes fz syntax is therefore executable
text: a doc explaining interpolation contains `#{...}` and will interpolate it,
and an unbound name there currently changes what the module compiles to without
reporting anything (fz-5xp.96). Escape the sigil in prose that describes it.

## Captures

`parse_capture_expr` reads `&` as a prefix operator with one operand. Only
two spellings are not expressions and are read from tokens: `&N` with no
space before the integer (the capture argument), and `&op/N` for an operator
such as `&+/2` (`parse_operator_capture`). Every other operand is parsed by
`parse_bp(CAPTURE_OPERAND_BP)`, bp 5: tighter than `when` (4) and `<-` (2),
and including `=` and every binary operator, `/` among them. So
`&Mod.f/1` and `&name/1` come out as `(& [(/ [target, arity])])`, while
`& &1.f`, `&{&1, &2}`, `&[&1]`, `&"#{&1}"` and `&(&1 + 1)` come out as `&`
around the body. The parser does not decide between function reference and
body; `rewrite_capture` in `source_sugar.rs` does, via
`is_function_ref_payload`.
