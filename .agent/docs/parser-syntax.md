# Parser Syntax Model

`src/parser` turns tokens into the `ast::Expr` / `ast::Item` tree. Its job is to
mirror Elixir's surface syntax while keeping the tree ordinary: keyword lists are
plain lists of two-tuples, do-blocks are sugar for a trailing `do:` keyword entry,
and the parser introduces no keyword-list node and no runtime keyword type. That
policy is what lets the rest of the compiler stay simple.

There are now two source paths:

- The legacy parser/frontend path rewrites the Elixir-flavored operators
  (`++`, `<>`, `..`), captures, and multi-clause `fn` in the frontend desugar
  pass (`src/frontend/macros.rs`) before old IR lowering.
- The compiler2 quoted-source path quotes those forms as Fz-shaped source data
  first, then normalizes them during staged demanded-function expansion
  (`src/compiler2/source_sugar.rs`) after raw `FunctionSource` publication and
  before `DefineFunction` decodes the body.

Three files carry the work:

- `items.rs` — top-level and module-body items: `fn`/`fnp`/`defmacro` clauses,
  `defmodule`/`defstruct`/`defprotocol`/`defimpl`, `alias`/`import`, `extern`,
  and `@`-attributes (`@doc`, `@moduledoc`, `@type`, `@spec`).
- `expressions.rs` — the Pratt expression parser (`parse_bp`), call forms,
  keyword lists, do-block sugar, lambdas, captures.
- `patterns.rs` — patterns (shared by `case`, lambda heads, `=`, list/map/struct
  literals).

`mod.rs` owns the `Parser` state, the token helpers, and the program entry points.

## Parser State

`Parser` threads three context flags that surrounding constructs set and inner
parses read:

- `suppress_trailing_do` — when true, `parse_bp` does not attach a trailing
  `do … end` to a call. The cond-position forms (`if`/`case`/`cond`/`with`
  scrutinees and `when` guards) set it via `with_no_trailing_do`, so
  `if pred(h) do … end` parses `pred(h)` as the condition and leaves the block
  to `if`.
- `comma_bound` — true while parsing one element of a comma-delimited container
  (list, tuple, map, bitstring, paren call args). A no-parens call recognized in
  that state takes a single argument and leaves the comma to the container.
  `with_comma_bound` / `with_comma_unbound` flip it; blocks, lambda bodies, and
  parenthesized groupings reset it to false.
- `saw_no_parens_call` — set by the no-parens-call site, read by the keyword-list
  parser. The AST does not record parens-vs-no-parens (`bar x` and `bar(x)` are
  the same `Call`), so this transient flag carries that distinction to the
  ambiguity check.

Non-fatal diagnostics collect in `warnings` and surface through
`parse_program(tel)`, which emits each one as a `[fz, diag, warning]` event.
There is no plain parser entry point that drops warning telemetry.

## Function Items

`fn` declares a function; `fnp` declares a module-private one. Both parse the
same clause shape through `parse_fn_clause` and accumulate into one `FnDef` per
name/arity (`items.rs` groups clauses by `(name, arity)`). The only difference is
`FnDef.is_private`: `fn` sets it false, `fnp` sets it true. A name/arity that
mixes `fn` and `fnp` clauses (or `fn` and `defmacro`) is a parse error — the
group's flag must be consistent.

A module's interface export is an `Item::Fn` that is not a macro, not private,
not `extern`, and not the implicit `__info__/1` builtin
(`src/modules/interface.rs`). So `fn` inside a `defmodule` enters the interface
and, under strict interface validation, must carry an `@spec`
(`public export … requires an explicit @spec`); `fnp` stays callable from its
own module but is omitted from the interface and skips that check.

A function head is normally `name(params)`. An operator in head position selects
the infix form: `fn left + right` declares the function named `+` with two
params. The same operator-head rule applies to `@spec` (`@spec integer + integer
:: integer`).

## Keyword Lists

`Tok::KwKey(name)` is the lexer token for `name:`. The parser consumes keyword
entries only where they can appear:

- list literals: `[a: 1, b: 2]`
- call arguments: `f(x, a: 1, b: 2)`
- call-postfix block sugar: `f(x) do … end`
- list-pattern / keyword-list heads: `[do: body]`

That means compiler2 accepts both source spellings Elixir uses for block-taking
macro heads:

- `defmacro m(arg, do: body)`
- `defmacro m(arg, [do: body])`

A keyword entry is ordinary data — a two-element tuple of the key atom and the
value, collected into a plain list. `Expr::List` carries `(elements, tail)`, and
keyword lists never use the cons tail:

```text
[a: 1, b: 2]
=> Expr::List(
     [ Expr::Tuple([Expr::Atom("a"), Expr::Int(1)]),
       Expr::Tuple([Expr::Atom("b"), Expr::Int(2)]) ],
     None,
   )
```

Calls collect trailing keyword entries into one final list argument. A trailing
`do … end` block appends a `do:` pair to that same final list (`attach_trailing_do`
extends the collapsed keyword argument, or makes one), so
`f(x, timeout: 10) do 42 end` has the call shape `f(x, [timeout: 10, do: 42])`.
A bare `do … end` on a block-positional literal stays separate: `f [a: 1] do … end`
keeps `[a: 1]` positional and adds a distinct `[do: …]`, matching Elixir.

This matches Elixir's user-facing model without adding a keyword-list AST node or
runtime type.

The `keyword` type is an ordinary alias in the runtime prelude
(`src/modules/runtime_library/runtime.fz`):

```text
@type keyword() :: [{atom, any}]
@type keyword(t) :: [{atom, t}]
```

## Named vs Anonymous Calls

A named call and an anonymous-function call are different syntax forms with
different AST nodes:

```text
count(1)     => Expr::Call(target, args)
count.(1)    => Expr::ClosureCall(target, args)
```

The ordinary `.` postfix keeps its field/index meaning (`m.k` lowers to an
atom-keyed `Expr::Index`); only `.(...)` is the closure-call operator. A bare
`count(1)` resolves by name; to call the value bound to `count`, source must
write `count.(…)`. Keeping the forms distinct means the resolver never has to
guess between "named function" and "local value of the same name".

## Record Type Expressions

`@type` bodies can give field types for a struct schema with record syntax:

```text
@type t :: %Range{first: integer, last: integer, step: integer}
```

The parser stores the body as raw type-expression tokens; `type_expr`
(`parse_struct_record_type`, building a `StructRecordType`) resolves them during
module type-env construction. `collect_struct_field_types`
(`src/frontend/resolve.rs`) then validates the record against the struct's
`defstruct` schema as a set — every record field must exist on the struct, and
every struct field must be present — and stores the result keyed by struct
module. The stored field order is the order written in the record type. This
gives later typing passes one schema fact to consume instead of reparsing
aliases or inferring field types from constructor sites.

## No-Parens Calls

A call may omit its parentheses: `double 21`, `Enum.map xs, f`. `parse_bp`
recognizes one when a **callable head** — a bare name or a module-qualified path,
i.e. `Expr::Var` or the `Expr::Index` that `Mod.fun` lowers to — is followed by a
token that **starts an argument**: separated from the head by spacing, and a
value token rather than an operator, container close, or block keyword. `(` and
`[` are excluded — the postfix loop owns them as paren-call and index. `+`/`-`
count only when unary-positioned (space before the operator, none before its
operand), so `foo -1` is the argument `-1` while `foo - 1` is subtraction.

Arguments are full expressions, so a nested no-parens call owns its own commas:
`f g a, b` is `f(g(a, b))`. Comma greediness depends on the `comma_bound` flag:

- At statement/operand position, arguments are comma-separated greedily.
- Inside a comma-delimited container, a no-parens call takes a single argument
  and leaves the comma to the container: `[foo a, b]` is `[foo(a), b]`.

Keyword entries collapse the same way as in paren'd calls. Trailing `key: value`
pairs become one final keyword-list argument, and a keyword key in head position
makes the whole argument list a lone keyword list:

```text
foo a, b: 1, c: 2   =>  foo(a, [b: 1, c: 2])
foo b: 1            =>  foo([b: 1])
```

### Policy: no-parens keyword as a keyword value

When a no-parens call is itself a keyword value and another keyword entry follows
it, the parse is ambiguous — `b: bar x, c: 2` could fold `c: 2` into `bar` or
leave it in the outer list. fz keeps the trailing keyword in the outer list
(`bar(x)` plus `c: 2`); Elixir folds it into the inner call. The choice is fixed
and observable: the parser emits a `parse/ambiguous-no-parens-keyword`
(`PARSE_AMBIGUOUS_NO_PARENS_KEYWORD`) warning to telemetry under
`[fz, diag, warning]`, so the divergence shows up and the source can be
disambiguated with explicit parentheses.

## Anonymous Functions

`fn` introduces an anonymous function as a non-empty list of clauses, terminated
by `end`:

```text
fn x -> x + 1 end
fn (a, b) -> a + b end
fn 0 -> :zero
   n -> n end
fn x when x > 0 -> x
   _ -> 0 end
```

The `end` is required — a multi-clause body has no boundary without it. Clause
structure matches `case` (a pattern list, an optional `when` guard, `->`, a
body), so `parse_lambda` and `parse_case` stay in lockstep. The AST is
`Expr::Lambda(Vec<LambdaClause>)`; each `LambdaClause` carries `params`, an
optional `guard`, a `body`, and its span.

`lambda_direct_clause` names the one shape the legacy interpreter and old IR
lowering run directly: exactly one clause with no guard. Every other legacy
shape is desugared first (below). Compiler2 quoted source keeps the raw lambda
source until source publication, then rewrites multi/guarded anonymous functions
into a single direct lambda whose body is a `case`.

## Captures

`&` introduces one of three forms, disambiguated by the single token after it:

```text
&N            => Expr::CaptureArg(N)      (an adjacent integer >= 1)
&(...)        => Expr::Capture(body)      (a parenthesized body)
&name/arity   => Expr::FnRef { name, arity }
&+/2          => Expr::FnRef { name: "+", arity: 2 }
&Kernel.+/2   => Expr::FnRef { name: "Kernel.+", arity: 2 }
```

`&N` requires the integer adjacent (no space) so `&1` is a placeholder while
`& 1` is not. `&(...)` parses its body as a fresh operand context, so the body's
own `&N` placeholders and nested calls come along. The function-reference form
accepts ordinary names, dotted names, `lib::extern` names, and operator-headed
functions. Division is spelled `&//2` or `&Kernel.//2`: the operator `/` followed
by the arity separator `/` lexes as `//`, which `parse_fn_ref_name_part` reads as
the operator name `/` plus a consumed slash.

The unparenthesized capture-of-call form `&Mod.fun(&1, &2)` is not parsed: after
`&name` the parser requires `/arity`.

Compiler2 frontdoor source quotes captures as ordinary `&` forms: adjacent
`&N` is `{:&, meta, [N]}`, `&(...)` is `{:&, meta, [body]}`, and function refs
remain `&name/arity` payloads. Source publication rewrites placeholders and
capture bodies into direct lambdas before body lowering, while preserving
function-reference captures as refs.

## Source Sugar Rewrites

The old frontend path and compiler2 source-publication path intentionally erase
the same user-facing sugars before executable lowering. In the legacy path,
`Expr::Capture` and `Expr::CaptureArg` have no runtime meaning on their own; the
interpreter (`src/exec/eval.rs`) and IR lowering (`src/ir_lower/expr.rs`) reject
them if they survive. `src/frontend/macros.rs` rewrites them, and the
Elixir-flavored operators, before old lowering. In compiler2, the same rewrite
policy lives in `src/compiler2/source_sugar.rs` and runs on quoted source before
`FunctionSource` publication:

- `&(… &N …)` becomes a `Lambda` whose params are `__fz_capture_arg_1..N` (N is
  the highest placeholder in the body) and whose body is the capture body with
  each `&N` replaced by the matching param.
- a bare `&N` becomes an N-parameter lambda returning its Nth parameter, so `&1`
  is the identity lambda.
- a guarded or multi-clause `Lambda` becomes a single direct lambda whose body is
  a `case` over synthetic params (`__fz_lambda_arg_i`), reusing the existing
  pattern-matrix dispatch. The clause patterns become the `case` clauses.
- the operators rewrite to ordinary calls:

```text
a ++ b       => List.concat(a, b)
a -- b       => List.subtract(a, b)
a <> b       => Kernel.fz_binary_concat(a, b)
a..b         => Range.new(a, b, 1)
a..b//step   => Range.new(a, b, step)
```

The `List` helpers are ordinary source functions in
`src/modules/runtime_library/list.fz`. `<>` is the one backed by a primitive: an
`extern "C"` `Kernel.fz_binary_concat` (`runtime/src/ir_runtime.rs`), because it
must allocate a binary. Range construction runs through the source `defstruct`
path (`Range.new` builds a `%Range{}`).

## Boundaries

Special forms (`if`, `with`, `quote`, …) own their own `do:` parsing paths.
Ordinary call keyword parsing runs inside those forms only after their special
parsers have set `suppress_trailing_do`, so a call's trailing-do sugar never
swallows a block the surrounding form expects.

Keyword entries are trailing. Once a call or list literal starts parsing keyword
entries, a following positional expression is a syntax error.

## Where it's proven

Parser behavior lives in `src/parser/parser_test.rs`, organized by feature into
submodules: `do_block_sugar_tests`, `no_parens_call_tests`,
`no_parens_keyword_ambiguity_tests`, `lambda_tests`, `capture_tests`. The
named-vs-anonymous call rule and bare-call resolution are covered in
`src/exec/eval.rs` tests; the `fnp` interface rule in
`src/modules/interface_test.rs`. End-to-end behavior across the four execution
paths runs through the fixture corpus (`fixtures/keyword_lists`,
`no_parens_call`, `no_parens_do`, `no_parens_keyword`) under
`tests/fixture_matrix.rs`.
