# Specs

`@spec` declarations are function contracts. A single declaration is one arrow:

```fz
@spec f(integer) :: integer
```

Some functions need an overload set: several arrows for the same name and arity,
where each arrow preserves its own input-to-output correlation.

```fz
@spec with_index(Enumerable.t(a), integer) :: [{a, integer}]
@spec with_index(Enumerable.t(a), (a, integer) -> b) :: [b]
fn with_index(enumerable, fun_or_offset)
```

Do not collapse that into parameter and result unions. This shape:

```fz
@spec with_index(Enumerable.t(a), integer | ((a, integer) -> b)) ::
  [{a, integer}] | [b]
```

answers a different question: it permits the integer input arrow to return
`[b]`, and permits the function input arrow to return `[{a, integer}]`. The
whole point of overload specs is preserving the relationship between one
accepted input shape and its result shape.

## Current Problem

Multiple adjacent `@spec` declarations now parse and lower into a
`ResolvedSpecSet`, but each downstream consumer still has to preserve the
arrow set. Any consumer that asks for “the one declared spec” is wrong for
overloads because it either drops valid arrows or tempts callers into parameter
and result unions that lose correlation.

Known single-spec sites:

- `src/parser/items.rs`: accepts adjacent matching specs and attaches them in
  order to the following function.
- `src/frontend/spec_check.rs`: validates every inferred narrow spec against
  the declared arrow set.
- `src/modules/interface.rs`: `InterfaceFn.spec` and protocol callback
  interface specs hold one `InterfaceSpec`.
- `src/frontend/protocols.rs` and `src/frontend/resolve.rs`: protocol callback
  facts and impl callback-spec compatibility use one spec per `(name, arity)`.
- `src/ir_lower/mod.rs`: `Module.declared_specs` stores resolved spec sets.
- `src/fz_ir/mod.rs`: `Module.declared_specs` is
  `HashMap<FnId, ResolvedSpecSet>`.
- `src/ir_planner/walk.rs`, `src/ir_planner/worklist.rs`, and
  `src/ir_codegen/driver.rs`: declared-call typing must select compatible
  arrows before reading params or results.
- `src/exec/eval.rs`: REPL/help spec rendering formats one spec line.

## Higher-Order Witnesses

Declared spec instantiation is evidence-driven. For a first-order argument, the
argument type itself is the witness. For a higher-order argument, a closure
literal has two facts:

- it is a closure value with target/capture identity;
- when called at a particular argument key, the planner may know an effective
  return for that target.

Those are not the same fact. `src/ir_planner/spec_witness.rs` keeps them
separate: it first instantiates the declared arrow from ordinary argument
witnesses, then derives additional arrow evidence for closure-literal
parameters from the closure target's effective return key. If that return key is
not known yet, the caller records a return-read and the worklist revisits the
caller when the closure return changes.

This is what makes specs such as:

```fz
@spec reduce_while(Enumerable.t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: b
```

data-flow correctly. The initial accumulator is one witness for `b`; the
reducer's `{:cont, b}` / `{:halt, b}` exits are another witness. The declared
result must join both instead of freezing `b` to the initial accumulator shape.

The declared scheme also names which callback positions participate in that
fixed point. `ResolvedSpec::higher_order_invariant_groups` reports the type
variables whose occurrences cross from outer params/results into callback
arg/result positions. For `reduce/3`, the loop-carried group is `b`:

```text
Param(1)          outer accumulator
Result            outer result
CallbackArg(2, 1) reducer accumulator arg
CallbackResult(2) reducer result
```

That correspondence is the planner-facing fact used to stabilize higher-order
callback keying; it is not a post-hoc widening heuristic.

## Correct Shape

Add a first-class overload-set shape:

```rust
struct SpecSet {
    arrows: Vec<SpecDecl>,
}

struct ResolvedSpecSet {
    arrows: Vec<ResolvedSpec>,
}
```

The exact Rust names can follow local style, but the semantic invariant should
hold everywhere:

- one `FnDef` can carry several `@spec` arrows for the same name and arity;
- each arrow resolves type variables and constraints independently;
- validators and planners select or quantify over arrows without unioning
  unrelated parameter and result positions;
- interface and artifact formats preserve every arrow deterministically.

## Plan

1. Parser and AST: remove the duplicate-`@spec` rejection, keep all adjacent
   matching `@spec`s attached to the following `FnDef`, and keep name/arity
   checks per spec. Replace the negative duplicate-spec test with a parse test
   that proves two specs attach in order.

2. Type-expression layer: add helpers to resolve all specs on a `FnDef` into a
   `ResolvedSpecSet`. Do not share type-variable substitutions across different
   arrows.

3. Spec validation: for each inferred narrow spec, find at least one declared
   arrow whose instantiated params accept the inferred inputs and whose
   instantiated result accepts the inferred result. Report a violation only when
   no declared arrow covers that inferred behavior. Keep any-key inferred specs
   skipped.

4. Declared-call typing: `ResolvedSpecSet` owns arrow selection. For call
   inputs, use a selected arrow's instantiated params only when the call picks a
   unique arrow; otherwise keep the concrete call arguments as the demand. For
   return typing, instantiate and union the matched results only after arrow
   selection. Instantiation uses the shared structural scheme matcher: variables
   can be witnessed by compatible nested shapes such as higher-order callback
   arrows, and partial/underconstrained results are not executable return facts.
   The matcher returns instantiated params and result together so demand shaping,
   declared-call return typing, and spec validation cannot drift into separate
   substitution stories. Validation passes positional holes as unknown witness
   slots rather than converting them to `any`.

5. Interfaces and protocols: public function specs and protocol callback specs
   carry ordered spec lists (`specs`), and interface fingerprints include every
   arrow in source order. Protocol impl compatibility compares overload sets by
   checking each impl arrow against the protocol arrow set, not by picking one
   optional callback spec.

6. REPL/help rendering: `?<name>` renders every resolvable declared arrow, one
   `@spec:` line per arrow, instead of silently dropping all but the first.

7. Acceptance fixture: `Enum.with_index/2` uses the honest two-`@spec` form,
   and `fixtures/enum_map_family` covers the function-mapper overload with
   several result shapes so overload selection must preserve input/result
   correlation.
