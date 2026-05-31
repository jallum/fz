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

The parser currently rejects adjacent multiple `@spec` declarations for one
function. That restriction is only the first visible failure; downstream code
also has single-spec assumptions.

Known single-spec sites:

- `src/parser/items.rs`: rejects a second pending `Attribute::Spec` before a
  function and has a regression named `multiple_spec_on_one_fn_errors`.
- `src/frontend/spec_check.rs`: uses `find_map(Attribute::Spec)` and validates
  inferred specs against one resolved arrow.
- `src/modules/interface.rs`: `InterfaceFn.spec` and protocol callback
  interface specs hold one `InterfaceSpec`.
- `src/frontend/protocols.rs` and `src/frontend/resolve.rs`: protocol callback
  facts and impl callback-spec compatibility use one spec per `(name, arity)`.
- `src/ir_lower/mod.rs`: `Module.declared_specs` is populated from the first
  spec only.
- `src/fz_ir/mod.rs`: `Module.declared_specs` is
  `HashMap<FnId, ResolvedSpec>`.
- `src/ir_planner/walk.rs`, `src/ir_planner/worklist.rs`, and
  `src/ir_codegen/driver.rs`: declared-call input and return typing read one
  declared arrow.
- `src/exec/eval.rs`: REPL/help spec rendering formats one spec line.

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

4. Declared-call typing: change `Module.declared_specs` to store a resolved set.
   For call inputs, choose declared arrows whose params are compatible with the
   call arguments; for return typing, instantiate the matching arrow result. If
   several arrows remain possible, union those matched results only after arrow
   selection.

5. Interfaces and protocols: change public function specs and protocol callback
   specs to carry ordered spec lists. Fingerprint rendering must include every
   arrow in deterministic order. Protocol impl compatibility should compare
   overload sets by coverage, not by one optional callback spec.

6. REPL/help rendering: render all arrows, one per line, instead of silently
   dropping all but the first.

7. Acceptance fixture: unblock `Enum.with_index/2`'s function overload by
   restoring the honest two-`@spec` form and adding the function-overload case
   to `fixtures/enum_map_family`.
