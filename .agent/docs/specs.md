# Specs

`src/specs` is no longer a spec semantic engine. It is the shared structural
shape model used by compiler2 while resolving source-level type syntax.

The retained API is intentionally small:

- `ResolvedTypeShape` mirrors source type structure: scalar leaves, literals,
  variables, named type applications, resources, lists, tuples, arrows, unions,
  and struct records.
- `ResolvedStructFieldShape` carries struct-record field names and field shapes.

Compiler2 owns the active contract path:

- `compiler2/type_expr.rs` parses type syntax without consulting the old
  `ModuleTypeEnv`.
- `compiler2/resolve.rs` resolves names against the namespace captured where a
  declaration appeared and returns hard compiler2 `Ty` values plus parallel
  `ResolvedTypeShape` values.
- `compiler2/contract.rs` and the compiler2 type/arrow-matching code consume the
  resolved contract data.
- `Types::close_bounds` is the shared addressed-`TypeVarId` resolver for `when`
  dependencies. It closes only ground acyclic RHS chains; unresolved and cyclic
  components remain symbolic. Contract matching and declared input domains both
  use this one interpretation.
- `FunctionContract` stores resolved protocol-domain marker obligations per
  arrow. The current obligation identity is the resolved protocol's
  `ModuleName`, wrapped as a `ProtocolDomainObligation`; it is
  classified from explicit positive markers in hard `Ty` values plus the
  contract bounds sidecar, not from source refs, negative/complement clauses, or
  protocol impl registries. Protocol-domain arrows can still refine calls, but
  arrows with obligations are skipped for fatal
  `spec/violation` decisions until protocol-domain validation is implemented;
  concrete arrows in the same overload set remain enforceable.
- A call's open inputs are instantiated by each matched arrow's STRUCTURAL
  SURFACE (`ContractArrow::structural`, `Types::structural_surface`): the
  arrow's parameters and bounds with every protocol-domain marker read as `any`,
  the reading the runtime type predicate gives the marker.
  `FunctionContract::apply` returns `matched_arrows` from that surface, and
  `instantiate_open_inputs` (`compiler2/jobs/semantic.rs`) intersects it only
  with a column whose observed type still carries type variables: evidence in
  flight, such as an unannotated lambda's `fp[va0] a0`. That is how a contract
  tells a callable argument what it will be called with: `make_resource(42,
  fn x -> ... end)` keys the lambda on the integer its `(t) -> nil` parameter
  instantiates to. Obligations, enforceability and diagnostics keep reading the
  declared arrow.
- A GROUND column is what the caller has and is never rewritten, whether it is
  `any`, `int | nil` or `int`: the contract answers the call's verdict and
  return, and the callee is keyed on the observed type. A caller that holds
  `any` therefore keys its callee under `any`, whatever the callee's `@spec`
  lists, so the callee's dispatch plan keeps its arm of last resort and a value
  outside every clause raises `FunctionClauseError`. The plan's arm of last
  resort goes only where the caller's own types prove nothing can miss
  (`a_spec_does_not_narrow_the_any_a_caller_holds_into_its_callees_key`,
  `a_caller_that_knows_its_argument_still_trims_the_callees_arm_of_last_resort`
  in `compiler2/jobs/semantic_test.rs`; fixtures `00740` and `00749`). A value
  typed only at runtime (a decoded JSON list) reaches
  `Enum.count(Enumerable.t(a))` as `any` and dispatches on the protocol at
  runtime. A ground column partly outside a clause's domain (`int | nil` into
  an `integer` parameter) is answered on the part inside the domain (below),
  and the matched arrow's parameters instantiate only a column still carrying
  type variables, so the ground column is not refined.
- Arrow matching (`Types::match_arrow`) handles union parameters structurally:
  a union of tuples with DIFFERENT arities matches a witness against the
  alternative of the witness's own width, and a kind collector (tuple, list,
  resource, map, arrow) vetoes a signature unless the witness intersects the
  pattern with that kind's component cleared (`witness_escapes_kind`) — a
  cross-kind union like `:first | {:acc, a}` accepts `:first` through its
  atom member but still rejects `:third`, which no member accepts.
- A call is refused only when its argument row is proven to fail: it fits no
  clause of the contract. `FunctionContract::apply` asks each clause in two
  steps: `ContractArrow::narrowed_row` is the one place a witness is narrowed
  to a clause's domain (before the walk), then `Types::match_arrow` runs on the
  narrowed row, then `FunctionContract::admits_instantiated_clause` is the one
  place admission is decided, on the clause as the walk instantiated it.
  - Narrowing: every ground column is narrowed to the clause's domain
    (`Types::clause_domain_at_every_instantiation`,
    `Types::narrow_to_clause_domain`), so the clause answers for the part of the
    call that overlaps it. A clause variable is read as the union over every
    instantiation of it (`Types::clause_domain_envelope`): its closed bound (or
    `any` when it has none) where it occurs covariantly, `none` under an
    arrow's parameter, so `(t) -> nil` reads as `(none) -> nil`, the
    arrow every instantiation's callable fits. `{binary, int} | {int, int}` into
    `pick({integer, a})` narrows
    to `{int, int}` and binds `a := int`. A column disjoint from the domain
    refuses the clause. A witness that still carries type variables is evidence
    in flight and passes unchanged.
  - `any` is the widest overlap: it means the call site does not know the
    argument's type, the way Elixir reads a `dynamic()` argument. It narrows to
    the domain like any other witness, so `resource(t)` applied to a handle typed
    `any` answers on the resource domain, and the callee is still keyed on the
    `any` the caller holds (above).
  - Admission, function: a function tests its clauses at run time, so a value
    outside the domain meets the callee's arm of last resort
    (`FunctionClauseError`, or the default clause of Kernel arithmetic raising
    `ArithmeticError`); `integer | :weird` into an `integer` parameter is
    accepted. The tests cannot see a brand (typing is brand-aware, the runtime
    is not), so the part of the witness the runtime would let in must lie inside
    the instantiated parameter: `witness ∩ runtime_reading(param) ⊆ param`, where
    `Types::runtime_reading` erases brands at any depth. `binary` into `utf8` is
    refused; `utf8` into `utf8` fits.
  - Admission, extern: an extern is a raw machine call with no clause tests
    (`FunctionContract::extern_wire` is set), so a column other than `any` must
    fit its instantiated parameter whole: `witness ⊆ param`. The judgement is on
    the instantiated clause because the domain envelope reads a variable under
    an arrow's parameter as `none`, which erases what the parameter constrained:
    with `t := int`, `(int) -> binary` against `(t) -> nil` is refused. A column
    whose parameter still carries variables passes. `any` is narrowed for an
    extern too.
  - A call with an uninhabited column cannot be made; it is never refused and
    answers nothing.
  - Result: the union, over the clauses that matched, of each clause's result
    on its narrowed row. `(int | float, int)` against `+/2` takes `int` from the
    `(int, int)` clause and `float` from the `(float, int)` clause and answers
    `int | float`; no separate coverage pass exists
    (`fixtures2/behavior/spec_polymorphic_clause_set_coverage.fz`).
- A variadic extern's contract carries a tail domain alongside its fixed
  parameters: the type every argument past the declared prefix must belong
  to (`extern_contract::variadic_tail_domain`). `FunctionContract::apply`
  widens the clause's parameter list by repeating the tail domain to the
  observed row's length before calling `match_arrow`, so a longer row is not
  an arity mismatch; a row shorter than the fixed prefix still is. A
  rejected row's diagnostic renders the same widened row
  (`FunctionContract::matched_domain_rows`, reusing
  `ContractArrow::matched_params`): the fixed positions named individually,
  then the tail's one type named once and marked `...`, e.g.
  `(binary, ...int | pid | reference | c_pointer | binary)`.
- Arrow matching is polarity-aware. A `@spec` variable collects LOWER bounds
  from its covariant occurrences (list element, tuple field, map field, resource
  payload, arrow result) and UPPER bounds from its contravariant ones (under an
  arrow's parameters). The instantiation is the JOIN of the lowers and nothing
  else — an upper bound never instantiates anything, so an `any`-typed predicate
  parameter in `filter`/`reject` does not widen the element type, and a variable
  in a contravariant result publishes its lower bound rather than an unsound
  `any`. The MEET of the uppers is the solvability CHECK: `join(lowers) ⊆
  meet(uppers)` is a necessary condition (over the variables both bounds reached,
  over observed lowers, before bound closure) for a solution to exist. A variable
  with only upper bounds stays free (`Underconstrained`).
- A contract RESULT is a fact only when the joins behind its variables are
  finished. A lower bound is the join of a variable's covariant occurrences;
  where the walk reaches a NODE it cannot read — the witness carries variables,
  or names no structure of the pattern's kind — every covariant variable beneath
  it is owed a term it did not get, and what `Sigma` holds is a PARTIAL join.
  (The unit is the node's merged outcome, not the individual occurrence; see
  [`addressed-arrow`](addressed-arrow.md) for the two collectors that skip an
  occurrence without marking it.) The parameter surface still refines from it
  (it is a sound lower bound), but the verdict is `Underconstrained`, so
  `FunctionContract::apply` publishes no result for that clause. `reduce_cont`'s
  accumulator variable occurs at the SEED and inside the reducer arrow's RESULT;
  `Enumerable` hands the reducer over as a bare address var, so a `[]`-seeded
  fold over `[int]` reads the seed alone and `{:done, []}` would be a claim that
  the fold returns what it started with. A variable the walk observed NOWHERE
  keeps its fact: it never enters `Sigma` and `close_bounds` fills it from its
  declared bound (`@spec f(integer) :: a when a: binary` is `Known binary`).
- The empty list gets no rule of its own. Through a list pattern `[]` reads its
  element as `none`, the bottom lower bound, which the join absorbs — so
  `([a], [a])` at `([int], [])` is `[int]` — and at a bare variable it is the
  whole argument, which is a fact: `@spec dbg(t) :: t when t: any` applied to
  `[]` publishes `[]`, not the declared `any`. The fz-f98.16 cleaner that used
  to drop `[]`-pinned bindings per position is gone (fz-kdt.120); it split those
  two shapes apart and it masked the partial join above, since dropping a
  `{:done, []}` rung's binding suppressed the claim without saying why it was
  wrong.
- An extern activation's return evidence is its `FunctionContract` applied to
  the activation's row, set directly rather than refined against a body
  observation: an extern has no body to observe, so its declaration is the
  only witness of what it returns. When the contract cannot answer for that
  row (`Underconstrained`, or the row falls outside its domain and is not
  itself a fatal violation) the evidence stays not-yet-known and the
  activation waits, rather than seeding a placeholder that outlives its own
  refinement (`compiler2/jobs/semantic.rs`; see
  [`semantic-authorities`](semantic-authorities.md), "what does an activation
  return"). `LoweredExtern` carries only the physical wire ABI; the wire's
  param and result types are read from the same `FunctionContract` fact.
- Fatal `spec/violation` diagnostics fire at every callsite of an extern:
  its declaration is its whole definition, and the row it is checked against
  comes straight from the one caller that made it, so a rejection is always
  a real fault, in the declaration or in the call
  (`function_contract_is_enforced` in `compiler2/jobs/semantic.rs`). An
  out-of-domain row therefore never falls through to the settled-`none`
  collapse or a native trap; it is a diagnosed compile-time fact, on every
  door, at the exact call. For an ordinary (non-extern) function the
  diagnostic still fires only at USER callsites. Library (bootstrap)
  callsites are validated for refinement but never diagnosed: shared library
  bodies carry joined activation evidence that can pair uncorrelated users
  into phantom argument combinations, so a correct matcher verdict there
  would be a false diagnostic with a span inside library source. The gate
  keys on the violation span's code and retires when activation evidence
  becomes correlation-sound.

  Two users of one library reducer no longer share an activation over the
  ELEMENT their lists carry: the element is part of the key wherever demand
  reaches it (fz-kdt.183, see [`type-specialization`](type-specialization.md)),
  so `Enum.reduce([1, 2], …)` and `Enum.reduce(["a", "b"], …)` in one program
  key two activations and publish two returns. That closed the class of false
  diagnostics where a USER callsite was diagnosed for a NEIGHBOUR's evidence —
  `with_index_users_key_apart_by_element.fz` is the reproducer. The CALLABLE
  slot is still blind and a returned tuple FIELD at a recursive key is still
  freight, so joined evidence has not gone away; the
  element axis of it has.
- Private runtime helpers declare the producer-owned parameter and result
  domains they actually consume. Without a contract, a helper's inputs are
  `any`, so constructor-only clauses such as `[]` and `[head | tail]` are
  genuinely partial and correctly warn. The fixture matrix inventories every
  `defp name/arity` under `lib/` and requires a matching `@spec name/arity`,
  while activated fixtures prove those declared domains remove the warnings
  without hiding genuine user fallthroughs.
- Kernel arithmetic (`+ - * / % div rem`, unary `+` and `negate`) is fully specced in
  `lib/kernel.fz`, so provably non-numeric operands at
  a user callsite (e.g. `:bad + 1`) are fatal compile-time spec violations on
  every path. Each ends in a default clause outside its `@spec`
  (`def _left + _right, do: arithmetic_error()`): the contract is the `@spec`,
  so the clause adds no refusal and no result type (it returns `never`), and an
  operand known only at runtime that is not a number reaches it and raises
  `ArithmeticError` instead of a clause miss or a trap in a typed extern.
  `send/2` is specced `(pid, t)`: the receiver is a pid, gotten
  from `self()` or `spawn`, and an integer such as `send(1, msg)` is rejected
  the same way.

The old `src/specs` operations were removed with the old-world compiler:
scheme matching, overload-set application, structural correspondence grouping,
and declared-vs-inferred coverage checking no longer live in this module. The
old files `apply.rs`, `match.rs`, `select.rs`, `validate.rs`, and
`specs_test.rs` are gone.

Current proof points:

```text
cargo test --lib compiler2::world_test::compiler2_resolve_spec_resolves_types_shapes_and_constraints_against_the_captured_namespace
cargo test --lib compiler2::types::arrow_match
cargo test --lib -- ground_union_input mixed_arity_tuple_union cross_kind_union
cargo test --test fixture_matrix spec_ok
cargo test --test fixture_matrix spec_violation
cargo test --test fixture_matrix opaque_fn_all_divergent
cargo test --test fixture_matrix spec_violation_between_side_effects
cargo test --test fixture_matrix spec_violation_cross_kind_union
cargo test --test fixture_matrix spec_boundary
cargo test --test fixture_matrix spec_mixed_protocol_concrete_violation
cargo test --test fixture_matrix 00605_libc_abs_arg_outside_declared_domain  # extern row, no library-callsite gate
cargo test --lib compiler2::contract_test::extern_row_outside_its_declared_contract_is_a_spec_violation
cargo test --lib compiler2::contract_test::variadic_extern_violation_names_the_tail_domain_past_the_fixed_params
```
