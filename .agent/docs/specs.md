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
  arrow. The current obligation identity is the resolved opaque marker tag
  (`protocol::<Name>.t`) wrapped as a `ProtocolDomainObligation`; it is
  classified from explicit positive markers in hard `Ty` values plus the
  contract bounds sidecar, not from source refs, negative/complement clauses, or
  protocol impl registries. Protocol-domain arrows can still refine calls, but
  arrows with obligations are skipped for fatal
  `spec/violation` decisions until protocol-domain validation is implemented;
  concrete arrows in the same overload set remain enforceable.
- Contract satisfaction is arrow-SET coverage, not just single-arrow
  subsumption: when no single arrow accepts a ground argument row,
  `FunctionContract::apply` checks whether the tuple of arguments is a subtype
  of the union of the enforceable clause-domain tuples (the Types calculator
  decomposes unions across positions). Covered rows satisfy the contract and
  their result is the union of per-clause results on positionally narrowed
  arguments — `(int | float, int)` satisfies `+/2`'s `(int, int)` and
  `(float, int)` arrows jointly and yields `int | float`.
- Coverage reads a VAR-CARRYING clause domain at `any`. A clause variable
  still free after its bounds are closed accepts anything, so that is the
  clause's domain: `pick({integer, a})` covers `{integer, any}`. Together with
  `pick({binary, a})` it covers every member of `{binary, int} | {int, int}`,
  which no single clause accepts — a witness is the argument, so neither clause
  accepts a union spanning both. A polymorphic clause set that could rescue no
  row at all would diagnose that legal program as a spec violation
  (`fixtures2/behavior/spec_polymorphic_clause_set_coverage.fz`). Narrowing a
  covered row into a clause domain leaves a var-carrying position untouched, so
  such a call learns that it is legal and learns no input refinement from it.
- Arrow matching (`Types::match_arrow`) handles union parameters structurally:
  a union of tuples with DIFFERENT arities matches a witness against the
  alternative of the witness's own width, and a kind collector (tuple, list,
  resource, map, arrow) vetoes a signature unless the witness intersects the
  pattern with that kind's component cleared (`witness_escapes_kind`) — a
  cross-kind union like `:first | {:acc, a}` accepts `:first` through its
  atom member but still rejects `:third`, which no member accepts.
- Fatal `spec/violation` diagnostics fire only at USER callsites
  (`function_contract_is_enforced` in `compiler2/jobs/semantic.rs`). Library
  (bootstrap) callsites are validated for refinement but never diagnosed:
  shared library bodies carry joined activation evidence that can pair
  uncorrelated users into phantom argument combinations, so a correct matcher
  verdict there would be a false diagnostic with a span inside library source.
  The gate keys on the violation span's code and retires when activation
  evidence becomes correlation-sound.

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
- Kernel arithmetic (`+ - * / %`) is fully specced in
  `src/modules/runtime_library/kernel.fz`, so provably non-numeric operands at
  a user callsite (e.g. `:bad + 1`) are fatal compile-time spec violations on
  every path. `send/2` is specced `(pid | integer, t)`: the runtime addresses
  processes by raw integer index (`fz_send_ref` takes `receiver_pid_bits`) and
  has no registry, so integer addressing is part of the callee's real domain.

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
```
