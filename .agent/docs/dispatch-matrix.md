# Dispatch Matrix

`src/dispatch_matrix` is the shared model for source-pattern and type-directed
dispatch. Function heads, `case`, `with else`, selective receive, guard helper
dispatch, and protocol finite-union dispatch all build a `DispatchMatrix`,
compile it to a `DispatchGraph`, and let producer policy decide what a winning
outcome means. `SourcePatternRows` normalizes AST patterns into rows, but the
runtime decision graph for source patterns is owned by `DispatchMatrix`.

The model names four separate concepts so dispatch work does not grow new
subsystem-specific cascades:

- `Region` is the value-space question an arm asks of a subject: type,
  constructor shape, equality against a literal or pinned value, map-key
  presence, bitstring shape, or a guard predicate.
- `Order` is why an arm wins when regions overlap: source order, type
  specificity, or an explicit materialized order.
- `Outcome` is an opaque handle chosen after an arm wins. Pattern bodies,
  receive accept/reject behavior, protocol direct calls, fallthroughs, and halts
  stay outside the region model.
- `DispatchGraph` is the executable decision shape: tests route to nodes, and
  successful edges carry branch-local proofs and projections.

`compile_dispatch_matrix` is pure and side-effect-free. It compiles ordered arms
into a deterministic graph and returns `DispatchCompileStats` so tests can assert
shape signals such as test count, fallback count, and shared-prefix tests without
depending on formatted graph dumps.

`compile_dispatch_matrix_with_type_order` handles `Order::Specificity` for
type-region arms. It uses `Types` operations only: pairwise relations are
`Equal`, more-specific, less-specific, disjoint, or ambiguous overlap; ordering
puts strict subtypes before supertypes while orthogonal arms keep deterministic
identity order. Equal-overlap handling is producer-policy driven: a producer can
classify equal regions with different outcomes as duplicate coverage or as an
ambiguity. `analyze_type_coverage` computes covered and residual receiver
domains, distinguishing closed coverage from open residuals.

Protocol call dispatch is callsite-owned in compiler2. `jobs/semantic.rs`
settles each callsite as a `CallSiteSummary` with one `CallTargetSummary` per
viable impl target. `compiler2::callsite_dispatch::call_destinations` is the one
door from that summary to what the call actually is: it answers
`CallDestinations::None`, `::Direct(target)`, or `::Dispatch(plan + targets)`,
and materialization follows the answer. The plan is a `PatternDispatchPlan<Ty>`
built from the receiver-narrowed `CallTargetSummary.surface_inputs`, with opaque
body ids assigned to the destinations in order.

A settled target is not automatically a destination. An arm asks its question
through `RuntimeTypePredicate`, which is coarser than the type it is projected
from: `[int]` and `[int | :ok]` project to overlapping questions -- the head
test separates only DISJOINT element families (the one-sided-filter law), and
a same-fn-id pair differing only in captures projects to one question
entirely. (Before fz-kdt.107 step 3, ANY two list types were one question --
a list test read the cons cell and nothing inside it; `[int]` vs `[:ok]` now
separate by head.)

A target is dropped when some sibling W *stands in for* it — names the SAME
callee, accepts a strictly wider observable domain, and asks a question that
admits everything its own admits — **and** the seat itself would not put it
ahead of W:

```text
    unroutable(N)  ⇔  ∃ W ≠ N :  stands_in_for(W, N)  ∧  ¬ seats_before(N, W)
```

`seats_before` is the seating relation under *Seating* below, factored into one
free function that both the seat and the drop call. For a stand-in pair that is
a routing question at all, `seating(W, N)` is `Covering` unconditionally, so the
condition reduces to
*keep N iff `covering(N, W)` and N's test is strictly inside W's*: a redundant
arm survives exactly where the seat would place it ahead of the arm that stands
in for it, and nowhere else. A callsite left with one destination is a `Direct`
call rather than a one-armed dispatch.

All three conjuncts of `stands_in_for` are load-bearing. The same-callee one:
a multi-target summary normally names one target per selected callee, which is
exactly what protocol dispatch is, and a wider domain sitting on a different
function's body is no stand-in at all. Strictness makes the relation a strict
partial order, so a maximal arm has no stand-in and survives, and arms of equal
observable surface — alike everywhere the runtime CAN look, different only
where it cannot — keep each other. And test containment is NOT implied by
surface containment: `[int | :ok] & not([:ok])` is a strict subtype of
`[int | :ok]`, but a negated list clause cannot be projected to a head
question, so its axis degrades to `ListShapes::shape_only` and the narrower
SURFACE carries the WIDER TEST — it admits `[:zzz]`, which its sibling refuses.

Both containments are judged on the OBSERVABLE surfaces — the settled
`surface_inputs` run through `Types::runtime_type_test_envelope`, the same
projection the plan's rows are built from — not on the settled semantic types. The envelope
erases what no runtime test can read back off a value: a callable argument
keeps its literal `fn_id` AND the capture types beside it, and loses the arrow
it was typed at, because a closure object's heap word at `+8` is the address of
the construction wrapper that minted it — and a wrapper is one function at one
capture layout, so the capture TYPES are a fact about the value while the arrow
is not.

A callable position is therefore a real question, and it is what separates
`Range.reduce_step/6`'s `({:cont, int} | {:halt, int}, #66closure[])` from its
`({:cont, int}, #68closure[])` sibling by its reducer. Before the callable axis
existed the pair asked one question, neither arm contained the other, and
`:halt` was one legal arm order away from being read as a continue. Now each arm
is reached by the values its own reducer travelled with. The axis reaches one
callable at two capture layouts too: `#66closure[int]` and `#66closure[float]`
are two construction wrappers, so they are two addresses and two questions, and
a value's captures are never loaded to decide it (fz-kdt.127). What the axis
cannot reach is a capture layout the projection could not shape — a clause that
pins several literals at once is an intersection, and it degrades the whole
axis to the target-only reading. The envelope hands such a clause on whole,
literals and all, so that degradation is decided in one place and the plan path
— which projects the ENVELOPED type, not the settled one — reads exactly what
projecting the settled type would.

The callable envelope is applied AT EVERY DEPTH (fz-kdt.119), not only to a
top-level argument. A closure nested in a tuple is read by the same one
comparison as a top-level one, so `{:tag, #66(int)}` and `{:tag, #66(float)}`
are two observables exactly as `#66(int)` and `#66(float)` are, and
`{:tag, #66}` and `{:tag, #68}` are two. Widening a nested callable to
`fun_top` instead would reproduce the defect above one tuple deep, and leave a
depth-0/depth-1 seam nothing in the runtime justifies.

Dropping decides no routing except in the one shape named after this paragraph,
and the argument is relative to arrival order rather than absolute. Take the
arrival [survivors in post-drop seated order, then the dropped arms
widest-first]. It is a permutation of the settled targets, so it is an order
the fixpoint could have delivered, and the seat reproduces its own output — for
two arms adjacent in a seated order the later one refuses to pass the earlier,
either because it stopped there or because the earlier one passed it and
antisymmetry forbids the reverse — so the first k insertions reproduce the
survivors' seat and the dropped arms arriving afterwards cannot reach back into
it. Each dropped N is then inserted and cannot pass its stand-in W: passing it
needs `seats_before(N, W)`, which the drop condition says is false. So W
precedes N there and admits everything N admits, N receives nothing, and the
routing the plan performs after the drop is one that legal arrival already
produced.

WHERE THAT STOPS: THE DROP CAN DISSOLVE A GROUP. Every step above assumes the
survivors group the same way with the dropped arm and without it. The seat
moves whole question groups and coverage quantifies over the product, so a
group is harder to cover than any one member — an arm sharing its question with
a SURVIVOR is part of what pins that survivor behind a wider arm. Drop it, the
group dissolves, the survivor is judged alone, and the seat can promote it past
the arm that used to swallow its values: those values then reach the survivor's
body, where every arrival of the un-dropped arms sent them to the wider arm. It
is not a blind escape — `seats_before` demands `Covering` before it moves
anything, so the promoted arm's surface names what it now receives, and the
escape census does not move — it is a routing the drop decides that arm order
used to.
`a_drop_that_dissolves_a_question_group_reseats_the_survivor_it_pinned` builds
the smallest case, three arms wide, and pins it. The precondition is exactly "a
dropped arm shares its question with a surviving one", and no callsite on the
corpus has one: swept over 597 fixtures at the fz-kdt.143 landing the count is
zero, which is why the corpus reads 0 behaviour movers on both doors. The
residue is fz-kdt.118's as much as fz-kdt.143's — 118 dropped a member of a
group, which dissolves one just the same. The re-routed values lie in BOTH
surfaces, so when the promoted survivor and the wider arm are specializations of
ONE callee the move is meaning-neutral by construction and the post-drop seat is
simply the more precise one; it is meaning-bearing only when they are DIFFERENT
callees, which is the semantic layer offering two callees for one value at one
callsite — an ambiguity no seat can resolve honestly. **fz-kdt.176** owns that
invariant (targets of different callees at one callsite have disjoint observable
surfaces, or the overlap is a diagnostic); with it this residue reduces to a
statement about precision.

The population beyond fz-kdt.118's is named exactly. Where the two arms ask ONE
question their tests are equal, `strictly_inside` is false, and N is dropped —
118's rule, decided identically, which is why the generalization is the
identity on 118's population. Everything the quantifier adds is
`{N : some W stands in for N and ¬covering(N, W)}`, and `¬covering(N, W)` is by
definition "seating N ahead of W is a blind escape". So nothing the seat would
have put first is ever dropped, and what leaves is exactly the arms that were
either dead behind their stand-in or a blind-escape seat waiting for a legal
arrival to produce it.

The check's shape carries two facts. The drop asks `seats_before` of two single
arms while the seat asks it of two question GROUPS; coverage quantifies over
the product of the groups, so a group reading can only be falser than the
singleton one. That mismatch cannot drop an arm the seat would have put ahead
of its stand-in: reading it group-wise could only turn `covering(W, N)` false,
which reduces `seats_before(N, W)` to plain `covering(N, W)`, and for the
singleton check to have refused while that holds the two tests must be equal —
which puts N and W in ONE group, where no seat separates them at all. What it
does not cover is the grouping the drop CHANGES, above. And no
cascade is needed: `stands_in_for` is a strict partial order, the existential
ranges over every arm rather than the survivors, so an arm dropped only on
account of another dropped arm is dropped by that one's own stand-in too.

Two adjacent facts close the loop. A drop to a single destination converts the
plan to a `Direct` call, which also removes the plan's fail node — a value
outside every arm's observable domain would have trapped and now routes to the
survivor. That conversion is fz-kdt.104's pre-existing `sole_destination` and
is fenced by the semantic analysis, not by this rule; what fz-kdt.143 changed
is that the drop can now reach it across the whole arm set where fz-kdt.118
reached it only within one question group. Measured at that landing: 51 call
dispatch sites before and 51 after, so no callsite on the corpus collapsed to
`Direct` that was not one already. And a drop cannot ground a call it should
not: `call_destinations` has exactly one consumer, at artifact materialization
— the semantic fixpoint, `RuntimeDemand`, and transport never read it, so
dropping an arm cannot shrink a `CallableDemand.targets` count or manufacture a
`CallEdge::Direct`.

What separability does not buy is order-independence. A test is coarser than
the surface it was projected from, so a value can pass an arm's test without
belonging to the domain that test was projected from, and seating decides which
arm receives it — order costs meaning wherever two tests overlap, and that is
fz-kdt.107's subject one rung wider than the arms asking ONE question.
(fz-kdt.129 corrects the "order costs precision, not meaning" phrasing this
paragraph inherited; the measurement is under *Seating*.) A `:timeout` arm
beside an `any` arm is the benign case — the atom test is exact, so nothing but
a `:timeout` passes it, coverage runs both ways, and the narrower TEST is
seated first rather than dropped.

Arms with no stand-in between them survive and stay order-decided: neither
observable domain contains the other, or they are two different functions, or
the narrower surface carries the wider test. So do arms alike everywhere the
runtime CAN look and different only where it cannot, where containment is
mutual and strictness keeps both.

That surviving order-decided residue is a live wrong answer, not a tolerated
imprecision: a body specialized on a closure literal can ground a DIRECT call
to it (`exact_direct_callable_layout` → `TransportCarrier::Absent` →
`materialize_closure_call_edge`), so a sibling's closure routed into it never
runs. Keeping the dead arm does not prevent that — the plan has no question to
separate them either way. See fz-kdt.107 and fz-kdt.125.

### The two free orders, and the stress that moves them

Two orders decide which body a value reaches, and neither is the language's.

A callsite's **arrival order** is the settled targets' order, which is the
semantic fixpoint's, which is the agenda's. A callable value's
**construction-wrapper member order** used to be the same: a
`BTreeSet<CallableSurface>` walked in interned-id order — the type interner's
mint order, which is the agenda's again. `jobs/transport.rs` derives the
wrapper's members AND its selection plan from that one list, and a selection
row's `body_id` is welded to its member's index, so the list itself is the only
place either can be reordered. **fz-kdt.108** made the SETTLED order canonical
there: `callable_flow_resolution_edges_product` (`jobs/runtime_demand.rs`) now
sorts the edges by `Types::cmp_tys` over each surface's inputs BEFORE the members,
the selection plan, the boundary resolutions, the flow's resolution list AND the
`activation_key` `Ty`s all derive from them — one ordering authority, inherited
by everything downstream, so a re-ordered pull produces the same artifact. The
direct half (`callable_flow_edges_for_targets`, a `BTreeSet<CallableTarget>`) is
ordered by the same key for the same reason. `cmp_tys` is total up to the two
residuals `types::order` documents (free-var ties, lambda byte-span labels);
those fall back to mint order and are the only construction-order gap left across
schedules (`00277_enum_tier0_fixture`'s `(int, list(int | :tail))` surfaces are
one). The stress knob still owns the order for testing: `wrappers:<seed>`
permutes the canonical list AFTER it is sorted (the perturbation wraps
`callable_flow_resolution_edges_product`'s result), so the fz-kdt.141 gate that
proves the perturbation reseats the members stays honest.

Any permutation of either order is one the fixpoint could have delivered, so an
answer that moves under one is an answer a schedule decides. `dispatch_stress`
(in `callsite_dispatch.rs`) makes that testable through
`FZ_STRESS_PERMUTE_DISPATCH`, a comma-separated list of clauses:

| setting | what it perturbs |
| --- | --- |
| unset, `""`, `0` | nothing — production borrows the settled order |
| `7` | seed 7 on both surfaces |
| `arms:7` | a callsite's arrival order only |
| `wrappers:7` | a construction wrapper's member order only |
| `reverse` | both surfaces reversed |
| `arms:reverse` | each runtime-indistinguishable GROUP mirrored — what the retired `FZ_STRESS_REVERSE_DISPATCH_ARMS` did |
| `arms:3,wrappers:9` | a different seed per surface |

A seed names a permutation of the whole order and NEVER the settled one: most
free orders in the corpus are two items long, a fair shuffle of two comes out
settled half the time, and a seed that leaves the order it was asked to perturb
is a green reading with nothing behind it. A setting the grammar does not
recognize panics rather than sweeping inertly, for the same reason.

**Why the group reversal was not enough** (fz-kdt.141). It reaches ONE
permutation, of exactly the pairs the plan cannot separate — so every time the
predicate learned to separate more of them (fz-kdt.119) the same knob got
weaker, and on a callsite whose groups are all singletons it is the identity.
And it never touched the wrapper order at all (fz-kdt.136). Measured over the
584-fixture corpus at the fz-kdt.141 landing, by backend-dump hash:

| perturbation | fixtures whose artifact moves |
| --- | --- |
| `arms:reverse` | 8 |
| `arms:<seed>` | 27 |
| `wrappers:<seed>` | 19 |
| unset vs `""` vs `0` | 0 — the knob is inert when off, on the same comparand |

**The gates.** `compiler2_dispatch_answers_the_same_under_a_permuted_arm_order`
and `..._under_a_permuted_wrapper_order` hold each census to one answer through
the interpreter, in process, under `arms:reverse` + two arm seeds and two
wrapper seeds respectively.
`compiler2_a_permuted_wrapper_order_reseats_the_construction_members` asserts
the wrapper perturbation LANDS (a moved canon), because a gate is worth exactly
what its perturbation reaches. `compiler2_jit_halts_a_reduce_under_every_arm_order`
holds the one fixture that can face the native door in process.

**The sweep recipe.** The in-process gates are bounded; the whole corpus by
every door is a shell sweep, and it is what a dispatch-order change should be
re-measured with:

    for setting in arms:reverse arms:1 arms:6 wrappers:1 wrappers:6 1 6; do
      for fixture in fixtures2/*.fz fixtures2/behavior/*.fz; do
        base=$(fz2 interp "$fixture" 2>/dev/null); base_rc=$?
        stressed=$(FZ_STRESS_PERMUTE_DISPATCH=$setting fz2 interp "$fixture" 2>/dev/null); rc=$?
        [ "$base" = "$stressed" ] && [ "$base_rc" = "$rc" ] || echo "MOVER $setting $fixture"
      done
    done

Swap `interp` for `run` (JIT) and for `build -o /tmp/x && /tmp/x` (AOT). Stdout
and the exit status are the behaviour comparand — stderr carries thread ids.
This recipe measures BEHAVIOUR movers (the zero column). The artifact-mover
table above is measured with the canon comparand instead: add
`--dump backend=<path>` to both invocations and compare the dump hashes -- a
fixture whose stdout is invariant can still move its plan content, which is
what the 8/27/19 numbers count.

**What the sweep reported at fz-kdt.141, and what it reports now.** The
interpreter was invariant under every setting then and is now: 0 movers over the
corpus × 19 settings. Natively FOUR fixtures aborted, all with one signature —
`fz_list_head_int_ref`, a list whose elements are not ints (atoms on two
fixtures, bitstrings on `enum_map_family`, structs on `00277`) read through the
int accessor — and all in the fz-kdt.107 step-3 class of list arms whose bodies
use incompatible element accessors and none of which covers another:

| fixture | settings that aborted it | at fz-kdt.107 step 3 |
| --- | --- | --- |
| `enum_map_family` | `arms:reverse`, `arms:6` | rc 0 |
| `00277_enum_tier0_fixture` | `arms:1` … `arms:5` | rc 0 |
| `dispatch_seat_element_blind` | every arm seed | rc 0 |
| `enum_predicate_search` | `arms:6` | rc 0 |

All four are dead. Re-measured at the step-3 landing over `arms:reverse` and
`arms:1` … `arms:6` on the JIT, and over `arms:reverse`/`1`/`6` on the AOT door:
every run exits 0 and prints what the settled order prints. The head question is
what killed them — the three arms of each group are three questions now, and
where two of them still meet at the head the covering one is seated first.

### What a test can see

`RuntimeTestAxis` (`src/runtime_type_predicate.rs`) is the table of every axis a
runtime test can decide, and it is the ONE table this layer is written against.
A predicate is a union over those axes and nothing else: a value reaches exactly
the axes its kind names, so a test is the OR of its axes' answers, containment
is the AND of them, and two tests overlap when they overlap on some axis. The
three lowerings — the interpreter's `matches_runtime_type_predicate`, and the
one native emitter in `native_codegen::runtime_test` that both the compiled-body
door and the receive door go through — each decide the axes by matching the
table exhaustively, so an axis cannot join the lattice without every lowering
refusing to compile until it is taught to test it.

Each axis carries an `AxisPrecision`, which is what a SEAT may read from
deciding it:

| axis | precision | why |
| --- | --- | --- |
| atoms | separating | passing is BEING one of the named values |
| callables | per position | passing is being MINTED FROM a named construction -- a function AND the capture types it closed over -- so it separates exactly as far as the capture sub-tests do |
| ints, floats | separating | presence bits: one representation, so no admitted body can misread what arrives — brands are runtime-erased by construction (fz-bsx), and restoring numeric singletons to the lattice would re-open this row |
| lists | per position | empty-or-cons, plus the first element's own question — as separating as two head questions are DISJOINT |
| named/other structs, maps, binaries, resources | erasing | a schema id or a kind, never the contents |
| tuples | per position | as separating as the positions' own sub-tests |

The tuple axis is `TupleShapes`: one shape per tuple CLAUSE of the descriptor it
was projected from, each carrying its positions' own predicates, plus the arity
reading derived from the shapes' lengths for the callers that only want that.
One shape per clause is what keeps cross-position correlation — `{:cont, int} |
{:halt, atom}` is two shapes, and joining them position-wise would admit
`{:cont, atom}`, which neither clause names (fz-kdt.126: never re-join what the
lattice kept apart). A clause with several positive signatures is an
intersection and one with negations is a difference; neither is a list of
positions, so either degrades the whole axis to the arity-only reading, which is
what every clause answered before fz-kdt.119 and is a sound over-approximation
of what it says now.

The callable axis is `CallableShapes`, built to the same pattern: one shape per
positive closure-literal CLAUSE, each carrying the function it names and one
sub-predicate per CAPTURE position, plus the target set derived from the shapes
for the callers that only want that. A construction wrapper is one function at
one capture layout and stamps its own address into every value it mints, so
which wrappers a test admits is decided at codegen from each wrapper's own
shape, and the value pays one address compare per admitted wrapper — its
captures are never loaded. A clause that pins several literals at once is an
intersection and is not one shape, so it degrades the whole axis to the
target-only reading, which is what every clause answered before fz-kdt.127.

That degradation is decided exactly once, in
`Types::runtime_type_predicate_callables`. `callable_identity_clauses` — the
envelope the plan path projects through — keeps the clause shape it was handed
rather than splitting such a clause into its several literals over no captures:
several zero-capture literals would arrive here as EXACT shapes with no capture
positions, and since a shape is admitted only at an equal capture count, that
axis would refuse every CAPTURING construction of the very targets it names.
Under-admission is the one direction a runtime test may never err in.

ADMISSION on this axis is CONTAINMENT, not overlap, and it is the one place the
axes differ in kind. A capture type is the ANNOTATION the mint stamped, not a
fact re-read off the value: the layout a capture was STORED in belongs to the
construction. A wrapper closed over `int | float` therefore stores a boxed
word, and a body whose capture lane is a raw int must not receive it even
though the two tests overlap — so a value is admitted only where its
construction shape lies INSIDE a shape the test names. The two-test relations a
seat reads (containment, overlap, erasing overlap) are the ordinary ones, and
recurse into the captures exactly as a tuple's recurse into its positions.

The list axis is `ListShapes`: which shapes the test admits, plus one HEAD
question per list clause that admits a cons cell — the same one-per-clause rule,
for the same correlation reason. A clause with several positive signatures or
with negations is not one element type, so either degrades the whole axis to the
shape-only reading, which is what every clause answered before fz-kdt.107 step 3.
An `[]`-only clause puts no head question: there is no cons cell to read.

**The one-sided-filter law.** A list type is HOMOGENEOUS by construction —
`ListSig` carries one element type for the whole list — so one head load is a
one-sided test:

- EXACT ON REJECTION. A head outside the element question proves the whole value
  lies outside the surface. That is a real proof, and it is what makes disjoint
  heads a real separation: `[:false | :true]` against `[int]` can never both
  admit a value, so no seat between them owes a surface check.
- ERASING ON ACCEPTANCE. A head inside the question proves nothing about the
  tail, which no test reads. So two `NonEmpty` tests whose heads overlap AT ALL
  erase, however exactly the heads themselves are decided: `[int]` and
  `[int | :ok]` put the same question to a first element and disagree only about
  what may follow it.

Disjoint heads are therefore the ONLY claimable separation, and this direction is
load-bearing rather than conservative. The rule that shipped in the step-3
proposal read "the heads differ" as separation; the prototype measured it seating
`[int]` ahead of `[int | :ok]` on the precision preference, at which point
`[1, :ok]` passes the narrow head test and lands in the body that reads every
element as an int — the very abort the axis exists to kill, re-created by it.
`an_arm_whose_head_overlaps_a_wider_one_is_seated_after_it` is the gate that
catches it.

**The `[]` exception.** Two tests meeting ONLY at the empty list do not erase.
`[]` is a single value carrying nothing for a body to misread, which is the same
reason the atom axis separates. Meeting through a cons cell is the erasing case,
because the tail behind it is what neither test looked at.

Both the interpreter and the two native doors read the head through the
representation's own owner — `matches_list_elements` through a `ListHeadReader`,
`emit_list_axis` through `RuntimeTestEmitter::list_head` — and the head question
is asked INSIDE the cons branch and nowhere else, so a head-blind or `[]`-only
test emits and answers exactly what it did before. The nested question is a full
`RuntimeTypePredicate`, so an arity reachable only through a head is an arity
every lowering must register a schema for; `RuntimeTypePredicate::sub_predicates`
is the ONE walk that reports them, matched exhaustively over the axis table so
the next nested axis cannot forget to answer (**fz-kdt.145**).

**What the head does not buy.** Splitting a question group does not cost the
drop any more, and `[int]` beside `[int | :ok]` is why: they are two questions
now, so fz-kdt.118's group-local drop no longer reaches the pair, but the arm
rule under *Protocol call dispatch* is quantified over every arm and drops
`[int]` anyway — their heads overlap, so `covering([int], [int | :ok])` is false,
the seat would never place `[int]` first, and an arm the seat would never place
first is no destination (**fz-kdt.143**). What the head DOES leave behind is a
pair whose heads overlap while neither surface contains the other: no seat is
escape-free, neither arm stands in for the other, so nothing is dropped and
arrival stands. `enum_predicate_search` carries the corpus's two, and
**fz-kdt.131** owns them.

The dropped arm is still a demanded executable wherever something else calls
it. On `dispatch_list_head_separates` the two arms fz-kdt.143 removes from the
`List.reduce_while_cont/3` callsite stay in the artifact and stay natively
defined, reached by direct call edges the callable-flow path grounds:
`define_function` holds at 111 while the callsite's arms go 4 → 2. Where the
dropped arms had no other caller the code goes with them — the three receive
fixtures lose six `Kernel.dbg/1` arms each, `define_function` 46 → 34, 49 → 37,
49 → 37.

**Every position is asked, at every depth.** A tuple position carries a full
predicate, so it is decided by the same lattice and the same three lowerings as
a top-level test, whatever axes it spans — a list-bearing position asks the list
axis, and a position holding a tuple recurses. There is no position a test
declines to ask, so there is no position a seat has to treat as overlapping and
erasing on principle.

It read differently until **fz-kdt.138**: a position that could hold a LIST was
excluded from the lattice and from all three lowerings alike, because deciding
it separates `{[], int}` from `{[int], int}` and that separation reached a fold
accumulator specialization that did not exist yet (**fz-kdt.132**, which minted
it). What the exclusion cost is `dispatch_nested_list_position_separates`: the
first clause took every value, so `{:a, [integer]}` against `{:a, [:ok | :err]}`
answered by clause order rather than by the value, on `interp`, `run` and
`build` alike — the tag defect `dispatch_annotated_tuple_tag_clauses` pins and
the element defect `dispatch_list_head_separates` pins, one nesting level in.
A blind position only ever ACCEPTS, so the defect showed only where the
list-bearing clause was written first, and a literal argument hid it entirely:
the argument's own type settles the clause at compile time, so a
literal-argument probe reports no defect at all.

## Seating

Which arm is tested first is therefore not read off arrival alone.
`specificity_order` starts from arrival order and corrects it wherever the arms
themselves say it is wrong.

### What a seat can get wrong

An arm's `RuntimeTypePredicate` is COARSER than the surface its body was
compiled for: a list head says nothing about the tail, and a tuple position
erases whatever its own sub-test erases.
So a value can satisfy every question an arm asks and still lie outside that
arm's surface, and seating that arm first routes the value into a body whose
representation never named it — `fz_list_head_int_ref` reads a list of atoms as
a list of ints and aborts on the JIT and native doors, while the interpreter's
dynamic tags hide it.

Call that a BLIND ESCAPE: `early` is seated before `late`, and at some position
the two tests both admit some value on an axis whose projection erases what the
bodies read, while `late`'s surface holds values `early`'s does not. Two
orderings were built on containment alone and BOTH create blind escapes, in
opposite directions (both were measured when a list test still saw empty-or-cons
and nothing else, which is why both examples turn on lists):

- seating the narrower SURFACE first puts `list(int) × {all?/1, all?/2, empty?}`
  ahead of `list(:ok) × {empty?}`. `list(int)` was a subtype of its sibling and
  the very same test — every list was "a non-empty list" to a predicate that
  recorded list shape and nothing else — so the surface rule seats an arm whose
  CALLABLE test admits three lambdas in front of one admitting a single lambda,
  where it swallows that sibling's values.
- seating the narrower TEST first puts `list(int) × {all?/1}` ahead of
  `list(:ok) × {all?/1, empty?}`, because a callable set of one is strictly
  inside a set of two. Then `Enum.all?([:ok, :ok])` carrying the shared lambda
  satisfied BOTH of its questions and reached the int-reading body.
  `dispatch_seat_element_blind` is that program; fz-kdt.107 step 3 gave those
  two arms disjoint head questions, so the pair no longer meets on an erasing
  axis at all.

Neither containment is the criterion on its own, and neither applies at all
until the pair is a routing question. `seating(early, late)` answers one of
three things:

- SEPARATED — no value satisfies both arms' tests. A plan row is a conjunction
  over its subjects, so the two arms admit a common call only where EVERY
  subject admits a common value (`RuntimeTypePredicate::overlaps`, position by
  position). Where one subject refuses, the plan's own test keeps the arms
  apart whichever way round they sit; the seat has nothing to decide and the
  pair keeps arrival order (**fz-kdt.186**). Before 186 the coverage check ran
  position by position under an `all`, so a pair disjoint at subject 0 passed
  that subject on the separation arm and was then judged blind at subject 1 —
  a routing that routes nothing, reported as a seat obligation.
  A subject the two arms ask IDENTICALLY is skipped: it admits the same set to
  both, whatever that set is, and where every arm asks it `discriminating_inputs`
  drops it and the plan emits no test there at all. That is stated rather than
  inferred, because not every projected test is realizable — a tuple clause with
  a subtracted signature loses its whole arity in
  `runtime_type_predicate_tuple_arities`, so `{any, any} & not({int, int})`
  projects to a test that admits nothing and does not overlap itself, and
  reading a subject like that as a separation collapsed a two-arm callsite to a
  `Direct` call on the arm the seat had put SECOND
  (`an_untested_position_is_not_a_separation`). So a separated pair always
  differs at the separating subject, which makes that subject discriminating and
  the emitted test the thing that keeps the arms apart.
- COVERING — some value satisfies both, and SURFACE COVERAGE holds: at every
  position where their tests could both admit a value on an ERASING axis
  (`overlaps_on_an_erasing_axis`, which reads the `AxisPrecision` table above),
  `early`'s surface already contains `late`'s.
- ESCAPING — some value satisfies both and that coverage fails somewhere.

"The tests differ" is not separation on an erasing axis: `[int]` and `[int | :ok]`
both admit a cons cell whose head is an int, and an arity-only tuple test at {2}
and one at {2,3} both admit a 2-tuple. A separating axis excuses the surface
check, because a value passing it is pinned down far enough that no admitted
body can misread it. A tuple pair is judged position by position: it is erasing
only where two shapes that could both admit a value overlap at a position that
is itself erasing — so `{:cont, int}` against `{:halt, int}` separates on an
atom and needs no surface check, while `{:ok, [int]}` against `{:ok, [int | :ok]}` is
one and the same question. Under that definition, seating a covering arm first
cannot escape anything, by construction -- the surface check is skipped only
where the tests cannot both admit a value the projection would blur.

### The rule

- arms are seated by their QUESTION GROUP, and a group's members keep arrival
  order. Keeping arrival order inside a group is the safety story — no test the
  plan emits separates a group's members, so their order decides which body
  their shared values run,
  and fz-kdt.107 prototyped canonically ordering them and got `{:done, 3}` where
  `{:halted, 3}` was due.
- groups start in arrival order, and group `x` is moved ahead of group `y` when

      covering(x, y) and ( not covering(y, x) or test(x) strictly inside test(y) )

  The first disjunct is the OBLIGATION — only one direction is escape-free, so
  take it. The second is the PRECISION preference — both directions are
  escape-free, so hand a value both tests admit to the arm that named it most
  precisely. The relation is antisymmetric: if both directions held, both would
  need `Covering` both ways, so both would rest on strict mutual containment of
  the tests, which makes the tests equal and the two groups one. A SEPARATED
  pair is false both ways for free.
- where NEITHER group covers the other, no seat is escape-free and the rule
  declines to have an opinion: the pair keeps arrival order. That is fz-kdt.107's
  inseparable class one rung wider, and **fz-kdt.131** owns it. The cure is a
  runtime test that can see what the body relies on — fz-kdt.119's per-position
  tuple tags, fz-kdt.107 step 3's list elements — not a cleverer sort.
- where the pair is SEPARATED, arrival stands too, and that residue is the one
  a canonical tie-break could remove: no value satisfies both conjunctions, so
  neither order routes anything anywhere and changing it changes no
  destination. **fz-kdt.194** owns it. Measured at fz-kdt.186's landing: under
  `arms:3` the canonical form differs from the settled build's on 25 of the 597
  corpus fixtures where it differed on 23 before, the two extras being
  `00420_enum_take_drop_split` and `enum_take_drop_split`, whose call-edge plan
  the old reading had been pinning to a seat.

So the three residues are one apiece: an inseparable GROUP (fz-kdt.107), an
overlap WITHOUT containment (fz-kdt.131), and a SEPARATED pair (fz-kdt.194).
The first two carry a routing the order decides; the third carries none.

The correction is one backward insertion pass: each group walks left past
already-seated groups for as long as the relation holds of the pair, and stops
at the first group it may not pass. A permutation comes out, so the seat is
TOTAL by construction and needs no tie-break to fall through to, and it is a
deterministic function of the arms and their arrival order. Stopping at the
first refusal is a requirement, not a compromise: passing a group means passing
everything between. `Covering` is not transitive — two groups can be blind at
different positions — so no rank or comparator linearizes it, which is why the
pass is an explicit insertion rather than a sort.

### What the seat guarantees

**All of this is about CALL-EDGE dispatch, and only about it.** The seat runs
where `routable_alternatives` runs, which is the callsite path;
`dispatch_from_callable_flow_edges` builds a construction wrapper's member
selection without it, so a wrapper's plan has no drop, no seat and no
`debug_assert` behind it (**fz-kdt.179**). The three SOURCE-ORDER sites — an
executable's own entry dispatch, a body's `case`, a `receive` — have no seat
either, and must not: their order is the source clause order, which is the
language's meaning.

Of call-edge dispatch, then: every pair whose seat differs from arrival order
was individually checked and moved only under `Covering`, which admits no blind
escape; every other pair sits exactly as arrival left it. So **the seat's blind
escapes are a SUBSET of arrival order's** — this rule can only ever remove one,
never add one. A `debug_assert` in `specificity_order` holds every callsite of
every debug compile to it, and
`compiler2_dispatch_seats_the_covering_arm_where_one_covers` reads the same
property back off the landed artifact across the arm-order census — for call
edges, and for the wrapper selections whose findings that gate's
`SELECTION_SEAT_ALLOWANCE` names one site at a time until fz-kdt.179 retires
them.

What the seat does NOT guarantee is that no blind escape remains.
`compiler2_dispatch_blind_escape_census_is_the_known_population` counts the
survivors. At fz-kdt.129's landing there were 19, over 12 arm pairs, every one a
list subject a shape-only test could not see the elements of; fz-kdt.119 retired
none of them, exactly because they were all lists.

fz-kdt.107 step 3 retires SEVENTEEN. A pair whose heads are disjoint never meets
on an erasing axis at all, and that is most of the population — including all
three of `enum_map_family`'s, which is why its arm-reversal abort dies, and
`dispatch_seat_element_blind`'s one, which is why that fixture stops aborting
under every arm seed.

TWO survive on call edges, both in `enum_predicate_search`: `[:false | :nil]`
seated before `[int | :nil]`, and `[:false | :true]` before
`[int | :ok | :true]`. Their heads genuinely OVERLAP — on `:nil` and on `:true`
— and neither surface contains the other, so no seat is escape-free and arrival
stands. That is **fz-kdt.131**'s facet 3, not a head the axis failed to read,
and its cure is a repr-level or minting-level decision rather than an ordering
rule. The reproducer fixture `dispatch_list_head_separates` carries the same
pair on purpose, so the call-edge census reads three.

### What the static census walks

The artifact carries a `PatternDispatchPlan` at FIVE kinds of site, and the
runtime reaches a body from each of them by the same first-match walk of the
same decision graph, so all five are censused (**fz-kdt.178**; before it, only
the call edges were). Three of the five have a plan field of their own —
`DispatchCallEdge`, `ExecutableDispatch`, `BackendConstructionWrapper` — and
two ride a `BackendTail`: `BackendTail::Dispatch`'s `ControlDispatch`, which is
a body's own `case`, and `BackendTail::Receive`'s `BackendReceive`.
`drive_test.rs`'s `artifact_plans` yields them, named by site: `callsite <n>
(executable <e>)`, `entry dispatch of executable <e>`, `case dispatch at entry
e<n> (executable <e>)`, `receive at entry e<n> (executable <e>)` and `wrapper
w<n> selection`. Each site lists its bodies in its own order — the call arms,
the reachable clause ids, the arm entries, the receive clauses, the member
index — and `compiler2_dispatch_lists_its_bodies_in_the_graphs_first_match_order`
holds that list to the order the graph actually reaches them in, over every
plan the census fixtures carry (281 plans, 0 disagreements), because the list
is what every seat argument here is read off and the graph is what execution
follows.

TWO OF THE FIVE ARE THE COMPILER'S ORDER and three are the PROGRAMMER's. A
call edge's arms and a wrapper's members are seated by the compiler, and those
are the two a seat rule may move. A function's clauses, a `case`'s clauses and
a `receive`'s clauses are tried first-match in SOURCE order, which is what the
language means, so all three are excluded from the seat gate and counted for
blind escapes under one source-order class instead.

The population, on the 22 census fixtures at the settled arrival:

| kind | plans | unreadable | blind readings | seat findings | one-question groups |
| --- | --- | --- | --- | --- | --- |
| call edge | 25 | 0 | 3 | 0 | 0 |
| entry | 144 | 137 | 0 | excluded | 0 |
| case | 3 | 3 | 0 | excluded | 0 |
| receive | 2 | 0 | 0 | excluded | 0 |
| wrapper selection | 107 | 0 | 45 | 45 | — |

All 45 selection readings are REACHABLE and all are fz-kdt.179's: 34 on 00277's
ten escaping wrappers, 3 on `enum_hof_three_distinct_closures`, and four apiece
on `00420_enum_take_drop_split` and `enum_take_drop_split`. A further 28 stood
here until **fz-kdt.186** — four apiece on `w13`-`w19`, where subject 0 asks a
`:tail` head against an `int` head — and they were never readings at all: the
pair is SEPARATED, the walk does not open it, and neither production nor the
census asks a seat question about it. The one-question groups are counted on
their own thirteen-fixture list by
`compiler2_dispatch_offers_no_runtime_indistinguishable_arm`: 105 groups, all
of them wrapper selections (00277 47, `enum_map_family` 46, `00420` 12), owned
by fz-kdt.179 and fz-kdt.107.

THE SOURCE-ORDER CLASS READS 0, and that zero speaks for 9 plans of 149: a
clause dispatch asks whatever the source patterns ask, and the reader compares
`Region::Type` questions only, so 140 are skipped — on entry plans
`Region::List` 87, `Region::Equal` 18, `Region::TupleArity` 17,
`Region::Guard` 15, and all three `case` plans on a `Region::Equal`. The gate
prints the breakdown and pins the plans and the skips per kind. A `Guard`
cannot be read statically; a `List` or a `TupleArity` can, and reading them is
**fz-kdt.187**'s.

The `case` and `receive` kinds contribute nothing to any of those columns
ANYWHERE, not just here: a corpus walk of the 469 drivable fixtures finds 70
`case` plans and 86 `receive` plans, and zero blind pairs across all 156,
because those sites ask `Region::Equal`, `TupleArity`, `List`, `MapKind`,
`Bitstring` or a guard and almost never a bare `Region::Type`. So the census
fixture list needed no widening for them.

The census is a RATCHET pointing at its tickets, not a target: any other new
entry is a new latent miscompile and wants a ticket, not a re-blessed constant.

The static and the dynamic instrument see different subsets of the same class,
and it takes both to tell them apart. `enum_predicate_search`'s pair is
statically real and dynamically reached only under `arms:6`;
`dispatch_list_head_separates`'s is statically real and never reached at all;
00277's wrapper selections are both — 34 reachable seats statically, 12 escapes
dynamically.

### The dynamic tripwire

The static census reasons about pairs of arms on hand-picked fixtures, and it
reasons about pairs the running program may never build.
`FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP` measures the real thing instead, on the
production path, over whatever the corpus actually runs (fz-kdt.135,
fz-kdt.144): the interpreter answers each dispatch type test under
`PositionScope::Lowered`, which is what the three lowerings can afford, and the
tripwire re-asks the admitted value's own axes under `PositionScope::Full`,
which is what the surface names. A value admitted by the first reading and
refused by the second passed a test no shape of the arm's surface names, which
is precisely a blind routing.

**What the two readings disagree about is the list SPINE.** Every tuple
position is asked identically by both (fz-kdt.138), and scalar and content-blind
axes coincide, so the only gap left is the one the one-sided-filter law names: a
head load is exact on rejection and erasing on acceptance, and the tail is what
no emitted test reads. Under `Full` a list is inside the surface when SOME ONE
clause's element question admits EVERY element — per-clause homogeneity, because
a `ListSig` carries one element type, so `[int] | [:ok]` must not claim
`[1, :ok]`. Each element is asked under `Full` in turn, so a list inside a list
or inside a tuple position walks too. A clause the projection could not shape
(fz-kdt.146's `shape_only` degrade) asks no head, so it has no `Full` content and
reports nothing: honest inertness, not a guess.

The cost is O(clauses × length) per admitted list and O(clauses × outer × inner)
one level of nesting down, which is why it lives behind the env gate and never
on the production answer. The walk stops at anything that is not a cons cell —
the empty list and an improper tail alike — and is bounded at 2^16 elements, so
its termination is a fact of the code rather than of the heap it reads.

Unset, the instrument is off and costs nothing; set to `abort` each finding is
fatal, which is how a single fixture is bisected down to the dispatch; set to
anything else each finding is reported on stderr with the offending VALUE and
the element that broke it, and a corpus census is

    FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP=1 fz2 interp <fixture> 2>&1 >/dev/null \
      | grep -c 'surface-membership escape'

Sweep the whole corpus by looping that over `fixtures2/*.fz
fixtures2/behavior/*.fz`, and re-run it under each legal arrival by adding
`FZ_STRESS_PERMUTE_DISPATCH=<setting>`: an escape the settled order does not
reach is still a latent one. The whole 597-fixture sweep costs about 10s, and
the knob's cost does not separate from that sweep's run-to-run spread —
measured at fz-kdt.144, 9.4-9.8s off against 11.0-13.2s on, and re-measured on a
second machine at 9.0-12.6s off against 8.9-10.6s on. Read it as free at corpus
scale rather than as a number.

**Interpreter only, and that is the whole instrument rather than half of one.**
All three doors answer the same `Lowered` question over the same dispatch plans,
so the escaping POPULATION is door-independent by construction. What differs
between doors is the HARM — `interp` survives on dynamic tags where the native
doors read the element through a grounded accessor — and harm is what the
three-door behaviour sweep above measures.

**The measured population** (fz-kdt.144, 597 fixtures, `interp`). Every fixture
not listed reads 0 at every setting.

| fixture | setting | escapes | owner |
| --- | --- | --- | --- |
| `00277_enum_tier0_fixture` | settled | 12 | fz-kdt.179 |
| `00277_enum_tier0_fixture` | `arms:reverse`, `arms:1` … `arms:6` | 12 | fz-kdt.179 |
| `00277_enum_tier0_fixture` | `wrappers:1`, `wrappers:6`, `wrappers:reverse` | 0 | — |
| `enum_predicate_search` | `arms:6` | 1 | fz-kdt.131 (facet 3) |
| `enum_predicate_search` | settled, every other setting | 0 | — |

`00277` is a construction-wrapper MEMBER SELECTION, not a callsite: a wrapper's
plan for `Enum.reverse(1..7//2, [:tail])`'s reducer tests
`empty_list() → list(int) → list(int | :tail)`, so the accumulator `[1, :tail]`
and its growth (`[3, 1, :tail]`, `[5, 3, 1, :tail]`, four values each) pass
`list(int)`'s head test and run the body compiled for `[integer]`. The covering
member exists and is seated second, because `dispatch_from_callable_flow_edges`
builds a wrapper's rows straight from `flow.first_class_edges` and never calls
`routable_alternatives` — neither fz-kdt.143's drop nor fz-kdt.129/131's
covering seat runs on member selection at all. stdout is right on every door
because the accumulator lane is `ValueRef` in both bodies: boxed element access,
the correlation nobody proved. **The SETTLED wrapper order is the only order
that escapes**, which is fz-kdt.147's shape reborn on the list axis.

WHICH wrapper the report does not say: `observe` prints the value, the element
and the predicate, and no plan site at all, so the twelve cannot be attributed
from this instrument (naming the site is **fz-kdt.187**'s). The static census
reads the sites by name, and there are ten of them on this fixture: `w10`,
`w11` and `w20` carry four members each and `w13`–`w19` carry eleven. `w2` is
not among them — its members are `[]`, `[{any, any}]` and their union, which
hold no int and escape nowhere.

`enum_predicate_search` under `arms:6` is fz-kdt.131's facet 3 measured on the
production path for the first time: `[1, :ok]` reaching a `[integer]` body
through two arms whose heads overlap and neither of whose surfaces contains the
other. It is 0 at the settled arrival, so only the seed reaches it.
`dispatch_list_head_separates` — the written-down reproducer for the same
facet — reads 0 at EVERY setting, because `Enum.all?` consumes the first element
before the recursive dispatch: the values that reach the `[:false | :true]` arm
are `[false]` and `[]`. That pair is statically real and dynamically unreached.

The census stays a RATCHET with names:
`compiler2_no_value_reaches_a_construction_member_that_never_named_it` drives
fifteen named `(fixture, arrival)` pairs in process — the SETTLED arrival of
all nine fixtures that have ever reported, `00277` under `arms:6` and under each
of the three wrapper orders, `enum_predicate_search` under `arms:6`, and
`dispatch_list_head_separates` at the settled arrival (the row that holds its
header's "dynamically unreached" sentence to the tree) — so a
count that moves in either direction is a new latent miscompile or a cure and
wants the table edited deliberately rather than a number re-blessed. The
remaining `arms:` seeds on `00277` are the SWEEP's measurement above, re-read
with the recipe rather than pinned in process, because every one of them reads
what the settled row already pins.

**What it read before the spine.** fz-kdt.119 landed the tuple reading and
measured SEVEN fixtures and 268 occurrences (`00183` 16, `00230` 16, `00418` 4,
`00419` 16, `00420` 106, `enum_take_drop_split` 106, `unused_range_binding` 4),
and they were all one defect: a nested LIST position inside a fold's
accumulator, and a MISSING SPECIALIZATION rather than a blind dispatch. A
reducer is minted beside the fold's initial accumulator and carries that arrow;
`resolve_closure_call` used to intersect every later argument with it, so the
accumulator's ascent stopped one rung short and the accumulator the fold
actually produces got no specialization and no construction member at all.
fz-kdt.132 minted the rung and the tuple population emptied; fz-kdt.138 then made
those positions testable, at which point the two scopes coincided and the
instrument had nothing left to compare. All seven still read 0, and they are in
the ratchet table's first rows so that stays a measurement.

Arm order was the settled targets' order and nothing else before fz-kdt.129 —
the fixpoint's, which is the agenda's — and `enum_predicate_search` seated one
`List.reduce_while_step/3` dispatch's wide arm first under FIFO and its narrow
one first under LIFO. That pair is now seated the same way under both, and
fz-kdt.119 moved WHICH way: the two arms' `{:halt, :false}` and
`{:cont, :true} | {:halt, :false}` states used to be one question, so coverage
had to seat the wide arm first to keep a `{:cont, :true}` out of the narrow
arm's body. Both positions of that state are atoms, the test now asks them, a
`{:cont, :true}` fails the narrow arm's first question outright, and with
nothing left for coverage to protect the second conjunct — precision — seats the
narrow arm first. Measured at the landing: all four schedule lenses stay
byte-identical under FIFO and LIFO, and the corpus dump census stays at the same
three schedule-movers (`00277_enum_tier0_fixture`, `enum_map_family`,
`dead_closure_capture_empty_list`), which carry arms no seat can separate.
Re-measured at fz-kdt.107 step 3: the four lenses are byte-identical still, and
the census is unchanged at three.

The artifact rung materializes a `CallEdge::Dispatch` for the `::Dispatch`
answer: the plan is the runtime type-test graph, while each `DispatchCallArm`
carries the existing impl `CallTarget`, return flow, and extern marshal facts
outside `DispatchMatrix`. Dispatch misses are unreachable for closed receiver
unions and lower to an explicit halt/trap path; there is no residual
protocol-stub outcome in the matrix.

A fired trap is reported at the process-exit boundary as a fault, not unified
with normal completion. Compiler2's `Term::Halt` codegen (the only producer is
the fault traps: `function_clause`, `match_error`, unreachable-control) calls
`fz_exit_fault` after recording the reason atom into `halt_value`, setting
`Process.exit_fault = Some(atom)`. Normal completion never touches the field,
and drivers never infer fault-ness from `halt_value` (a program may
legitimately return a fault-shaped atom). `Compiler2::run_root_jit` reads the
root task's `exit_fault` after `run_until_idle` and returns the reason as an
`Err`; `fz_aot_run_main` reads it before teardown, names the reason on stderr,
and exits nonzero. The backend interpreter needs no marker — its trap is a
Rust `Err` that already propagates to the CLI.

`pattern_dispatch_from_source` is the source-pattern producer. It consumes the
AST-facing `SourcePatternRows`, extracts positive proof paths into `Order::Source`
arms, and keeps pattern-specific payloads as opaque outcome metadata: body id,
leaf bindings, pinned inputs, prepared keys, and guard expressions.
Inline lowering for function heads, `case`, and `with else`, plus interpreter
receive probes and native receive codegen, walk the resulting
`PatternDispatchPlan` directly. Receive accept/reject policy is not encoded in
`DispatchMatrix`; selective receive remains a producer/outcome policy layered
above the same regions. For selective receive specifically, the winning outcome
is not "put the message somewhere and revisit it later". A hit outcome is a
projected outcome-closure payload for the winning clause body; a miss outcome is
"append the full message to the mailbox and stay parked".

Compiler2 semantic reachability is another consumer, not another dispatch
model. `compiler2/dispatch_reachability.rs` interprets the graph's edge proofs
against root input `Ty` rows and uses plan-owned `PatternSubjectRef` paths to
derive every tested projection. It never stores types by `SubjectId` and never
adds type/domain policy to this generic module. Before traversal, a runtime
envelope replaces bare inference templates in positive, recursively inspectable
tuple/list/map/resource slots with `any`, narrows unresolved negative exclusions
instead of widening them, and preserves callable arrows that the pattern graph
cannot inspect. Negative finite variable branches are erased while preserving
their concrete axes; negative cofinite branches with excluded variable IDs
become empty. A cofinite variable axis with no excluded IDs remains ordinary
top. Exact tuple projections lift to their roots;
ambiguous positional list projections keep both edges. Each reachable outcome
retains its refined root inputs for clause analysis, so reachability and clause
binding consume the same proof.

## Vocabulary Boundary

DispatchMatrix has three layers that must stay separate:

- **Region question:** the semantic question, such as "is subject in this type",
  "is this value a cons cell", "is this key present", or "is this value equal to
  that literal or pinned value".
- **Branch evidence:** what becomes true only on a branch. A cons success can
  project head/tail. A map-key-present success can project the map value, even if
  that value is `nil`; the miss branch records absence. A failed empty-list
  question means "not empty list", not "cons".
- **Backend emission:** the current IR can still use `TypeTest`, equality,
  `IsListCons`, `IsEmptyList`, or `MatcherMapGet` plus `IsMatcherMapMiss`.
  Those names are lowering choices, not DispatchMatrix source vocabulary.

Future dispatch changes should add producers on top of this model instead of
adding one-off pattern, protocol, or planner dispatch passes. Graph compilation
is tested with fake outcome handles, callsite-dispatch arm ids, and
source-pattern-derived pattern outcomes. Protocol dispatch and source-pattern
dispatch share the same decision model; runtime helper names that still say
"matcher" are ABI vocabulary, not a separate compiler data model.
