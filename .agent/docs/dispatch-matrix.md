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
Two targets that project to ONE question are not two alternatives — nothing but
their order would decide which body runs, and that order is the scheduler's. A
target is therefore dropped when a sibling both (a) is runtime-indistinguishable
from it and (b) *stands in for* it: names the SAME callee and accepts a strictly
wider domain. A callsite left with one destination is a `Direct` call rather
than a one-armed dispatch.

(b) is judged on the OBSERVABLE surfaces — the settled `surface_inputs` run
through `Types::runtime_type_test_envelope`, which is the same projection the
plan's rows are built from — not on the settled semantic types. The envelope
erases what no runtime test can read back off a value: a callable argument
keeps its literal `fn_id` and loses its arrow and its captures, because a
closure object's heap word at `+8` is the code it was minted from and nothing
else about it survives into the value.

A callable position is therefore a real question, and it is what separates
`Range.reduce_step/6`'s `({:cont, int} | {:halt, int}, #66closure[])` from its
`({:cont, int}, #68closure[])` sibling by its reducer. Before the callable axis
existed the pair asked one question, neither arm contained the other, and
`:halt` was one legal arm order away from being read as a continue. Now each arm
is reached by the values its own reducer travelled with. What the callable axis
does NOT reach is one callable at two capture layouts: `#66closure[int]` and
`#66closure[float]` are one code pointer, and the capture record the runtime
could read back is not on this axis (fz-kdt.127).

The callable envelope is applied AT EVERY DEPTH (fz-kdt.119), not only to a
top-level argument. A closure nested in a tuple is read by the same one
comparison as a top-level one, so `{:tag, #66(int)}` and `{:tag, #66(float)}`
are one observable and `{:tag, #66}` and `{:tag, #68}` are two. Widening a
nested callable to `fun_top` instead would reproduce the defect above one tuple
deep, and leave a depth-0/depth-1 seam nothing in the runtime justifies.

Dropping does not decide a routing. Every question an indistinguishable
group's rows ask projects to one and the same `RuntimeTypePredicate` — the
rows still carry distinct observable types and the plan still emits a test per
row, but no test it can emit separates the group, so the member the graph
reaches first receives every value the group can see — one member was going to
get them all whatever the arrival order. The rule only decides WHICH: the
survivors are the maximal elements of the observable containment order,
computed order-independently. Where one maximal member exists it is the only
choice complete on every axis a runtime test can see; where two maximal arms
are incomparable both stay and that pair remains order-decided (this corrects
fz-kdt.104's inherited "unique maximal survivor" phrasing — uniqueness holds
per containment CHAIN, not per question class). Every routing reachable after
the drop is one some legal arm order already produced, which is what makes it
safe; what it removes is the dependence on that order. Two adjacent facts
close the loop: a drop to a single destination converts the plan to a
`Direct` call, which also removes the plan's fail node — a value outside
every arm's observable domain would have trapped at base and now routes to
the survivor; that conversion is fz-kdt.104's pre-existing `sole_destination`
and is fenced by the semantic analysis, not by this rule. And a drop cannot
ground a call it should not: `call_destinations` has exactly one consumer, at
artifact materialization — the semantic fixpoint, `RuntimeDemand`, and
transport never read it, so dropping an arm cannot shrink a
`CallableDemand.targets` count or manufacture a `CallEdge::Direct`.

Both halves of (b) are load-bearing. Domain containment alone is not behavioral
completeness — a multi-target summary normally names one target per selected
callee, which is exactly what protocol dispatch is, and a wider domain sitting
on a different function's body is no stand-in at all. And one-way containment is
not (a): when the questions differ the plan CAN separate the pair, so both
survive. What separability does not buy is order-independence. A test is coarser
than the surface it was projected from, so a value can pass an arm's test
without belonging to the domain that test was projected from, and seating
decides which arm receives it — order costs meaning wherever two tests overlap,
and that is fz-kdt.107's subject one rung wider than the arms asking ONE
question. (fz-kdt.129 corrects the "order costs precision, not meaning"
phrasing this paragraph inherited; the measurement is under *Seating*.) A
`:timeout` arm beside an `any` arm is the benign case — the atom test is exact,
so nothing but a `:timeout` passes it — and the narrower TEST is seated first.

Twins with no stand-in between them (neither observable domain
contains the other, or two different functions) also survive and stay
order-decided — including arms alike everywhere the runtime CAN look and
different only where it cannot, where containment is mutual and strictness
keeps both.

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
**construction-wrapper member order** is a `BTreeSet<CallableSurface>` walked in
interned-id order — the type interner's mint order, which is the agenda's again;
`jobs/transport.rs` derives the wrapper's members AND its selection plan from
that one list, and fz-kdt.108 welded a selection row's `body_id` to its member's
index, so the list itself is the only place either can be reordered. It is
reordered where it is built, in `jobs/runtime_demand.rs`, before members,
selection, boundary resolutions or the flow's resolution list derive from it.

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
| callables | separating | passing is being MINTED FROM a named function -- identity, not captures; honest only while the same-fn-id/different-capture shape compiles on no path (fz-kdt.127) |
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
representation's own owner — `matches_list_head` through a `ListHeadReader`,
`emit_list_axis` through `RuntimeTestEmitter::list_head` — and the head question
is asked INSIDE the cons branch and nowhere else, so a head-blind or `[]`-only
test emits and answers exactly what it did before. The nested question is a full
`RuntimeTypePredicate`, so an arity reachable only through a head is an arity
every lowering must register a schema for; `RuntimeTypePredicate::sub_predicates`
is the ONE walk that reports them, matched exhaustively over the axis table so
the next nested axis cannot forget to answer (**fz-kdt.145**).

**What the head does not buy.** Group-splitting costs fz-kdt.118's drop: `[int]`
and `[int | :ok]` used to be one question, so the narrower was dropped as
unroutable; they are two questions now, both survive, and the extra body is real
native code. That growth is **fz-kdt.143**'s. And a pair whose heads overlap
while neither surface contains the other is not reachable by any seat —
`enum_predicate_search`'s two, which **fz-kdt.131** owns.

**The Scope-A carve-out.** A position that can hold a LIST is not tested at all
(`lowering_tests_position`), by the lattice and by all three lowerings alike.
Testing only such a position's non-list axes would make the test STRICTER than
the type — a position's question is a disjunction and dropping a disjunct
rejects values the arm's surface names — so the choice is to decide the list
axis there or to be blind, and deciding it separates `{[], int}` from
`{[int], int}`, which wakes the dead-and-broken accumulator specialization
**fz-kdt.132** owns. Blind is the over-approximation, and it is what this layer
said everywhere before per-position shapes existed. A blind position therefore
counts as overlapping AND as erasing: what a lowering declines to ask, a seat
may not claim as separation. **fz-kdt.138** is Scope B, which retires it.

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

Neither containment is the criterion on its own. SURFACE COVERAGE is: `covers`
holds of `(early, late)` when, at every position where their tests could both
admit a value on an ERASING axis (`overlaps_on_an_erasing_axis`, which reads the
`AxisPrecision` table above), `early`'s surface already contains `late`'s. "The
tests differ" is not separation on an erasing axis: `[int]` and `[int | :ok]`
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
  order. The carve-out is the safety story — no test the plan emits separates a
  group's members, so their order decides which body their shared values run,
  and fz-kdt.107 prototyped canonically ordering them and got `{:done, 3}` where
  `{:halted, 3}` was due.
- groups start in arrival order, and group `x` is moved ahead of group `y` when

      covers(x, y) and ( not covers(y, x) or test(x) strictly inside test(y) )

  The first disjunct is the OBLIGATION — only one direction is escape-free, so
  take it. The second is the PRECISION preference — both directions are
  escape-free, so hand a value both tests admit to the arm that named it most
  precisely. The relation is antisymmetric: if both directions held, both would
  need `covers` both ways, so both would rest on strict mutual containment of
  the tests, which makes the tests equal and the two groups one.
- where NEITHER group covers the other, no seat is escape-free and the rule
  declines to have an opinion: the pair keeps arrival order. That is fz-kdt.107's
  inseparable class one rung wider, and **fz-kdt.131** owns it. The cure is a
  runtime test that can see what the body relies on — fz-kdt.119's per-position
  tuple tags, fz-kdt.107 step 3's list elements — not a cleverer sort.

The correction is one backward insertion pass: each group walks left past
already-seated groups for as long as the relation holds of the pair, and stops
at the first group it may not pass. A permutation comes out, so the seat is
TOTAL by construction and needs no tie-break to fall through to, and it is a
deterministic function of the arms and their arrival order. Stopping at the
first refusal is a requirement, not a compromise: passing a group means passing
everything between. `covers` is not transitive — two groups can be blind at
different positions — so no rank or comparator linearizes it, which is why the
pass is an explicit insertion rather than a sort.

### What the seat guarantees

Every pair whose seat differs from arrival order was individually checked and
moved only under `covers`, which admits no blind escape; every other pair sits
exactly as arrival left it. So **the seat's blind escapes are a SUBSET of
arrival order's** — this rule can only ever remove one, never add one. A
`debug_assert` in `specificity_order` holds every callsite of every debug
compile to it, and
`compiler2_dispatch_seats_the_covering_arm_where_one_covers` reads the same
property back off the landed artifact across the arm-order census.

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

TWO survive, both in `enum_predicate_search`: `[:false | :nil]` seated before
`[int | :nil]`, and `[:false | :true]` before `[int | :ok | :true]`. Their heads
genuinely OVERLAP — on `:nil` and on `:true` — and neither surface contains the
other, so no seat is escape-free and arrival stands. That is **fz-kdt.131**'s
facet 3, not a head the axis failed to read, and its cure is a repr-level or
minting-level decision rather than an ordering rule. The reproducer fixture
`dispatch_list_head_separates` carries the same pair on purpose, so the census
reads three.

The census is a RATCHET pointing at fz-kdt.131, not a target: any other new
entry is a new latent miscompile and wants a ticket, not a re-blessed constant.

### The dynamic tripwire

The static census reasons about pairs of arms on hand-picked fixtures.
`FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP` measures the real thing instead, on the
production path, over whatever the corpus actually runs (fz-kdt.135): the
interpreter answers each dispatch type test as the lowerings do — under
`PositionScope::Lowered`, blind where they are blind — and then re-asks the
tuple axis under `PositionScope::Full`, which looks at the positions they skip.
The LIST axis is not re-asked; that reading becomes possible now that a head
carries a predicate of its own, and it is **fz-kdt.144**, deliberately left out
so the 268-escape baseline stays one population's comparand.
A value admitted by the first reading and refused by the second passed a test no
shape of the arm's surface names, which is precisely a blind routing. Unset, it
is off and costs nothing; set to `abort` each finding is fatal, which is how a
single fixture is bisected down to the dispatch; set to anything else each
finding is reported on stderr, and a corpus census is

    FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP=1 fz2 interp <fixture> 2>&1 >/dev/null \
      | grep -c 'surface-membership escape'

The instrument has no reading before fz-kdt.119 — without per-position shapes
there is no record of what an arm's surface named — so its baseline is the
landing's own measurement: SEVEN fixtures, 268 occurrences.

| fixture | occurrences |
| --- | --- |
| `00183_enum_take_list_range` | 16 |
| `00230_enum_take_chained` | 16 |
| `00418_enum_count_range` | 4 |
| `00419_enum_take_mixed` | 16 |
| `00420_enum_take_drop_split` | 106 |
| `enum_take_drop_split` | 106 |
| `unused_range_binding` | 4 |

Every one is a nested LIST position — the Scope-A carve-out, blind on purpose —
and the two at 106 are the same program reached twice and are what fz-kdt.132
owns. These are LATENT SITES, not regressions: like the 19-escape census this is
a ratchet, and a new entry wants a ticket rather than a re-blessed constant.

**All 268 are decided by the construction-wrapper member order** (fz-kdt.141).
Re-running the census under `FZ_STRESS_PERMUTE_DISPATCH`: `arms:` seeds move it
by ZERO — the whole population lives on the wrapper surface, not the callsite
one — while `wrappers:1` takes it to 68 and `wrappers:6` to 20, with five of the
seven fixtures going to zero and `enum_take_drop_split` going 106 → 34 → 10, on
identical stdout everywhere. So the number is not a fact about the program: it
is a fact about which member the interner's mint order happened to put first,
and the settled order is the WORST of the orders measured. That is the same
blindness read from the other side — nothing separates the members, so whichever
comes first takes every value, and the escapes are the values whose surface that
member does not name.

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
