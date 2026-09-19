# Set-Theoretic Types

## Model

A fz type denotes a **set of values**. Subtyping is set inclusion, and the lattice
operations are literal set operations:

```text
A <: B        <=>  ⟦A⟧ ⊆ ⟦B⟧
A and B       =    ⟦A⟧ ∩ ⟦B⟧        (intersect)
A or  B       =    ⟦A⟧ ∪ ⟦B⟧        (union)
A \ B         =    ⟦A⟧ \ ⟦B⟧        (difference)
A is empty    <=>  ⟦A⟧ = ∅          (the decision procedure)
A, B disjoint <=>  ⟦A⟧ ∩ ⟦B⟧ = ∅
```

Everything reduces to deciding emptiness: `is_subtype(a, b)` asks whether
`(a \ b)` is empty; `is_disjoint(a, b)` asks whether `(a and b)` is empty.
Difference is the public subtraction operation. Its descriptor implementation
is exact: it carves each correlated brand/structure case into the structural
outside and the still-structural overlap under the remaining brands (see
"Brands carry their inner" below).

`is_subtype` is NOT a safe "covers everything the other says" test for a
closure-literal column. `emptiness.rs::func_clause_empty` decides `P \ N` for a
negative arrow carrying a `ClosureLit` from `fn_id` and `captures` alone — it
never reads `args` or `ret` — so two arrows over ONE lambda are mutually
subtypes however far apart their signatures are. That is also why a template
arrow and its ground instance come out equivalent: it is `func_clause_empty`'s
capture-subset test on the shared literal that erases the difference, not a
general absorbing property of free vars. A literal whose own capture TYPE is
empty is empty whatever the rest of the clause says — a closure holds exactly
one value per capture slot, so `#3closure[none]` denotes nothing. Two literals
that can name one value MERGE at intern time rather than staying distinct, so
that is where a `none` capture comes from: one brand met at two capture types,
or the ANONYMOUS literal (a `ClosureLit` with no `fn_id`, fz-kdt.127, which is
every brand at once) met with a branded one. (Vars are nominal on their own axis:
`is_subtype(int, α)` and `is_subtype(α, int)` are both false.) The blind spot
is structural — a lambda inside a tuple, a list, a resource payload, a map
field or another arrow's signature is reached the same way.

Callers that need containment rather than the lattice order ask
`Types::row_column_dominates`, which adds equal `free_var_ids` and containment
of `lit_arrow_shapes` — the `(fn_id, captures, args, ret)` evidence subtyping
discards, collected by the same structural walk `free_var_ids` uses — on top of
`is_subtype`. It is memoized under its own NON-symmetric
`ComparisonKey::RowColumnDominates`; the symmetric-key helper is for relations
whose two positions are interchangeable, and this one's are not.

A type is a union across independent **axes**, one per runtime kind, held in
disjunctive normal form (DNF). A `StructureOf` is one such structural union:

```text
basic      presence bits: int, float, binary (str is the binary bit)
atoms      finite-or-cofinite set of atom names   (:ok, :error, nil, true, …)
opaques    finite-or-cofinite set of opaque-type names   (nominal)
vars       finite-or-cofinite set of type-variable ids
tuples     DNF of tuple shapes (nested type per element)
lists      DNF of list shapes  (nested elem type, empty/non-empty flag)
resources  DNF of resource shapes (nested payload type)
funcs      DNF of arrow shapes (arg types + ret type, optional closure lit)
maps       DNF of map shapes   (nested value types)
```

`DescrOf` is an outer finite partition of correlated cases:

```text
DescrOf = BrandCase[]
BrandCase = { brands: finite-or-cofinite names, structure: StructureOf }
```

`brands` is NOT a runtime kind. Within one `BrandCase` it is a conjunctive
refinement over that case's structural axes: top means no brand constraint (the
unbranded case and every brand), while a finite set names nominal refinements.
The outer union is what preserves correlations such as `utf8(binary) | nil`;
there is no global brand factor beside independently-unioned axes.

`nil`, `true`, and `false` live on the `atoms` axis, not on `basic` (`bool_lit` is
`atom_lit("true")` / `atom_lit("false")`). `str` is exactly the `binary` basic bit.

**Numbers have no literal sets — numeric constants are values, not types.** The
lattice deliberately cannot express `int_lit(42)` or `0 | 1`: `int()` and
`float()` are indivisible presence bits, exactly as in Elixir's
`Module.Types.Descr`. Constant dispatch (`def f(0)`) is a value comparison the
matcher performs at runtime; constant map keys ride the lowering as values
(`LoweredMapKey`). A numeric literal written in TYPE position (`@type d :: 0`)
means its kind and emits the `type/numeric-literal-widened` warning
(`compiler2/resolve.rs`). Atoms keep singleton sets because `:ok | :error`
unions are the language's backbone. Compiler2's `int_lit` and
`as_int_singleton` trait methods are documented degenerates for the shared
trait surface.
A value belongs to a descriptor when it belongs to at least one case's structure
AND that case's brand set admits its brand. `any()` is one unconstrained case with
every structural axis at top; `none()` has no cases. A case is empty when its
brand set is empty or all structural axes are empty (structural clauses are
checked recursively with a coinductive memo for recursive shapes). Every value
constructor starts from `Descr::unbranded()`, one case whose brands are top.
`union` appends cases and interning partitions and normalizes them, so bottom is
the identity without letting an empty case widen another case.

DNF construction keeps clause lists hygienic by boolean identity. One clause-
product skeleton (`dnf.rs::dnf_intersect_with`) serves both intersections —
the structural kernel (`Descr::intersect`) and the semantic path
(`Types::intersect`, which collapses same-shape positives through `MergeSig`)
— and it drops duplicate clauses (`A ∨ A = A`), clauses holding a literal
both positively and negatively (`P ∧ ¬P = ∅`), and clauses a `MergeSig` merge
proves empty (`PosMeet::Empty`: tuple arity mismatch, an empty tuple
coordinate or resource payload, a non-empty list sig with no element left).
`dnf_union` drops duplicate clauses and `dnf_neg` skips duplicate factors.

The persistence boundary (`Types::intern`) canonicalizes every descriptor
entering the interner.

First the TUPLE NORMALIZER (`Types::normalize_tuple_axis`). Per clause,
`normalize_tuple_coordinate_difference` rewrites a ground difference whose
cover differs in exactly one coordinate to one rectangle, which also turns a
clause carrying a negative into a plain rectangle. Then
`axis::fuse_tuple_rects` reaches a fixpoint: FUSION merges two rectangles that
agree on every coordinate but one into the single rectangle over the union of
that coordinate (`{A,C} ∨ {B,C} = {A∨B, C}`), and WIDENING grows a coordinate
to the union of that coordinate over its same-arity siblings while the grown
rectangle remains inside the axis union. A rectangle only grows and never past
the union, so the denoted set is invariant and the outcome does not depend on
arrival order. Fusion mints the union coordinate it merges on, so this fold can
spend an interned type to save an identity; the coordinate it builds is interned
through this same boundary and names only older types.

Then, still before the sort, the LIST NORMAL FORM (`emptiness::list_denotation`,
`types/axis.rs`). A `ListSig` denotes `[]` (when `empty`) together with every
non-empty list over `elem`, so a list clause says exactly two things: does it
hold `[]`, and which non-empty lists does it keep. One function reads those two
facts off a clause's factors, and the boundary writes them back as the clause —
one positive sig carrying the fragment and the `[]` flag, one negative sig per
surviving subtraction. So `list(T) ∧ ¬[]` is stored as `non_empty_list(T)`, a
subtraction that removes nothing (`[int] \ non_empty_list(:nil)`) is dropped
instead of kept as a factor, and one that removes the whole fragment leaves
`[]`. Across the axis, `[]` is held as soon as ONE clause holds it, so every
clause that keeps only non-empty lists is widened to hold it too and a bare `[]`
clause is then redundant: `[] ∨ non_empty_list(T)` is `list(T)`. That decision
reads the finished clause SET, never the order a fold arrived in. A merge that
reaches `list(any)` leaves the axis's widest SIG, which absorption below rewrites
to the contentless clause, so the merge feeds the one top spelling rather than
competing with it.
`Descr::union` used to carry the same merge and could not: over the members
`non_empty_list(binary)`, `non_empty_list(:nil)`, `non_empty_list(:nil)`,
`empty_list()`, folding forward gave `list(:nil) | list(binary)` and folding in
reverse `non_empty_list(binary) | list(:nil)` — one union, both already in
canonical clause order, two ids (fz-kdt.48.6). The same denotation reached by
`difference`, `intersect` or substitution was not merged at all.

Element ARITHMETIC — meeting two positives' elements, or meeting a subtraction
with the fragment — is skipped when a clause's elements carry type variables.
The kernel reads a variable as an atom disjoint from everything else, so
`list(α) ∧ list(int)` has no non-empty fragment and
`non_empty_list(α) ∧ ¬non_empty_list(int)` subtracts nothing: both true of the
clause as it stands, neither true once `α` is substituted. Reading the `[]`
flags carries no such risk — substitution never touches them — so a var-bearing
clause that needs no element arithmetic still normalizes.

Then ORDER (`order.rs::ClauseOrder`): every DNF axis is sorted by a total
order, factors inside a clause before clauses inside an axis, so a descriptor's
clause list is a function of its clause set and each clause a function of its
factor set — not of the arrival order that built either. A DNF axis denotes a
set but is stored as a `Vec` and every producer appends, so `A ∨ B` and `B ∨ A`
used to reach the interner as two vectors and be handed two `Ty`s for one type
— and a `Ty` IS the identity of a specialization, so which bodies exist was a
function of the schedule (fz-kdt.105). `Conj::pos` grew the same way inside the
clause product, so `A ∧ B` and `B ∧ A` split one overload in two. Factors have
to be sorted first: a clause compares by its stored factor lists, so the clause
order is a function of the clause set only once each clause is a function of
its own factors. Sorting also puts equal factors adjacent, which is where
`A ∧ A = A` collapses. The order is lexicographic over the structure,
compared in place rather than rendered as text. A comparison records each
normalized pair while it is in flight; re-entering a pair breaks the back edge
as no further structural difference, and a completed pair reuses its verdict.
The walk therefore terminates for regular trees as well as acyclic ones. A
distinct cyclic pair can have the same finite unfolding, so a completed
structural tie also takes the root identity order. `Equal` still means exactly
the same `Ty`; a comparator that could tie two DIFFERENT clauses would hand the
survivor back to arrival order. Structural address vars order by their
`AddrStep` path, never by the mint-order `TypeVarId` behind them.

Storage order reads NOTHING mutable outside the descriptor, the ids it names,
and its completed-tie identity order. That is a hard requirement, not a
preference: the index lookup below is sound only while a descriptor's normal
form cannot move under it. Closure literals are
where it had to be won. A callable can be interned before its owner exists and
`Types::define_callable_origin` registers the typed origin later, so ordering
two literals by their registered origins would rewrite a stored clause order
the moment a registration landed — and one denotation would then take one id
before the registration and another after. Storage therefore orders two
literals by `FnId` alone. The ACTIVATION relation
(`ClauseOrder::for_activation`, reached through `Types::cmp_activation_ty`)
keeps the origin order — typed module/name/arity for a named function,
recursive owner plus structural occurrence for a generated one, the displayed
label only a projection — and it can, because it runs only over activation
surfaces where every literal's origin is registered and asserted to be.
Two residuals are deliberate: a tie broken by two FREE type vars falls back to
mint order, and so does one broken by two closure literals. The stored order of
a funcs axis is therefore mint order, not source order — nothing reads it as
source order, since `TyCanon` sorts its own rendered clause texts, activation
keys go through the activation relation, and every other reader folds or maps
the axis rather than selecting a clause by position.

Then the EMPTY-CLAUSE DROP, on all five axes: a DNF axis denotes the union of
its clauses, so a clause that denotes nothing is that union's identity
(`A ∨ ∅ = A`) and is filtered out. Each axis asks its own
`emptiness::*_clause_empty` (`types/axis.rs`); the tuple axis takes a memoized
`Types::is_empty` shortcut for the common plain-positive product, injected by
the caller so the rule itself holds no cache. Sweeping all five is also what
makes the bottom collapse below exact AND cheap: an axis with no empty clause
left is empty exactly when it holds no clause at all, so the collapse reads the
descriptor structurally instead of re-running the recursion.

Then ABSORPTION (`types/axis.rs`), one rule for the tuple, list, resource, map
and literal-free callable axes. An axis denotes the UNION of its clauses, so a
clause the union of its surviving siblings already covers adds nothing and is dropped
(`A ⊆ B₁ ∨ … ∨ Bₙ ⇒ A ∨ B₁ ∨ … ∨ Bₙ = B₁ ∨ … ∨ Bₙ`), and an axis whose clauses
between them cover the axis IS that axis's top and collapses to it.
Union coverage is strictly stronger than the pairwise containment it replaces:
`list(int)` is inside `empty_list() ∨ non_empty_list(int)` though neither
sibling holds it alone. Exact duplicates are its degenerate case — once the
first is dropped it stops covering its twin, so one survives. The containment
question goes to the shared calculator, by installing the clauses on an
otherwise contentless descriptor and asking `is_subtype`; there is no per-axis
subsumption rule left. Absorption has to run AFTER the sort: it visits in index
order and drops the FIRST of a mutually-covering pair, so without a canonical
order the schedule would still choose which clause lives.

"Semantically equal" means equal under the relation the CALCULATOR answers
with. Resources use the same collective product coverage as tuples: a resource
clause intersects its positive payloads, then `resource_clause_empty` asks
whether the UNION of its negative payloads covers that one-coordinate product.
So `resource(:a|:b)` is inside `resource(:a) ∨ resource(:b)`, and
`resource(int) ∨ resource(not int)` is every resource. Maps use that calculator
over their required fields too. A positive map is open and fixes its tag; a
negative with another required key cannot cover its smallest witness, while a
negative that omits one of the positive keys contributes `any` at that product
coordinate. Different tags never contribute coverage.

Every axis has ONE spelling of its top: the clause with NO factors, which is
what `Descr::any()` already writes on all five axes. That is the whole point of
the rule — an axis written `[ListSig { empty: true, elem: any }]` and an axis
written `[Conj::top()]` denote the same set, so leaving both spellings in play
hands one set two identities, and `any | [any]` stops being `any`. A single
plain clause that IS the axis top is therefore rewritten to the contentless
clause at the same boundary, and `list(any)`,
`empty_list() ∨ non_empty_list(any)` and `any | [any]` all land on it.

What that costs is that a reader projecting a positive signature off a list or
resource clause has to read a contentless clause as the widest signature
(`[any]`, `resource(any)`) rather than as "no list at all": `Descr::as_pure_list`
and `Descr::pure_resource` take the caller's interned `any` for exactly that,
`list_element_type` and `resource_payload_type` already answered `any` there,
and `Types::display` renders each axis top as the widest type a user could
write.

Whether an axis IS its top is one rule (`axis::axis_is_top`) for all five. A
clause with no factors constrains nothing, so an axis carrying one is its top
whatever sits beside it, and that answer belongs to no axis. Otherwise the axis
reads its clauses' positive signatures (`AxisView::plain_top`) and only what
that cannot settle reaches the exact calculator question.

The split falls where it does because a clause carrying a NEGATIVE factor
carves a set no signature comparison can read. A finite union of positive-only
TUPLE clauses is never every tuple — a positive `TupleSig` fixes an arity, and
arity is unbounded — and a finite union of positive-only MAP clauses is never
every map, for the same reason about struct tags. But `{any, any} ∨ ¬{any, any}`
IS every tuple and `%{k: any} ∨ ¬%{k: any}` is every map, so "those axes have no
top to reach" would be false, and the two carvings would intern apart while the
calculator called them equal. The LIST axis answers its positive-only case
exactly — one clause admits `[]` and one admits every element — and the
RESOURCE axis likewise — one clause's payload is every value. Neither rule is
set reasoning; both are read off the kernel's own clause-emptiness rule. `top`
minus a union of plain clauses is the single clause negating them all, and
`emptiness::list_clause_empty` calls that empty exactly when one negated
signature admits `[]` and one negated signature's element swallows the
fragment. Resource payload alternatives and map-field rectangles instead go to
the shared product calculator, which decides whether their union covers the
candidate. A literal-free callable axis does the same; a clause naming a
closure literal instead names a construction layout and does not participate in
callable absorption.

What those two rules ask of a child — "is this every value" — is a question
about the DENOTATION, and `Descr::is_full` is its one implementation:
structural where it can be (`looks_full`), otherwise the exact containment,
guarded by the necessary conditions so the common answer costs no question.
A structural reading ALONE is incomplete, because a retained literal callable
axis can write `f ∨ ¬f` for every callable without looking full. Reading the spelling
instead of the denotation would leave `[x]` and `[any]` two ids and two
canonical forms for one set of lists, the false difference the canon
faithfulness ratchet exists to forbid. The canonical rendering asks the same
function, so the boundary and the oracle cannot disagree about what `any` is.

The literal-free CALLABLE axis is absorbed at the boundary: its arrow signature
does not distinguish runtime callable values. A literal-bearing arrow retains
its capture layout, because transport reads every possible environment and a
capture-subset absorption could erase a real one. Literal-bearing axes get
exact duplicate removal only.

The literal's args and result are not value identity. Before ordering,
`Types::intern` restores a named literal's deterministic owner template and an
anonymous literal's arity-only `any` surface. `ActivationInput` carries the
separate addressed `ActivationSignature`s a contract or call analysis observed.
The value and observation therefore have one owner each: observations cannot
mint a second closure value identity, and normalizing a value cannot erase an
observed call surface.

## Arrow meets and callable application

One positive arrow is a constraint on a callable's behavior over its whole
argument tuple. Therefore two arrows with the same argument vector merge their
return constraints: `(D -> R₁) and (D -> R₂) = D -> (R₁ and R₂)`. Different
argument vectors are an overload and stay as separate positive factors. In
particular, `(A -> R₁) and (B -> R₂)` is not `(A | B) -> (R₁ and R₂)`; that
would both lose result-to-domain correlation and, for more than one argument,
admit the pointwise hull rather than the union of the two input tuples.

The callable module is the one ground positive-arrow application authority. A
callable DNF clause is one possible callable value, so every DNF clause must
cover the input row. Positive arrows inside one clause are instead overload
arms: their domains cover a row collectively. The result partitions the row by
its arm membership, intersects the returns on each overlapping region, and
unions the non-empty regions' answers. Thus `(int -> int) and (binary ->
binary)` accepts `int | binary`, while a union of those two callable values
does not guarantee either domain; and `(any -> int) and (int -> atom)` answers
`none` on `int` but `int` on `binary`.

This evaluator reports a known result, proven uncovered/non-callable input, or
opaque evidence. Negative factors, literal arrows, and free variables are
opaque: projecting them to positive arms would pretend to know a return or
coverage fact they do not provide. The relational matcher may still consume
positive structure with variables; it must not turn an opaque constraint into a
spurious mismatch.

The coverage walk and the dedupe only ever remove, and both visit in index
order, so what they leave is still sorted; a saturated axis is REPLACED by the
one clause that spells its top, and one clause is sorted whatever it is. One pass therefore
suffices, and the pass is idempotent: run on an already-normal descriptor it
sorts a sorted list to itself, finds nothing left to drop, absorb or collapse,
and arrives back where it started. That idempotence is what the index lookup
below turns into a shortcut.

`Types::intern` is absorption's authority, and the list normal form's, but not
their only caller: `TyCanon` applies the same functions to the descriptors it
synthesizes itself, because tuple-coordinate widening builds `Descr` values that
never reach the interner and an unabsorbed or unnormalized coordinate would
render two carvings of one type as two types. One function each, so neither
caller can invent a rule the other does not have.

The two callers do not run the list reading over the same clauses. The boundary
skips element arithmetic on a var-bearing clause (above); the rendering reads
the denotation unconditionally, because a rendering is a claim about what a type
IS and substitution never reaches it. So `non_empty_list(α)` and
`non_empty_list(α) \ non_empty_list(int)` are stored as `[α]` and
`[α] & not([int])`, two ids over one denotation, and both canon as
`fp[L] non_empty_list(α0)`. That is the rendering being right: the oracle
counts the pair as ONE denotation holding two ids, which states the residue — a
variable-aware meet the boundary does not have — as a finding, where rendering
them apart would have hidden it as a difference that is not there.

Last, the BOTTOM COLLAPSE: a descriptor that denotes the empty set is replaced
by `Descr::none()` before an id is assigned, so the empty set has exactly one
`Ty` however it was reached, and `Types::is_empty(t)` holds exactly when `t` is
that id. It asks `Descr::looks_empty()`, which the empty-clause drop above
makes exact; reading the descriptor structurally also means it never descends
through interned children, so it can neither mint the id it is about to reject
nor inherit the emptiness recursion's coinductive assumption about a cycle.

The whole pass runs only when the descriptor is not already in the index
(`TypeInterner::lookup`). The invariant that makes the shortcut sound is that
an interned descriptor's normal form is a pure function of the descriptor:
every pass above reads the descriptor's own bytes and the immutable descriptors
of the ids it names, plus the stable identity that resolves a completed
structural tie. A descriptor the index holds was normalized once, so it is its
own normal form and re-deriving it would rewrite it to itself. Asking first
keeps the boundary's cost proportional to the types a compile mints rather than
to how often it asks for them, and it is the common case by a wide margin: on
the target fixtures the overwhelming majority of intern calls are answered by
the index, which is also what keeps the absorption's containment questions to a
small constant per compile.

A regular component is prepared outside the arena with private local
references. Refining those local nodes against each other answers "which of my
nodes are the same state?"; on its own it does not answer "is one of my states
a handle that already exists?". So the refinement also takes the states of
every recursive handle the component mentions, as fixed nodes, and a mention
becomes a reference to that fixed node rather than an opaque leaf.
`TypeInterner::is_regular` is the id-to-"this names a recursive state"
direction that finding those handles needs; the regular keys in the index are
the other direction, from key to id. Fixed nodes are already minimal, so a
local node can only join one by being bisimilar to it, and the handle set is
closed under its own children, so once a class holds a fixed node every class
it reaches holds one too. A class that lands with a fixed node is that handle,
and the nodes in it resolve to that existing `Ty`.

What is left over is the genuinely new part of the component, and it alone is
keyed and minted. Its bodies name the resolved handles as ordinary published
children; putting a handle back where a symbolic node stood can let clauses
absorb one another, so a body a substitution touched is normalized once more.
The residual then gets a canonical rooted graph key, checked in the same index
that holds ordinary descriptors. A hit returns the existing complete `Ty`s. A
miss maps local references to the final contiguous ids and appends only
completed descriptors plus their direct and regular keys. No incomplete id,
redirect, or second type graph can escape the transaction.

Resolution is bisimulation of the DNF bodies, which is what makes it exact and
cheap to decide. It does not see a containment that holds only through the
types a clause names: with `A = μX. int | [X]`, the component
`μY. int | [[A]] | [Y]` denotes `A` — `is_subtype` says so both ways — but no
partition of the clause structure says so, so it keeps an id of its own.

A component's nodes go through the same tuple-coordinate carving as ordinary
descriptors while they are still local, unresolved references to each other's
eventual `Ty`s. Widening there asks the same "is this wider rectangle already
covered by its siblings" question, but a coordinate that is still a local
reference has no `Descr` to ask it with. The calculator only trusts a
coordinate's covering question when every sibling row is resolved the same
way the trial rectangle is at that coordinate: where the trial names a local
node, every sibling row must name that exact same node (it then cancels out
of the comparison symbolically, whatever the node turns out to mean once
published); where the trial holds a published type, no sibling row may hold
an unresolved local reference at that coordinate instead. Either mismatch has
no sound stand-in for "the type this cyclic reference will eventually have,"
so the calculator declines to claim coverage rather than guess with `any`.
Guessing wide there let two distinct tags from a mutual component's own arms
fuse into one before either arm was published, corrupting the component's own
canonical body.

What clause order canNOT reconcile is a different CARVING of one type:
`{[int], :false} | {[int], :true}` and `{[int], :false | :true}` are one
denotation in two decompositions, and no clause-by-clause rule sees it because
neither carving's clauses contain the other's. The TUPLE NORMALIZER above is
what reconciles them, by rewriting both to the same union of rectangles.

Union-time hygiene is not enough, because clauses are also made
equal AFTER a union — `erase_closure_identity` strips closure brands in place,
turning a legitimate two-brand union into `A ∨ A`, and `funcs = [A, A]` would
otherwise intern as a different `Ty` than `funcs = [A]`. That difference is
what the activation key is built from, so idempotence at the boundary is what
makes the key a join homomorphism (fz-kdt.80). A debug-build assert in
`TypeInterner::intern` (`debug_assert_dnf_axes_hygienic`) checks the
empty-clause invariant on all five axes, that every absorbable axis has nothing
left to absorb, and callable idempotence; it runs on an index miss, so
it costs one sweep per distinct descriptor. The tuple-emptiness
recursion (`emptiness::phi_tuple`) returns early on an empty coordinate and drops
negations disjoint from the product, so it explores only inhabited splits
instead of fanning out `arity^|negs|` branches on any ONE call; pruning alone
does not stop the same `(coordinates, negations)` subproblem from being
re-asked from every branch of an enclosing recursion (two mutually recursive
tuple-tagged clauses, for instance), so `phi_tuple` and `Descr::is_empty_memo`
both answer through `emptiness::Memo`, one result cache keyed on
`emptiness::Operand` (`MemoKey::Tuple`/`MemoKey::Descr`) and shared across
every branch of one top-level emptiness question. Each coordinate an
`Operand` carries is either the interned `Ty` itself, compared and hashed by
id, or, for a descriptor that algebra (intersect/diff/union) has just built
and not yet interned, a reference-counted `Descr` compared and hashed by
content; touching an already-interned coordinate never allocates or clones
one. `Memo` runs Tarjan's SCC algorithm on the
fly over its own call graph: a witness (`false`) is cached the instant it is
found, cyclic or not, because an over-optimistic coinductive guess can only
ever make a computation look MORE empty, never manufacture a witness; an
empty (`true`) result is cached only once the strongly-connected component
that produced it closes with no witness anywhere inside it, so every member
of a cycle becomes cacheable together, not just the subproblem that happened
to close the recursion.

Callable emptiness uses the same proof shape without giving a partition an
integer identity. For a negative arrow `S -> V`, a positive-arrow partition
can witness an escaping callable precisely when both `S \ union(selected
inputs)` and `intersection(unselected returns) \ V` are inhabited. The
calculator walks that partition recursively, carrying those two residual
descriptors. Selecting a positive shrinks only the input residual; leaving it
unselected shrinks only the output residual. An empty residual can never become
inhabited again, so that subtree is exact to prune. This makes the decision
independent of the number of positive arrows while retaining the same shared
`Memo` as the only child authority.

## One implementation, shared trait

Consumers ask type questions through the `Types` trait (`src/types/mod.rs`), not by
inspecting a representation. The active implementation is compiler2's
`Types` (`src/compiler2/types/`): `Ty(u32)`, an interned id into one owning
interner. Its structural `Descr` stays private and the id space is
compiler2-owned. See [`type-world`](type-world.md) for the ownership and why
id-equality is what lets facts detect change without hashing.

A `Ty` handle is meaningful only with the implementation value that produced it,
so handles from two `Types` instances are never composed.

The trait is the abstraction boundary for construction, projection, substitution,
nominal disjointness, widening, and equivalence:

- `Types` default methods compose existing hooks (`bool_lit`, `is_equivalent`).
- An implementation supplies the representation primitives: constructors, lattice
  operations, shape projections, subtype/disjointness decisions, and the
  widening/classification hooks.
- The implementation's own tests cover representation mechanics only — DNF
  normalization, axis views, interning — while implementation-agnostic semantics are
  asserted once through the shared conformance and smoke suites.

## Schemes vs concrete facts

Free type variables are meaningful only inside a **type scheme** — a parametric
promise such as `forall a b. (a, b) -> {a, b}`. At a callsite the scheme is
instantiated by collecting a substitution from declared parameter patterns and the
caller's witness types, then applying it to the result pattern:

```text
params  : [a, b]
witness : [1, :ok]
sigma   : a := 1, b := :ok
result  : {a, b}[sigma] = {1, :ok}
```

Witness collection is structural and walks only shapes that preserve correlation
clearly enough to bind variables: tuples positionally, list elements, resource
payloads, callable arrows (args and ret), and map fields where keys align. A
variable can be determined by a nested position, not only a top-level parameter:

```text
param   : (a, b) -> {:cont, b} | {:halt, c}
witness : (integer, {:not_found, int}) ->
            {:cont, {:not_found, int}} | {:halt, {:found, int}}
sigma   : a := integer
          b := {:not_found, int}
          c := {:found, int}
```

This is the load-bearing case for higher-order functions such as
`Enum.reduce_while/3`: the accumulator variable is witnessed by the initial
accumulator and the reducer's `{:cont, b}` payload. The halt payload has its own
variable when the contract allows a search result to differ from the accumulator
type.

Witness collection keeps evidence three-valued so a safe-fallback projection is not
mistaken for proof:

```text
Known     this position produced usable substitution evidence
Unknown   this position produced no evidence; keep walking other positions
Invalid   this position is incompatible with the declared shape
```

**The boundary rule is load-bearing:** a scheme may contain free variables; a
complete executable fact may not. A `Ty` with free variables can live in a declared
spec, an arrow clause, or an underconstrained result, but a *settled* return fact or
activation key must be a known concrete type, a boundary-erased dynamic value, or a
diagnostic — never a free variable, and never `none` standing in for "not proven
yet" (see [`semantic-fixpoint`](semantic-fixpoint.md)). Compiler2 now owns
contract-aware arrow matching; `src/specs` only carries the structural shape
model described in [`specs`](specs.md).

## Brands carry their inner; opaques are nominal tags

`brands` and `opaques` are **nominal refinements** over structural representations.
They are carried differently because they mean different things. A brand `B`
declared `@type B :: refines U` creates one correlated case whose structural
payload is `U` and whose brands are `{B}` — the same values, fewer of them. An
opaque is a pure nominal tag on its own kind axis: `opaque_of("T")` sets only the
`opaques` axis, so the tag is not a subtype of the plain representation it hides.

```text
mint_brand(binary, "utf8")  : [{ brands = {utf8}, structure = { basic = binary } }]
plain binary                : [{ brands = any,    structure = { basic = binary } }]
opaque_of("T")              : [{ brands = any,    structure = { opaques = {T} } }]
```

An unbranded type's case admits every brand, not no brand: `binary` constrains
nothing about brands, so `utf8 <: binary` — dropping the refinement leaves a
structural `binary` — while a plain `binary` is NOT a `utf8`, because `any ⊄
{utf8}`. The
direction is the whole point: a `@spec` position declared `binary` accepts a
`utf8` argument, and a position declared `utf8` rejects a bare `binary`
(`spec/violation`). Opaque tags make two distinct opaque names lattice-disjoint,
and disjoint from plain structural values unless a consumer explicitly combines
the tag with structural axes.

A value carries at most ONE brand. That is a rule of the LANGUAGE, not an
artefact: there is no intersection type expression, so `Positive and Even` is
unwritable, and the lattice reads the meet of two brands over one inner as
EMPTY. `Meters or int` is `int`, and `Meters and Feet` is `none`.

`Descr::diff` is exact across the outer cases. For each minuend/subtrahend pair
it keeps `(structure \\ other_structure, minuend_brands)` and the overlapping
structure under `minuend_brands \\ other_brands`; further cases repeat the carve.
Thus `utf8(binary) | nil` remains two correlated arms, and subtracting either
arm cannot release the other arm's brand. `Descr::neg_structure` is only the
private complement of one case's structural axes; the outer difference is the
authority for the full correlated result.

A bottom therefore arrives in more than one descriptor shape: `Descr::none()`
has no cases, a case with an empty brand set is uninhabited even when its
structure is inhabited, and a tuple with an empty coordinate empties through a
structural axis. They all denote the same set, so `Types::intern` answers every
provably empty descriptor with the one `none` identity, and `Types::is_empty(t)`
holds exactly when `t` is that id. Descriptor arithmetic runs BEFORE interning
and still meets the several shapes, so `Descr::looks_empty()` — never
`== Descr::none()` — stays the descriptor-level bottom test that `union` asks
before it admits a case.

A refinement renders as a refinement, never as a union: `utf8(binary)`,
`not(Meters)(int)`, `(Feet | Meters)(int)`. Rendering it `binary | utf8` would
read as a SUPERTYPE of `binary`, which is the lattice inverted. `display` and
`TyCanon` share the one renderer (`format::brand_refinement`), so the two
surfaces cannot drift.

The case partition is canonical at every interning boundary. It splits every
mentioned name into a singleton cell plus the cofinite residual, unions and
normalizes the structural payload admitted by each cell, drops structurally
empty cells without querying unresolved recursive locals, then groups equal
payloads back into finite/cofinite cases in deterministic order. Ordinary and
regular-component interning use this one construction. Consequently overlapping
carvings, input order, and productive recursive references have one `Ty`
identity, while `utf8(binary) | nil` rejects a bare binary exactly.

Because brand inners live in the symbol, **brand questions are answered from the
symbol's own structure** — there is no side map and nothing about a name is
looked up. `mint_brand(inner, name)` is the constructor that establishes a
brand; it is called once, where the name is defined (see
[`type-naming`](type-naming.md)), so the symbol is complete from birth. There is
no constructor for a bare tag with no inner: a refinement of nothing denotes
nothing. Opaque source definitions publish the tag itself. Structs are not
opaques: a `MapSig` carries a `StructTag` and its fields in one atomic record
leaf. The tag's parsed `ModuleName` owns equality, hashing, and order; its
`ModuleId` identifies the World dependency. Nominal protocol targets use the
typed `OpaqueTag::ProtocolTarget(ModuleName)` variant of the existing opaque
set axis, distinct from ordinary `OpaqueTag::Named(String)` source names.

**Brands carry no runtime witness.** There is no brand `ValueKind` (the runtime
kinds are Bitstring/ProcBin/Struct/…; see [`any-value`](any-value.md)), and the
runtime compares structure and bytes, so a `utf8` value is indistinguishable from
the binary it wraps. `erase_nominal` is the type-level expression of that fact: it
ignores each case's `brands` set and drops the `opaques` axis, keeping the
structural axes that remain and recursing through every structural position, so a
brand nested inside a tuple is discharged too. Ignoring the case set IS the whole
brand erasure, because the inner is already the structural payload beside it. A
pure opaque tag with no structural axes over-approximates to `any()` so the erased
set is never too small. The runtime type predicate reads the same way: it never
consults the brand set.

## Two models: typing vs runtime

Two different questions get two different models. Both are decided structurally
from the type value itself — no carrier of nominal maps is threaded into the call:

```text
TYPING question    "is this assignment / dispatch / parameter / FFI legal?"
                   -> brand-AWARE. Brands count. A utf8 parameter rejects a bare
                      binary. is_disjoint / is_subtype use the full lattice.

RUNTIME question   "can these two values be equal? can this pattern match?"
                   -> brand-BLIND. The runtime erases brands and == compares bytes.
                      is_value_disjoint uses the brand-erased lattice.
```

`is_value_disjoint(a, b)` erases nominal tags from both operands and asks whether the
results intersect emptily — set-equal to `is_disjoint(erase_nominal(a),
erase_nominal(b))`. It is the only disjointness that may authorize folding `==`/`!=`
or pruning a pattern arm.

```text
is_value_disjoint(utf8, binary)        = false    (overlap -> == runs)
is_value_disjoint(utf8, int)           = true     (a binary is never an int)
is_value_disjoint(:ok, :error)         = true     (distinct atom singletons)
```

## Which predicate, where

The choice of predicate follows the question, not the call site:

```text
== / != fold, pattern-literal match, guard, runtime type test
    ->  is_value_disjoint / runtime_type_predicate   (value; the slot is never read)
@spec argument coverage (arrow_set_covers), extern contracts, dispatch planning
    ->  is_subtype                                   (typing; the slot is compared)
```

There is one runtime-equality relation, `is_value_disjoint`, and every value site
consults it; a literal/guard comparison and a pattern-arm prune lower to that same
brand-blind question. The case's brand set is a TYPING fact only: a runtime test
is built by `Types::runtime_type_predicate`, which never reads it, so no
runtime test can separate a `utf8` from the binary it wraps. A brand is checked
where types are checked — spec positions, dispatch, boundaries — and nowhere
else.

## Struct field types

A struct schema has two separate source facts, and the type model joins them:

```text
defstruct [:first, :last, :step]              # field order
@type t :: %Range{first: integer, ...}        # field types
```

A struct value's hard type is one tagged map signature: typed `ModuleId`, stable
qualified display name, and declared fields are conjunctive. Plain maps use the
disjoint `MapTag::Plain`; therefore `%Range{first: integer}` cannot become
`%{first: integer}` during overload carving. Record-axis top contains both
families, while `map_top` contains only plain maps. Runtime test envelopes derive
the observable schema-tag question by clearing positive field constraints;
positional tuple storage is derived later from the settled schema, never unioned
into the semantic type. Unknown or ambiguous field projection stays `any`.

The two runtime envelopes preserve different evidence through the same
polarity-aware structural walk. `runtime_envelope` prepares semantic projection:
it retains tagged-record fields and recursively widens unresolved field types,
while preserving callable typing. `runtime_type_test_envelope` prepares an
observable predicate: it keeps a struct's tag and a callable's construction
identity, erasing positive struct fields and callable arrows. A shaped negative
struct remains conservative on that predicate surface because a schema-only
test cannot reject just the excluded field values.

## Proof gates

```text
cargo test --lib compiler2::types   # the interned implementation
cargo test --lib dispatch_matrix    # shared generic dispatch/type-region model
cargo test --lib brand_lattice_law  # the refinement direction, by construction
cargo test value_disjoint_soundness_table
cargo test value_disjoint_nested_in_tuple_is_false
```

The fixture corpus pins that `==`, `case`-match, and guard agree across the execution
paths on branded values (`bsx_nested_eq`, `bsx_nested_match`, `bsx_guard_eq`), and
that the typing side is brand-AWARE in both directions: `brand_refines_its_inner`
passes a branded value to an inner-typed `@spec`, and `brand_rejects_a_bare_inner`
is a `spec/violation` for the bare inner at a brand-typed one.
