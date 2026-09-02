//! The permanent ratchet for the canonical external form.
//!
//! `canon(a) == canon(b) && a != b` is exactly "one type, two identities" — the
//! interner canonicalization defect fz-kdt.48 records. This file is that
//! defect's regression guard: it does not fix it, it makes it impossible for a
//! canonical rendering to start lying about it.

use std::collections::HashMap;
use std::sync::Arc;

use super::canon::{canon_backend_program, function_label};
use super::dump::DumpStage;
use super::identity::{ExecutableNeed, FunctionId, RootId};
use super::types::{Ty, TyCanon, Types};
use super::{CodeSubmission, Compiler2, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// The two fixtures the ticket names. Both are driven to their settled world;
/// the canon sweep then reads the WHOLE interned arena, not a hand-picked
/// sample, so a type minted anywhere in the compile is covered.
const TARGETS: [(&str, &str); 2] = [
    (
        "fixtures2/00420_enum_take_drop_split.fz",
        include_str!("../../fixtures2/00420_enum_take_drop_split.fz"),
    ),
    (
        "fixtures2/behavior/fz_f98_range_map_converges.fz",
        include_str!("../../fixtures2/behavior/fz_f98_range_map_converges.fz"),
    ),
];

/// Drives one fixture to its published `BackendProgram` — the same stage the
/// `--dump backend` path reaches — and renders it.
fn canon_of(name: &str, text: &str) -> String {
    let (mut compiler, root) = submit(name, text);
    compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("{name} should reach a backend program: {error}"));
    let world = compiler.world();
    canon_backend_program(world, &world.backend_program(root))
}

fn submit(name: &str, text: &str) -> (Compiler2<ConfiguredTelemetry>, RootId) {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: text.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    (compiler, root)
}

fn drive_fixture(name: &str, text: &str) -> Compiler2<ConfiguredTelemetry> {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: text.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive();
    compiler
}

fn equivalent(types: &Types, left: Ty, right: Ty) -> bool {
    types.is_subtype(&left, &right) && types.is_subtype(&right, &left)
}

/// `canon(a) == canon(b)` exactly when `a` and `b` are mutually subtype, over
/// the full arena of both target fixtures.
///
/// Two things keep an all-pairs claim over ~1.4k types affordable, and both are
/// exact — neither weakens what is asserted.
///
/// The FINGERPRINT that opens every canonical form is invariant under type
/// equivalence (see `types::canon::descr_fingerprint`), so two types carrying
/// different fingerprints are inequivalent by construction and never need a
/// semantic check.
///
/// Inside one fingerprint group, EQUIVALENCE IS TRANSITIVE. Group the types by
/// their canonical form; prove each class internally equivalent against its own
/// head (linear); then prove distinct heads pairwise inequivalent. Every
/// cross-class pair follows: `x ≡ head(A)`, `y ≡ head(B)`, `head(A) ≢ head(B)`.
///
/// Measured red-first: a canon WITHOUT the tuple-coordinate widening fails here
/// on `{list(int), :false} | {list(int), :true}` against
/// `{list(int), :false | :true}` — one union carved two ways, which no pairwise
/// clause subsumption can reconcile.
#[test]
fn canon_is_faithful_over_the_full_arena_of_both_target_fixtures() {
    for (name, text) in TARGETS {
        let compiler = drive_fixture(name, text);
        let world = compiler.world();
        let types = world.types();
        let labels = |fn_id| function_label(world, FunctionId::from_fn_id(fn_id));
        let mut canon = TyCanon::new(&labels);

        let arena = types.interned_tys();
        let mut groups: HashMap<Arc<str>, Vec<Ty>> = HashMap::new();
        for ty in &arena {
            groups.entry(canon.fingerprint(types, *ty)).or_default().push(*ty);
        }

        let mut collapsed = 0_usize;
        for group in groups.values() {
            let mut classes: HashMap<Arc<str>, Vec<Ty>> = HashMap::new();
            for ty in group {
                classes.entry(canon.render(types, *ty)).or_default().push(*ty);
            }
            for (form, class) in &classes {
                let head = class[0];
                for member in &class[1..] {
                    assert!(
                        equivalent(types, head, *member),
                        "{name}: Ty({}) and Ty({}) share a canonical form but are not mutually \
                         subtype -- canon claimed a false equivalence\n  {form}",
                        head.as_u32(),
                        member.as_u32(),
                    );
                }
                collapsed += class.len() - 1;
            }

            let heads: Vec<Ty> = classes.values().map(|class| class[0]).collect();
            for (index, left) in heads.iter().enumerate() {
                for right in &heads[index + 1..] {
                    assert!(
                        !equivalent(types, *left, *right),
                        "{name}: Ty({}) and Ty({}) are mutually subtype but render differently\n  \
                         left:  {}\n  right: {}",
                        left.as_u32(),
                        right.as_u32(),
                        canon.render(types, *left),
                        canon.render(types, *right),
                    );
                }
            }
        }

        // Pins the CURRENT interner defect (fz-kdt.48): the arena really does
        // carry distinct ids for one type, so the sweep above is proving canon
        // collapses a measured defect rather than passing vacuously. When
        // fz-kdt.48 lands this expectation goes to zero and the sweep keeps its
        // full value.
        assert!(
            collapsed > 0,
            "{name}: expected the arena to still carry mutually-subtype distinct ids (fz-kdt.48); \
             if that defect is fixed, update this expectation to zero"
        );
    }
}

/// The measured display hole, pinned directly: the lattice distinguishes three
/// list forms and `Types::display` renders two of them identically as `[T]`.
/// A canonical form that inherited that would report two different types equal.
#[test]
fn canon_distinguishes_the_three_list_forms_display_conflates() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    let (empty, possibly_empty, non_empty) = {
        let types = compiler.types_mut_for_test();
        let int = types.int();
        (types.empty_list(), types.list(int), types.non_empty_list(int))
    };
    let world = compiler.world();
    let types = world.types();
    let labels = |fn_id| function_label(world, FunctionId::from_fn_id(fn_id));
    let mut canon = TyCanon::new(&labels);

    assert_eq!(
        types.display(&possibly_empty),
        types.display(&non_empty),
        "the display hole this test guards against must still be present"
    );
    let rendered: Vec<String> = [empty, possibly_empty, non_empty]
        .iter()
        .map(|ty| canon.render(types, *ty).to_string())
        .collect();
    assert_eq!(
        rendered.len(),
        rendered.iter().collect::<std::collections::HashSet<_>>().len(),
        "canon must render empty, possibly-empty and non-empty lists distinctly: {rendered:?}"
    );
}

/// No interned id may survive into the canonical form. An id is an arena
/// position in one `World`, so a rendering that carries one is not comparable
/// across processes, versions, or a build cache — which is the whole point of
/// having the form at all.
#[test]
fn canon_of_a_backend_program_carries_no_interned_id() {
    let (name, text) = TARGETS[1];
    let rendered = canon_of(name, text);

    for id in [
        "Ty(",
        "ValueId(",
        "CallSiteId(",
        "ControlEntryId(",
        "ShapeId(",
        "LaneId(",
        "CallableId(",
        "BoundaryId(",
        "FunctionId(",
        "ModuleId(",
        "CodeId(",
        "FnId(",
        "SubjectId(",
        "OutcomeId(",
    ] {
        assert!(
            !rendered.contains(id),
            "the canonical form must not carry the interned id `{id}`"
        );
    }
    // A generated lambda's NAME mints its owner's raw id; `function_label` has
    // to resolve that away rather than pass it through.
    assert!(
        !rendered.contains("#lambda:"),
        "a generated lambda label must resolve its owner instead of carrying the owner's raw id"
    );
    assert!(
        rendered.contains("executable x0"),
        "the canonical form should still describe the program: {}",
        &rendered[..rendered.len().min(400)]
    );
}

/// fz-kdt.105 — every closure literal the compile interns names a callable the
/// owner labelled.
///
/// Canonical clause order compares closure literals by their stable
/// `Module.name/arity` label, never by the mint-order `FnId` behind them. That
/// only holds if the label table is COMPLETE: an unlabelled callable falls back
/// to raw-id order, which would quietly reintroduce the cross-version movement
/// the label discipline exists to prevent. `World` names each callable as it
/// mints the id, and this is the sweep that says the two mint sites are all of
/// them.
#[test]
fn every_closure_literal_names_a_labelled_callable() {
    for (name, text) in TARGETS {
        let compiler = drive_fixture(name, text);
        let unnamed = compiler.world().types().unnamed_callables();
        assert!(
            unnamed.is_empty(),
            "{name}: closure literals over unlabelled callables {unnamed:?} would order by raw FnId"
        );
    }
}

/// Two compiles of one input in one process publish one canonical form. This
/// is the weakest of the three determinism properties and the one the canonical
/// form OWNS: it holds by construction, with no sort of Debug text behind it.
#[test]
fn two_compiles_of_one_root_produce_one_canonical_form() {
    let (name, text) = TARGETS[1];
    let first = canon_of(name, text);
    let second = canon_of(name, text);
    assert!(
        first == second,
        "two compiles of one root must publish one canonical form; they first differ at byte {:?}",
        first.bytes().zip(second.bytes()).position(|(a, b)| a != b)
    );
}

/// fz-kdt.63's specialization-width watch. Removing the analysis's
/// retract-and-remint churn moved the emitted inventory on 6 of 574 fixtures,
/// in BOTH directions: `enum_take_drop_split` improved (237 -> 214
/// executables; 32 widened activations replaced by 7 precise ones) while
/// `enum_predicate_search` WIDENED (207 -> 221; fourteen extra activations
/// keyed on `int | :false | :ok | :true`). The mechanism: rebasing is the one
/// reset of the return-widening ladder (`define_return`'s `ascents`,
/// semantic.rs), and the churn was exercising it by accident -- fz-kdt.65
/// owns giving the ladder an explicit reset. Until then these pins hold both
/// directions still: a drop is an improvement worth re-pinning with its
/// cause; a rise is the ladder running away.
///
/// WHICH LENS: these numbers come from `drive_root_to_dump_stage` on a freshly
/// submitted root, which is what this test drives. On the tree that set them
/// the three production front doors agree -- `fz2 interp`, `fz2 run` and
/// `fz2 build`, each with `--dump backend=`, all report 59/217/211 and repeat
/// bit-stably -- but agreement between the doors is not a property anything
/// proves, and a report of them diverging is being tracked under fz-kdt.106.
/// So: re-measure through THIS door before re-pinning, and say which door any
/// new number came from.
///
/// Re-pinned DOWNWARD again by fz-kdt.105, which put every DNF axis in
/// canonical clause order at `Types::intern`: `enum_take_drop_split` 211 -> 207,
/// the other two unchanged (their canonical backend dumps are byte-identical).
/// The cause, measured: `drop_while`'s accumulator `{[], :true} | {[int],
/// :false}` was interned TWICE at base -- `Ty(501)` and `Ty(517)`, the same two
/// clauses in the two orders `dnf_union` can produce -- so re-deriving the
/// answer looked like a CHANGE and the return-widening ladder climbed past it to
/// the wider `{[int], :false} | {[int], :true}`. With one id for one carving the
/// answer reproduces, the ladder stops a rung lower, and the four
/// `Enum.drop_while/2#lambda@7205-7420/2` specializations keyed on the wide type
/// lose their only callers to the precise sibling that already existed beside
/// them; the same narrowing turns one `List.reduce_while_cont/3` key into its
/// precise form (1-for-1, no count change). Every one of the eight boundaries
/// that named a wide arm still names an arm -- no destination was dropped, and
/// the fixture corpus is stdout byte-identical. The differently-CARVED twin
/// `{[int], :false | :true}` still interns apart: one denotation, two
/// decompositions, which clause ORDER cannot reconcile (fz-kdt.48).
///
/// Re-pinned DOWNWARD by fz-kdt.104, which stopped offering dispatch
/// alternatives no runtime test could ever route to. Each disappearance is a
/// dropped arm: `enum_predicate_search` 221 -> 217 (four narrow
/// `List.reduce_while_step/3` halt-payload specializations, whose two
/// three-armed dispatches each collapse to the arm that stands in for them);
/// `enum_take_drop_split` 214 -> 211 (one `List.reduce_while_cont/3`, one
/// `List.reduce_while_step/3` and one `Range.reduce_while_step/6`, each the
/// narrow half of a `{:cont, _}` / `{:cont | :halt, _}` pair the runtime reads
/// as the same 2-tuple). `fz_f98_range_map_converges` has no such pair and
/// holds at 59.
///
/// Re-pinned in BOTH directions by fz-kdt.106, which made a correlated-input
/// row set absorb the rows it dominates instead of accumulating one per
/// superseded conclusion. Same door as every number above: this test's own
/// `drive_root_to_dump_stage(root, DumpStage::Backend)`.
///
/// `enum_predicate_search` 217 -> 203: the ladder is gone, so its row set no
/// longer crosses `ACTIVATION_INPUT_ROW_BUDGET`, no longer widens to one
/// column-wise joined row, and the fourteen specializations keyed on the
/// resulting `int | :false | :ok | :true` are never minted. Those fourteen are
/// exactly the FIFO-only surplus fz-kdt.105 isolated, so this number is now
/// what the LIFO schedule already reached: the count no longer depends on the
/// agenda.
///
/// `enum_take_drop_split` 207 -> 215, a RISE, and it is the same cause read
/// from the other side. Thirty budget collapses on this fixture were widening
/// row sets into shared wide keys; without them the callers' correlation
/// survives and the specializations it names stay distinct, so precision
/// REPLACES collapse-driven sharing and the inventory grows. The
/// classification gate (fz-zih) admits a rise exactly when it is paired with a
/// reduction in budget collapses on that fixture; here that pairing is 30 -> 0,
/// asserted by
/// `correlated_input_rows_never_reach_the_widening_budget_on_the_lenses`, and
/// the fixture's stdout is byte-identical through interp, JIT and AOT.
/// `fz_f98_range_map_converges` collapses at neither base nor head and holds
/// at 59.
///
/// Re-pinned UPWARD by fz-kdt.125, which gave the runtime predicate a callable
/// axis: `enum_predicate_search` 203 -> 204. The one arrival is
/// `List.reduce_while_step/3[list(a0_e), {:halt, :false}, a2]`, an arm
/// fz-kdt.118 had dropped as "runtime-indistinguishable and strictly
/// contained". It is not indistinguishable any more -- its sibling is keyed on
/// a different reducer literal, and a closure value's heap word names the
/// lambda it was minted from -- so the pair is two destinations the plan tests
/// for, and the specialization that was dead code becomes reachable. This is
/// fz-kdt.123's resolution, measured: arms BECOME LIVE. Nothing else moved --
/// no key, demand, or transport fact on any lens changed text, and the
/// fixture corpus is stdout byte-identical through interp, JIT and AOT.
///
/// Re-pinned DOWNWARD by fz-kdt.132: `enum_take_drop_split` 215 -> 196. A
/// fold's reducer was clamped onto the specialization it was minted beside, so
/// its accumulator climbed in partial rungs -- `{[], []}`, then
/// `{[], [int]}`, then `{[], [int]} | {[int], []}` -- and stopped one short of
/// the `{[int], [int]}` the fold actually produces. Unclamped, the ladder is
/// one rung: three `split_while`/`split_with` reducer specializations per
/// captured lambda become one, and `split_pair_finish` is keyed on the pair it
/// really receives instead of a union that never named it. Nineteen
/// executables leave; the analysis that finds the one true rung costs 39 more
/// activations, ratcheted in `analysis_claims_survive_a_run_that_could_not_re_derive_them`.
/// The other two lenses hold, and stdout is byte-identical on all three doors.
///
/// Re-pinned UPWARD by fz-kdt.127, which made the forwarder erasure keep
/// capture TYPES and drop only the brand: `enum_predicate_search` 204 -> 206,
/// `enum_take_drop_split` 196 -> 204. Both arrivals are the SAME cause and it
/// is not this fixture's own shape -- a forwarder that takes closures from
/// DIFFERENT lambdas whose capture tuples differ now keys one activation per
/// tuple. In `enum_predicate_search` the `reduce_while/3` chain splits the
/// capture-free `Enum.all?/1`/`any?/1` wrappers from the capture-bearing
/// `all?/2`/`any?/2` ones; in `enum_take_drop_split` the same chain splits
/// capture-free `take_positive`/`drop_positive` from `take_every`/`drop_every`,
/// which close over the step. `enum_take_drop_split` also gains two new
/// dispatch nodes, and they ask real questions -- the accumulator tag
/// `{:cont, _}` vs `{:cont | :halt, _}` and which construction the reducer
/// is -- in the recursive core. Corpus-wide (597 fixtures, 469 backend dumps)
/// the same erasure REMOVES dispatch nodes from five fixtures --
/// `00275_enum_count_member_reduce`, `a_mixed`, `enum_predicate_search`,
/// `repr_seam_enum_count_after_reduce2`, `same_lambda_two_capture_types` --
/// and ADDS ten to four: two here, two to this fixture's `00420_` twin, four
/// to `same_lambda_two_capture_types_dynamic`, and two to
/// `callable_union_capture_containment`, which this same commit rehomes on
/// that dynamic shape so fz-kdt.167's containment law keeps an end-to-end
/// witness (fz-kdt.171). Whether capture arity, rather than
/// capture type, is the right grain for forwarders fed by different lambdas is
/// fz-kdt.169's measurement; stdout is byte-identical on all three doors over
/// 597 fixtures.
#[test]
fn backend_inventory_width_stays_pinned_on_the_target_fixtures() {
    for (name, text, executables) in [
        (
            "fixtures2/behavior/fz_f98_range_map_converges.fz",
            include_str!("../../fixtures2/behavior/fz_f98_range_map_converges.fz"),
            59,
        ),
        (
            "fixtures2/behavior/enum_predicate_search.fz",
            include_str!("../../fixtures2/behavior/enum_predicate_search.fz"),
            206,
        ),
        (
            "fixtures2/behavior/enum_take_drop_split.fz",
            include_str!("../../fixtures2/behavior/enum_take_drop_split.fz"),
            204,
        ),
    ] {
        let (mut compiler, root) = submit(name, text);
        compiler
            .drive_root_to_dump_stage(root, DumpStage::Backend)
            .unwrap_or_else(|error| panic!("{name} should reach a backend program: {error}"));
        let world = compiler.world();
        assert_eq!(
            world.backend_program(root).executables.len(),
            executables,
            "{name}: the emitted executable inventory moved off its fz-kdt.63 pin; \
             re-measure, name the cause, and re-pin"
        );
    }
}

/// The artifact side of the same claim (fz-kdt.91). An executable's
/// `clause_ids` is the reachable-clause SET carried into the artifact; its
/// order is content only because something has to write it down. Ordering it
/// by `body_id` — minted in source order by `entry_source_patterns` and
/// required to ascend with source priority by the dispatch planner — is what
/// keeps the canonical form still when a precision fix repopulates the keys.
/// Try-order is not at stake: both backends select through
/// `ExecutableDispatch::plan()` and use `clause_ids` only as the
/// `body_id`-to-position lookup `clause_index` performs.
#[test]
fn artifact_clause_ids_follow_source_order_on_the_target_fixtures() {
    for (name, text) in [
        TARGETS[0],
        TARGETS[1],
        (
            "fixtures2/behavior/enum_predicate_search.fz",
            include_str!("../../fixtures2/behavior/enum_predicate_search.fz"),
        ),
    ] {
        let (mut compiler, root) = submit(name, text);
        compiler
            .drive_root_to_dump_stage(root, DumpStage::Backend)
            .unwrap_or_else(|error| panic!("{name} should reach a backend program: {error}"));
        let world = compiler.world();
        let program = world.backend_program(root);
        let unordered = program
            .executables
            .iter()
            .filter_map(|executable| {
                let clause_ids = executable.entry_dispatch.as_ref()?.clause_ids();
                let ascends = clause_ids.windows(2).all(|pair| pair[0] < pair[1]);
                (!ascends).then(|| {
                    format!(
                        "{} {clause_ids:?}",
                        function_label(world, executable.key.activation.function)
                    )
                })
            })
            .collect::<Vec<_>>();
        assert!(
            unordered.is_empty(),
            "{name}: {} executable(s) carry clause ids in row-arrival order rather than source \
             order, so any key-population change permutes the artifact: {unordered:?}",
            unordered.len(),
        );
    }
}

/// The executable inventory is NUMBERED by its position in the final-packaging
/// sort, and the canonical dump prints those numbers everywhere — `entry x<N>`,
/// `callee=x<N>`, and the construction wrappers keyed off the same executable
/// symbols. Two specializations of one function differ only in their INPUT
/// TYPES, so the input vector is the tiebreak that decides their indices; keyed
/// on raw `Ty` interner ids that tiebreak is INTERNING order, which the agenda
/// decides.
///
/// Measured on `enum_take_drop_split` (fz-kdt.101): flip `Agenda::pop` to
/// `pop_back` (src/compiler2/agenda.rs:36 — build, dump, revert) and two
/// byte-identical `Enum.reduce/3#lambda@439-517/2` construction wrappers trade
/// indices, `w10` <-> `w11`, because their owning specializations carry the
/// same types under different ids.
///
/// The invariant that removes the freedom: siblings break their tie on
/// fz-kdt.105's canonical, id-free structural comparator (`Types::cmp_tys`), so
/// two entries a reader cannot tell apart still have ONE order, and it is a
/// function of what they say rather than of when they were interned.
#[test]
fn sibling_specializations_are_ordered_by_canonical_inputs_not_interning_order() {
    for (name, text) in [
        TARGETS[0],
        TARGETS[1],
        (
            "fixtures2/behavior/enum_predicate_search.fz",
            include_str!("../../fixtures2/behavior/enum_predicate_search.fz"),
        ),
    ] {
        let (mut compiler, root) = submit(name, text);
        compiler
            .drive_root_to_dump_stage(root, DumpStage::Backend)
            .unwrap_or_else(|error| panic!("{name} should reach a backend program: {error}"));
        let world = compiler.world();
        let types = world.types();
        let program = world.backend_program(root);
        let descents = program
            .executables
            .windows(2)
            .enumerate()
            .filter(|(_, pair)| pair[0].key.activation.function == pair[1].key.activation.function)
            .filter(|(_, pair)| {
                types
                    .cmp_tys(
                        &pair[0].key.activation.inputs(types),
                        &pair[1].key.activation.inputs(types),
                    )
                    .is_gt()
            })
            .map(|(index, pair)| {
                format!(
                    "x{index}/x{} {}",
                    index + 1,
                    function_label(world, pair[0].key.activation.function)
                )
            })
            .collect::<Vec<_>>();
        assert!(
            descents.is_empty(),
            "{name}: {} sibling pair(s) sit in interning order rather than canonical order, so \
             `entry x<N>` numbering follows the schedule: {descents:?}",
            descents.len(),
        );
    }
}

/// The four lenses the fz-kdt.106 review measured schedule confluence on.
const LENSES: [(&str, &str); 4] = [
    (
        "fixtures2/behavior/enum_predicate_search.fz",
        include_str!("../../fixtures2/behavior/enum_predicate_search.fz"),
    ),
    (
        "fixtures2/00420_enum_take_drop_split.fz",
        include_str!("../../fixtures2/00420_enum_take_drop_split.fz"),
    ),
    (
        "fixtures2/00183_enum_take_list_range.fz",
        include_str!("../../fixtures2/00183_enum_take_list_range.fz"),
    ),
    (
        "fixtures2/behavior/fz_f98_range_map_converges.fz",
        include_str!("../../fixtures2/behavior/fz_f98_range_map_converges.fz"),
    ),
];

/// fz-kdt.106: the schedule may not decide what gets specialized.
///
/// `ACTIVATION_INPUT_ROW_BUDGET` is the ONE place where a correlated-input row
/// set stops being a function of what the callers published: past the budget
/// the antichain widens to its column-wise join, and which side of the cliff a
/// row set lands on is a function of how many rungs of ascent history happened
/// to have arrived — which is the agenda's business, not the program's. On
/// `enum_predicate_search` at base that is exactly what happened: FIFO
/// accumulated ten rows (seven of them one caller's ladder) and collapsed to a
/// single wide row, minting fourteen specializations keyed on
/// `int | :false | :ok | :true` that LIFO's lucky eight-row set never mints.
///
/// With the ladders absorbed the budget stops firing on real programs, and a
/// row set that never collapses is a function of its publishers alone. Zero
/// collapses is therefore the schedule-confluence claim, asserted on the
/// production path through the event the compile emits.
///
/// Each lens is driven to its NATIVE program, the door the rest of this gate
/// drives. The earlier BACKEND door reports identically — measured at base,
/// `enum_predicate_search` 28 and `00420_enum_take_drop_split` 30 either way —
/// because the collapses all happen in the analysis both doors share; the
/// choice is a matter of matching the gate, not of coverage. RED at base on
/// two of the four at those counts. The byte-for-byte half is verified by
/// hand, per the fz-kdt.93/.104 precedent: change `Agenda::pop` (src/compiler2/agenda.rs) to
/// `self.queue.pop_back()`, rebuild, and `fz2 interp <fixture> --dump
/// backend=<path>` must produce the same bytes as the FIFO build on all four.
/// `enum_predicate_search` was the exception until fz-kdt.129 -- ONE dispatch
/// whose two distinguishable arms swapped with the schedule that settled them,
/// 28 lines apart -- and it is closed by seating the arm whose surface COVERS
/// its sibling's ahead of it, whichever order the two arrived in
/// (`callsite_dispatch::specificity_order`). Its executable COUNT is
/// schedule-independent too (204 under both), which is what this gate pins.
///
/// `enum_map_family` used to move between the schedules by 1170 backend-canon
/// lines; fz-kdt.108 closes it (0 either way) by giving the callable-flow
/// construction wrapper one canonical `cmp_tys` edge order. TWO corpus
/// fixtures still move and are not this gate's business:
/// `00277_enum_tier0_fixture` (562 lines -- fz-kdt.107's dispatch-twin class
/// plus a `cmp_tys` free-var tie whose fallback to `TypeVarId` mint order is
/// itself schedule-visible, fz-kdt.161) and `dead_closure_capture_empty_list`
/// (2 lines -- fz-kdt.120's return-precision residue). Measured base-vs-head
/// on 2026-09-02: enum_map_family 1170 -> 0, the other two unchanged at
/// 562/2.
///
/// The budget itself STAYS — it is what makes termination a theorem rather
/// than a property of lucky inputs. A collapse after this change would be
/// genuine correlation width, and worth the ticket it would earn.
#[test]
fn correlated_input_rows_never_reach_the_widening_budget_on_the_lenses() {
    for (name, text) in LENSES {
        let telemetry = ConfiguredTelemetry::new();
        let capture = crate::telemetry::Capture::new();
        capture.install(&telemetry, &["fz", "compiler2", "activation_inputs"]);
        let mut compiler = Compiler2::new(telemetry);
        compiler.submit_code(CodeSubmission {
            name: Some(name.to_string()),
            text: text.to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        assert!(
            compiler.demand(super::Job::LowerNativeProgram(root)),
            "{name} should explicitly demand the native program",
        );
        assert!(
            matches!(compiler.drive(), super::DriveOutcome::Resolved),
            "{name} should drive to a settled native program",
        );

        let collapses = capture
            .find(&["fz", "compiler2", "activation_inputs", "budget_collapsed"])
            .iter()
            .map(|event| match event.measurements.get("collapses") {
                Some(crate::telemetry::Value::U64(collapses)) => *collapses,
                other => panic!("{name}: a budget-collapse event must carry a count: {other:?}"),
            })
            .sum::<u64>();
        assert_eq!(
            collapses, 0,
            "{name}: a correlated-input row set widened past its budget, so what the compile \
             specializes is a function of the agenda and not of the program",
        );
    }
}
