//! The permanent ratchet for the canonical external form.
//!
//! `canon(a) == canon(b) && a != b` is exactly "one type, two identities" — the
//! interner canonicalization defect fz-kdt.48 records. This file is that
//! defect's regression guard: it does not fix it, it makes it impossible for a
//! canonical rendering to start lying about it.

use crate::fast_hash::HashMap;
use std::sync::Arc;

use super::super::Compiler2;
use super::super::canon::{canon_backend_program, function_label};
use super::super::drive_harness::Drive;
use super::super::dump::DumpStage;
use super::super::identity::{ExecutableKey, FunctionId};
use super::super::types::{Ty, TyCanon, Types};
use crate::telemetry::ConfiguredTelemetry;

/// The two fixtures the ticket names, by number. Both are driven to their
/// settled world; the canon sweep then reads the WHOLE interned arena, not a
/// hand-picked sample, so a type minted anywhere in the compile is covered.
///
/// `00420_enum_take_drop_split` and `00567_fz_f98_range_map_converges`.
const TARGETS: [u32; 2] = [420, 567];

/// Drives one fixture to its retained `BackendProgram` — the same stage the
/// `--dump backend` path reaches — and renders it.
fn canon_of(number: u32) -> String {
    let settled = Drive::fixture(number).dump_stage(DumpStage::Backend);
    let program = settled.backend_program();
    canon_backend_program(settled.world(), &program)
}

#[test]
fn enum_take_drop_split_reuses_identity_before_the_type_boundary() {
    let settled = Drive::fixture(420).settle();
    let work = settled.world().types().interning_work_stats();
    assert!(
        work.identity_shortcuts > 0,
        "the fixture must exercise identity reuse before the type boundary: {work:?}"
    );
}

fn equivalent(types: &Types, left: Ty, right: Ty) -> bool {
    types.is_subtype(&left, &right) && types.is_subtype(&right, &left)
}

/// Two activations entered the same cycle when neither has an entry, or both
/// name the same function entered at equivalent inputs.
fn equivalent_entries(types: &Types, left: Option<(FunctionId, Ty)>, right: Option<(FunctionId, Ty)>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some((left_function, left_arrow)), Some((right_function, right_arrow))) => {
            let (left_inputs, right_inputs) = (types.arrow_params(&left_arrow), types.arrow_params(&right_arrow));
            left_function == right_function
                && left_inputs.len() == right_inputs.len()
                && left_inputs
                    .iter()
                    .zip(right_inputs)
                    .all(|(left, right)| equivalent(types, *left, *right))
        }
        _ => false,
    }
}

fn equivalent_executable_keys(
    types: &Types,
    program: &super::super::BackendProgram,
) -> Vec<(ExecutableKey, ExecutableKey)> {
    let executables = program
        .executables()
        .iter()
        .map(|executable| (&executable.key, executable.key.activation.inputs(types)))
        .collect::<Vec<_>>();
    let mut duplicates = Vec::new();
    for (index, (left_key, left_inputs)) in executables.iter().enumerate() {
        for (right_key, right_inputs) in &executables[index + 1..] {
            if left_key.activation.root != right_key.activation.root
                || left_key.activation.function != right_key.activation.function
                || left_key.need != right_key.need
                || !equivalent_entries(types, left_key.activation.entry, right_key.activation.entry)
            {
                continue;
            }
            if left_inputs.len() == right_inputs.len()
                && left_inputs
                    .iter()
                    .zip(right_inputs.iter())
                    .all(|(left, right)| equivalent(types, *left, *right))
            {
                duplicates.push(((*left_key).clone(), (*right_key).clone()));
            }
        }
    }
    duplicates
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
    for number in TARGETS {
        let settled = Drive::fixture(number).settle();
        let name = settled.fixture_path().to_string();
        let world = settled.world();
        let types = world.types();
        let labels = |fn_id| function_label(world, FunctionId::from_fn_id(fn_id));
        let mut canon = TyCanon::new(&labels);

        let arena = types.interned_tys();
        let mut groups: HashMap<Arc<str>, Vec<Ty>> = HashMap::default();
        for ty in &arena {
            groups.entry(canon.fingerprint(types, *ty)).or_default().push(*ty);
        }

        let mut collapsed = 0_usize;
        for group in groups.values() {
            let mut classes: HashMap<Arc<str>, Vec<Ty>> = HashMap::default();
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

        // The arena carries distinct ids for one type, so the sweep above
        // proves canon collapses them rather than passing vacuously. Both
        // counts are CEILINGS: a change may lower them and none may raise them
        // without the cause stated beside the pin.
        assert!(
            collapsed <= duplicate_ceiling(number),
            "{name}: {collapsed} mutually-subtype distinct ids, above the {} this fixture is \
             pinned at -- a boundary fold may lower this ceiling, never raise it",
            duplicate_ceiling(number)
        );
    }
}

/// How many ids each target fixture spends on a type it already has. Lower is
/// better, so a change that removes one lowers the pin in the same motion.
///
/// The ids that remain carry something their denotation does not: what a
/// reader takes back out of the type. A closure literal denotes one value, and
/// `func_clause_empty` compares two literals by brand and captures alone, but
/// the literal's arrow surface is read back. It is the closure's own variables
/// where the literal is minted, the key's addressed variables (`a2_p0`) once a
/// key arrow holds it, and a contract's instantiation where a contract met it.
/// Each view is its own id. Interning every literal at its own variables loses
/// the contract instantiations that `callable_value_clauses` and contract
/// application read; letting literal inclusion compare surfaces separates the
/// minted and the addressed views of one value, which then cannot flow between
/// a body and its key (fixture 01143 and the distiller fail on every path). A
/// plain arrow whose result is `any` is every function of its arity, and is kept for the parameters a
/// key reads back (see the axis test
/// `writing_an_arrow_as_the_set_it_denotes_would_erase_the_inputs_a_key_reads_back`).
/// Collapsing nearly every pair across the fixture census changed compile work
/// by 0.09%, so these ids cost identity, not work.
///
/// The number of interned types is deliberately NOT pinned beside it. It is
/// not a lower-only quantity: fusing two clauses that agree on all but one
/// coordinate mints the union of that coordinate, so a fold can spend a type
/// to save an identity. Identities are what a specialization is keyed on;
/// intermediate types are not.
fn duplicate_ceiling(number: u32) -> usize {
    match number {
        // The Enum `*_while`, `*_every` and `*_positive` wrappers have key arrows beside their evidence
        // arrows, and each holds a closure literal whose surface views are separate ids; a view whose
        // accumulator is still a type variable is interned once per call site that names it.
        420 => 197,
        // The widened key type `%{1: atom}` stands beside `%{1: :a}` and holds a closure literal whose
        // surface views are separate ids; a view whose accumulator is still a type variable is
        // interned once per call site that names it.
        567 => 19,
        other => panic!("no pinned ceiling for fixture {other:05}"),
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
        rendered.iter().collect::<crate::fast_hash::HashSet<_>>().len(),
        "canon must render empty, possibly-empty and non-empty lists distinctly: {rendered:?}"
    );
}

/// No interned id may survive into the canonical form. An id is an arena
/// position in one `World`, so a rendering that carries one is not comparable
/// across processes, versions, or a build cache — which is the whole point of
/// having the form at all.
#[test]
fn canon_of_a_backend_program_carries_no_interned_id() {
    let rendered = canon_of(TARGETS[1]);

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
        "SourceOwner(",
        "FnId(",
        "SubjectId(",
        "OutcomeId(",
    ] {
        assert!(
            !rendered.contains(id),
            "the canonical form must not carry the interned id `{id}`"
        );
    }
    assert!(
        !rendered.lines().any(|line| line.trim_start().starts_with("revision ")),
        "the canonical form must not carry synthetic artifact revisions"
    );
    // Generated labels follow typed owner-and-occurrence origin. Their display
    // names are never parsed into identity.
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

#[test]
fn generated_function_labels_follow_typed_origin_not_function_allocation() {
    fn compile_label(unrelated_functions: usize) -> String {
        let mut settled = Drive::fixture(564)
            .before_submit(move |world| {
                for index in 0..unrelated_functions {
                    world.reference_function(super::super::ModuleId::GLOBAL, format!("unrelated_{index}"), 0);
                }
            })
            .settle();
        let root = settled.root();
        assert_eq!(settled.compiler_mut().run_root_interp(root), Ok(42));

        let main = settled.compiler().root_function(root);
        let super::super::LoweredBody::Clauses { generated, .. } = &*settled.world().lowered_body(main);

        let generated = generated.first().copied().expect("source lambda identity");
        let super::super::identity::FunctionOrigin::Generated { owner, occurrence } =
            &settled.world().function_ref(generated).origin
        else {
            panic!("generated function typed origin");
        };
        assert!(std::sync::Arc::ptr_eq(
            owner,
            &settled.world().function_ref(main).denotation
        ));
        let expected = format!(
            "{}#lambda@{}/1",
            function_label(settled.world(), main),
            occurrence.as_u32()
        );
        let label = function_label(settled.world(), generated);
        assert_eq!(label, expected);
        label
    }

    assert_eq!(compile_label(0), compile_label(7));
}

#[test]
fn same_range_generated_peers_order_independently_of_function_allocation() {
    fn compile(unrelated_functions: usize) -> String {
        let settled = Drive::fixture(565)
            .before_submit(move |world| {
                for index in 0..unrelated_functions {
                    world.reference_function(super::super::ModuleId::GLOBAL, format!("unrelated_{index}"), 0);
                }
            })
            .dump_stage(DumpStage::Backend);
        let program = settled.backend_program();
        canon_backend_program(settled.world(), &program)
    }

    let baseline = compile(0);
    assert!(baseline.contains("#lambda@1/0"), "peer identity must survive rendering");
    assert_eq!(baseline, compile(7));
}

/// Every closure literal has a typed origin shared by the function interner.
/// The ACTIVATION order demands one — `ClauseOrder::cmp_callable` expects it
/// outright, and asserts two distinct callables have distinct origins — so a
/// missing registration is a panic on an activation surface, not a quiet
/// fallback. World registers at both mint sites, before any literal can name
/// one. (Storage order reads no origin at all; that is what lets the interner
/// answer from its index.)
#[test]
fn every_closure_literal_has_a_registered_origin() {
    for number in TARGETS {
        let settled = Drive::fixture(number).settle();
        let unregistered = settled.world().types().unregistered_callables();
        assert!(
            unregistered.is_empty(),
            "{}: closure literals over unregistered callables {unregistered:?} have no activation order",
            settled.fixture_path()
        );
    }
}

/// Two compiles of one input in one process publish one canonical form. This
/// is the weakest of the three determinism properties and the one the canonical
/// form OWNS: it holds by construction, with no sort of Debug text behind it.
#[test]
fn two_compiles_of_one_root_produce_one_canonical_form() {
    let number = TARGETS[1];
    let first = canon_of(number);
    let second = canon_of(number);
    assert!(
        first == second,
        "two compiles of one root must publish one canonical form; they first differ at byte {:?}",
        first.bytes().zip(second.bytes()).position(|(a, b)| a != b)
    );
}

/// The specialization-width watch: the emitted executable inventory of each target
/// fixture. A drop is an improvement worth re-pinning with its cause; a rise is the
/// return-widening ladder running away, or precision replacing collapse-driven sharing
/// where the classification gate admits it.
///
/// WHICH LENS: these numbers come from `drive_root_to_dump_stage` on a freshly
/// submitted root, which is what this test drives. The three production front doors
/// (`fz2 interp`, `fz2 run` and `fz2 build`, each with `--dump backend=`) are
/// expected to agree, but agreement between the doors is not a property anything
/// proves. So: re-measure through THIS door before re-pinning, and say which door any
/// new number came from.
///
/// Kernel's arithmetic externs declare their failure with `raises:`, so an
/// operator's wrapper executable raises for itself and no result-decoding
/// executable stands beside it. `arithmetic_error/0` remains an ordinary
/// generic fz call.
#[test]
fn backend_inventory_width_stays_pinned_on_the_target_fixtures() {
    for (number, executables) in [
        (
            568, // enum_count_member_reduce
            39,
        ),
        (
            567, // fz_f98_range_map_converges
            55,
        ),
        (
            569, // enum_map_family
            110,
        ),
        (
            562, // mailbox_closure_each
            44,
        ),
        (
            563, // mailbox_closure_reduce
            53,
        ),
        (
            570, // actor_ring
            // The ring's `got == 5` compares a mailbox value, so all three
            // reachable `==` clauses emit: `fz_op_eq_ii`, `fz_op_eq_fi` and
            // the `any`/`any` `fz_op_eq`.
            72,
        ),
        (
            571, // enum_predicate_search
            // Exact caller rows retain four specializations hidden by blended evidence.
            190,
        ),
        (
            420, // enum_take_drop_split, over both a list and a range
            188,
        ),
    ] {
        let settled = Drive::fixture(number).dump_stage(DumpStage::Backend);
        let program = settled.backend_program();
        assert_eq!(
            program.executables().len(),
            executables,
            "{}: the emitted executable inventory moved off its target-fixture pin; \
             re-measure, name the cause, and re-pin",
            settled.fixture_path()
        );
        let duplicates = equivalent_executable_keys(settled.world().types(), &program);
        assert!(
            duplicates.is_empty(),
            "{}: equivalent activation inputs minted {} duplicate executable keys: {duplicates:?}",
            settled.fixture_path(),
            duplicates.len(),
        );
    }
}

/// The artifact side of the same claim (fz-kdt.91). An executable's
/// The retained outcome-to-clause target table derives the source-body SET for
/// presentation. Its order is content only because something has to write it
/// down. Ordering it by `body_id` — minted in source order by
/// `entry_source_patterns` and required to ascend with source priority by the
/// dispatch planner — keeps the canonical form still when a precision fix
/// repopulates target slots. Try-order is not at stake: both backends select
/// through `ExecutableDispatch::plan()` and route through `OutcomeId` slots.
#[test]
fn artifact_clause_ids_follow_source_order_on_the_target_fixtures() {
    for number in [TARGETS[0], TARGETS[1], 571] {
        let settled = Drive::fixture(number).dump_stage(DumpStage::Backend);
        let world = settled.world();
        let program = settled.backend_program();
        let unordered = program
            .executables()
            .iter()
            .filter_map(|executable| {
                let clause_ids = executable
                    .abi
                    .materialized
                    .entry_dispatch
                    .as_ref()?
                    .clause_ids()
                    .collect::<Vec<_>>();
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
            "{}: {} executable(s) carry clause ids in row-arrival order rather than source \
             order, so any key-population change permutes the artifact: {unordered:?}",
            settled.fixture_path(),
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
/// `pop_back` (crates/fz-engine/src/agenda.rs:36 — build, dump, revert) and two
/// byte-identical `Enum.reduce/3#lambda@439-517/2` construction wrappers trade
/// indices, `w10` <-> `w11`, because their owning specializations carry the
/// same types under different ids.
///
/// The invariant that removes the freedom: siblings break their tie on
/// the canonical typed activation comparator (`Types::cmp_activation_tys`), so
/// two entries a reader cannot tell apart still have ONE order, and it is a
/// function of what they say rather than of when they were interned.
#[test]
fn sibling_specializations_are_ordered_by_canonical_inputs_not_interning_order() {
    for number in [TARGETS[0], TARGETS[1], 571] {
        let settled = Drive::fixture(number).dump_stage(DumpStage::Backend);
        let world = settled.world();
        let types = world.types();
        let program = settled.backend_program();
        let descents = program
            .executables()
            .iter()
            .collect::<Vec<_>>()
            .windows(2)
            .enumerate()
            .filter(|(_, pair)| pair[0].key.activation.function == pair[1].key.activation.function)
            .filter(|(_, pair)| {
                types
                    .cmp_activation_tys(
                        pair[0].key.activation.inputs(types),
                        pair[1].key.activation.inputs(types),
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
            "{}: {} sibling pair(s) sit in interning order rather than canonical order, so \
             `entry x<N>` numbering follows the schedule: {descents:?}",
            settled.fixture_path(),
            descents.len(),
        );
    }
}

/// The four lenses the fz-kdt.106 review measured schedule confluence on:
/// `00571_enum_predicate_search`, `00420_enum_take_drop_split`,
/// `00183_enum_take_list_range` and `00567_fz_f98_range_map_converges`.
const LENSES: [u32; 4] = [571, 420, 183, 567];

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
/// hand, per the fz-kdt.93/.104 precedent: change `Agenda::pop` (crates/fz-engine/src/agenda.rs) to
/// `self.queue.pop_back()`, rebuild, and `fz2 interp <fixture> --dump
/// backend=<path>` must produce the same bytes as the FIFO build on all four.
/// `enum_predicate_search` was the exception until fz-kdt.129 -- ONE dispatch
/// whose two distinguishable arms swapped with the schedule that settled them,
/// 28 lines apart -- and it is closed by seating the arm whose surface COVERS
/// its sibling's ahead of it, whichever order the two arrived in
/// (`callsite_dispatch::specificity_order`). Its executable COUNT is
/// schedule-independent too (204 under both), which is what this gate pins.
///
/// `enum_map_family` is schedule-stable: the callable-flow construction wrapper has one
/// canonical typed activation edge order. TWO corpus fixtures still move and are not this
/// gate's business:
/// `00277_enum_tier0_fixture` (fz-kdt.107's dispatch-twin class plus a structural free-var
/// tie whose fallback to `TypeVarId` mint order is itself schedule-visible, fz-kdt.161) and
/// `dead_closure_capture_empty_list` (fz-kdt.120's return-precision residue).
///
/// The budget itself STAYS — it is what makes termination a theorem rather
/// than a property of lucky inputs. A collapse after this change would be
/// genuine correlation width, and worth the ticket it would earn.
#[test]
fn correlated_input_rows_never_reach_the_widening_budget_on_the_lenses() {
    for number in LENSES {
        let drive = Drive::fixture(number);
        let capture = crate::telemetry::Capture::new();
        capture.install(drive.telemetry(), &["fz", "compiler2", "activation_inputs"]);
        let settled = drive.dump_stage(DumpStage::Native);
        let name = settled.fixture_path().to_string();

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

#[cfg(test)]
mod carrier_canon_tests {
    use super::super::*;

    fn render_root_carrier_with_dummy_lanes(dummy_lanes: usize) -> String {
        let mut world = World::new();
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        for _ in 0..dummy_lanes {
            world.intern_lane(crate::compiler2::transport::LaneDescr {
                ty: atom,
                class: crate::compiler2::transport::TransportClass::Value,
            });
        }
        let carrier = world.intern_lane(crate::compiler2::transport::LaneDescr {
            ty: int,
            class: crate::compiler2::transport::TransportClass::Value,
        });
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let layout = BackendValueLayout {
            structural: nothing,
            carrier: TransportCarrier::ValueRef(carrier),
            tys: Box::new([int]),
            reprs: Box::new([AbiValueRepr::ValueRef]),
        };
        let labels = |fn_id| function_label(&world, FunctionId::from_fn_id(fn_id));
        ProgramCanon::new(&world, TyCanon::new(&labels)).layout(&layout)
    }

    #[test]
    fn root_carrier_canon_uses_the_lane_type_not_its_mint_order() {
        assert_eq!(
            render_root_carrier_with_dummy_lanes(0),
            render_root_carrier_with_dummy_lanes(1)
        );
    }
}
