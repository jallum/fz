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
            221,
        ),
        (
            "fixtures2/behavior/enum_take_drop_split.fz",
            include_str!("../../fixtures2/behavior/enum_take_drop_split.fz"),
            214,
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
