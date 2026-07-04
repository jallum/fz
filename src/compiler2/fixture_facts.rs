//! Canonical compiler2 facts for fixtures2 compiler contracts.
//!
//! These facts are derived over a caller-supplied activation inventory (the
//! set of activations a root reaches) rather than old-world dump text. Callers
//! source that inventory from the product path — e.g.
//! `Compiler2::product_activation_inventory` — so runtime-demand/callable-flow
//! reached executables (escaped lambdas) are included. Stable fixture-facing
//! identity comes from source provenance: callsite spans and owner-relative
//! lambda provenance.

use std::collections::HashMap;

use crate::fz_ir::FnId;
use crate::source::Span;

use super::body::{CallSiteId, LoweredBody, LoweredTail};
use super::identity::{ActivationKey, FunctionId, RootId};
use super::semantic::{CallSiteSummary, SelectedCallee};
use super::types::{ClosureSurfacePos, TypeVarId, decode_closure_surface_var};
use super::world::World;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalCallEdgeFact {
    pub caller: String,
    pub callsite: String,
    pub dispatch: String,
    pub targets: Vec<CanonicalCallTargetFact>,
    pub return_ty: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalCallTargetFact {
    pub target: String,
    pub input_types: Vec<String>,
    pub return_ty: String,
}

pub(crate) fn canonical_call_edge_facts(
    world: &World<'_>,
    root: RootId,
    inventory: &[ActivationKey],
) -> Vec<CanonicalCallEdgeFact> {
    let root_code = world.function_definition(world.root_function(root)).0.code;
    let mut labels = HashMap::new();
    let mut activations = inventory.to_vec();
    activations.sort_by_key(|activation| (activation.root.as_u32(), activation.function.as_u32(), activation.arrow));
    activations.dedup();
    activations.retain(|activation| world.function_definition(activation.function).0.code == root_code);
    activations.sort_by_cached_key(|activation| activation_sort_key(world, activation, &mut labels));

    let mut facts = Vec::new();
    for activation in activations {
        let Some(analysis) = world.activation_analysis(&activation) else {
            continue;
        };
        let callsite_kinds = callsite_kinds(&world.lowered_body(activation.function));
        let mut callsites = analysis.callsites.clone();
        callsites.sort_by_key(|callsite| (callsite.span().start, callsite.span().end, callsite.as_u32()));
        for callsite in callsites {
            let key = super::semantic::CallSiteKey {
                activation: activation.clone(),
                callsite,
            };
            let Some(summary) = world.callsite_summary(&key) else {
                continue;
            };
            facts.push(canonical_call_edge_fact(
                world,
                &activation,
                callsite,
                summary,
                callsite_kinds
                    .get(&callsite)
                    .copied()
                    .unwrap_or(CallsiteDispatchKind::Direct),
                &mut labels,
            ));
        }
    }
    facts
}

pub(crate) fn render_canonical_call_edge_snapshot(facts: &[CanonicalCallEdgeFact]) -> String {
    if facts.is_empty() {
        return "(no canonical call edges)\n".to_string();
    }
    let mut out = String::new();
    for fact in facts {
        out.push_str(&format!(
            "{} | {} | {} | {} => {}\n",
            fact.caller,
            fact.callsite,
            fact.dispatch,
            render_target_list(&fact.targets),
            fact.return_ty
        ));
    }
    out
}

fn canonical_call_edge_fact(
    world: &World<'_>,
    activation: &ActivationKey,
    callsite: super::body::CallSiteId,
    summary: &CallSiteSummary,
    dispatch_kind: CallsiteDispatchKind,
    labels: &mut HashMap<FunctionId, String>,
) -> CanonicalCallEdgeFact {
    let dispatch = dispatch_kind.as_str(summary);
    CanonicalCallEdgeFact {
        caller: activation_label(world, activation, labels),
        callsite: span_label(callsite.span()),
        dispatch,
        targets: summary
            .targets
            .iter()
            .map(|target| CanonicalCallTargetFact {
                target: target_label(world, target.callee.clone(), labels),
                input_types: target
                    .surface_inputs
                    .iter()
                    .map(|ty| stable_type_text(world, world.types().display(ty)))
                    .collect(),
                return_ty: target
                    .return_ty
                    .map(|ty| stable_type_text(world, world.types().display(&ty)))
                    .unwrap_or_else(|| "none".to_string()),
            })
            .collect(),
        return_ty: summary
            .return_ty
            .map(|ty| stable_type_text(world, world.types().display(&ty)))
            .unwrap_or_else(|| "none".to_string()),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CallsiteDispatchKind {
    Direct,
    Closure,
}

impl CallsiteDispatchKind {
    fn as_str(self, summary: &CallSiteSummary) -> String {
        match self {
            Self::Closure => "closure".to_string(),
            Self::Direct if summary.targets.len() > 1 => "direct-multi".to_string(),
            Self::Direct
                if summary
                    .targets
                    .iter()
                    .any(|target| matches!(target.callee, SelectedCallee::ProviderBoundary(_))) =>
            {
                "provider".to_string()
            }
            Self::Direct => "direct".to_string(),
        }
    }
}

fn callsite_kinds(body: &LoweredBody) -> HashMap<CallSiteId, CallsiteDispatchKind> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return out;
    };
    for entry in entries {
        match entry.tail {
            LoweredTail::DirectCall { callsite, .. } => {
                out.insert(callsite, CallsiteDispatchKind::Direct);
            }
            LoweredTail::ClosureCall { callsite, .. } => {
                out.insert(callsite, CallsiteDispatchKind::Closure);
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
        }
    }
    out
}

fn activation_sort_key(
    world: &World<'_>,
    activation: &ActivationKey,
    labels: &mut HashMap<FunctionId, String>,
) -> (String, Vec<String>) {
    (
        canonical_function_label(world, activation.function, labels),
        activation
            .inputs(world.types())
            .iter()
            .map(|ty| world.types().display(ty))
            .collect(),
    )
}

fn activation_label(world: &World<'_>, activation: &ActivationKey, labels: &mut HashMap<FunctionId, String>) -> String {
    format!(
        "{}[{}]",
        canonical_function_label(world, activation.function, labels),
        activation
            .inputs(world.types())
            .iter()
            .map(|ty| stable_type_text(world, world.types().display(ty)))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn target_label(world: &World<'_>, callee: SelectedCallee, labels: &mut HashMap<FunctionId, String>) -> String {
    match callee {
        SelectedCallee::Function(function) => canonical_function_label(world, function, labels),
        SelectedCallee::ProviderBoundary(function) => {
            format!("provider:{}", canonical_function_label(world, function, labels))
        }
    }
}

fn canonical_function_label(
    world: &World<'_>,
    function: FunctionId,
    labels: &mut HashMap<FunctionId, String>,
) -> String {
    if let Some(label) = labels.get(&function) {
        return label.clone();
    }
    let function_ref = world.function_ref(function);
    let label = match parse_generated_lambda(function_ref.name.as_str()) {
        Some(generated) => {
            let owner = FunctionId::from_fn_id(FnId(generated.owner));
            let owner_label = canonical_function_label(world, owner, labels);
            format!(
                "{owner_label}::lambda[{}]/{}",
                provenance_span_label(generated.start, generated.end),
                function_ref.arity
            )
        }
        None => {
            let base = match world.module_name(function_ref.module) {
                Some(module) if !module.is_empty() => format!("{module}.{}", function_ref.name),
                _ => function_ref.name.clone(),
            };
            format!("{base}/{}", function_ref.arity)
        }
    };
    labels.insert(function, label.clone());
    label
}

fn render_target_list(targets: &[CanonicalCallTargetFact]) -> String {
    targets
        .iter()
        .map(|target| {
            format!(
                "{}({}) => {}",
                target.target,
                target.input_types.join(", "),
                target.return_ty
            )
        })
        .collect::<Vec<_>>()
        .join(" || ")
}

fn span_label(span: Span) -> String {
    if span.is_dummy() {
        "<generated>".to_string()
    } else {
        format!("@{}-{}", span.start, span.end)
    }
}

struct GeneratedLambda {
    owner: u32,
    start: u32,
    end: u32,
}

fn parse_generated_lambda(name: &str) -> Option<GeneratedLambda> {
    let rest = name.strip_prefix("#lambda:")?;
    let (owner, rest) = rest.split_once(':')?;
    let (start, end) = rest.split_once('-')?;
    Some(GeneratedLambda {
        owner: owner.parse().ok()?,
        start: start.parse().ok()?,
        end: end.parse().ok()?,
    })
}

fn provenance_span_label(start: u32, end: u32) -> String {
    format!("@{}-{}", start, end)
}

/// Consume a `closure[...]` capture tag (balanced on `[`/`]`, since a
/// captured type can itself be a list and so nest further `[`/`]` pairs),
/// if one starts at the iterator's current position. A no-op (the iterator
/// is left untouched) if the tag isn't present.
fn drop_closure_capture_tag(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    const TAG: &str = "closure[";
    let mut probe = chars.clone();
    if !TAG.chars().all(|expected| probe.next() == Some(expected)) {
        return;
    }
    let mut depth = 1_u32;
    for ch in probe.by_ref() {
        match ch {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
    }
    *chars = probe;
}

fn stable_type_text(world: &World<'_>, rendered: String) -> String {
    let mut out = String::with_capacity(rendered.len());
    let mut chars = rendered.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '#' && chars.peek().is_some_and(|next| next.is_ascii_digit()) {
            // Drop the volatile interned-id / closure-literal suffix (`…#14`,
            // or `…#14closure[captures]` when the literal is an env-carrying
            // closure — see `format_closure_lit_suffix` in
            // `compiler2::types::format`). Call-edge snapshots key on source
            // provenance (callsite spans, owner-relative lambda labels), not
            // on closure-literal identity, so the whole suffix is noise here.
            while chars.peek().is_some_and(|next| next.is_ascii_digit()) {
                let _ = chars.next();
            }
            drop_closure_capture_tag(&mut chars);
            continue;
        }
        if ch == 'α' && chars.peek().is_some_and(|next| next.is_ascii_digit()) {
            // Project a free var id onto its stable owner-relative label.
            let mut var_id = 0_u32;
            while let Some(digit) = chars.peek().and_then(|next| next.to_digit(10)) {
                var_id = var_id.saturating_mul(10).saturating_add(digit);
                let _ = chars.next();
            }
            out.push_str(&stable_var_label(world, var_id));
            continue;
        }
        out.push(ch);
    }
    out
}

/// Decode a bare free type-variable id (the `N` in a rendered `αN`) into a
/// STABLE, definition-order-independent label.
///
/// A closure-surface var packs `N = fn_id * 64 + position` (`closure_var_id`),
/// and `fn_id` is a registration-order counter — so the raw `αN` drifts
/// whenever an unrelated function is defined ahead of the owning lambda. This
/// projects the id back onto the owner's stable source provenance (the same
/// owner-relative coordinate the call-edge labels already use): `α4352` renders
/// as `main::lambda[@5-20]/1:a0`, and `:r` for the dedicated return slot, so a
/// snapshot survives id churn.
///
/// A free var whose decoded owner/position does not resolve to a real function
/// slot with a matching arity is not a closure-surface var we can attribute, so
/// it keeps the bare `αN`. (A future keying change that tags closure-surface
/// vars distinctly — as structural addresses already are — would remove that
/// residual ambiguity; this decoder is the seam such a change would refine.)
fn stable_var_label(world: &World<'_>, var_id: u32) -> String {
    let bare = || format!("α{var_id}");
    let Some((fn_id, position)) = decode_closure_surface_var(TypeVarId(var_id)) else {
        return bare();
    };
    let function = FunctionId::from_fn_id(fn_id);
    let Some(function_ref) = world.try_function_ref(function) else {
        return bare();
    };
    let arity = function_ref.arity;
    let slot = match position {
        ClosureSurfacePos::Ret => "r".to_string(),
        ClosureSurfacePos::Arg(pos) if (pos as usize) < arity => format!("a{pos}"),
        ClosureSurfacePos::Arg(_) => return bare(),
    };
    let label = canonical_function_label(world, function, &mut HashMap::new());
    format!("{label}:{slot}")
}

#[cfg(test)]
mod capture_tag_tests {
    use super::{World, drop_closure_capture_tag, stable_type_text};
    use crate::telemetry::ConfiguredTelemetry;

    /// Runs `drop_closure_capture_tag` over `input` and returns what's left
    /// in the iterator afterward, so tests can assert on the untouched tail
    /// (empty when the whole rest of the input was consumed).
    fn strip(input: &str) -> String {
        let mut chars = input.chars().peekable();
        drop_closure_capture_tag(&mut chars);
        chars.collect()
    }

    #[test]
    fn leaves_non_tag_text_untouched() {
        assert_eq!(strip("int"), "int");
    }

    #[test]
    fn leaves_partial_prefix_match_untouched() {
        // `closureXYZ[...]` shares a prefix with the tag but isn't it: the
        // exact literal `closure[` must match, not just `closure`.
        assert_eq!(strip("closureXYZ[atom]"), "closureXYZ[atom]");
    }

    #[test]
    fn strips_a_flat_capture() {
        assert_eq!(strip("closure[int] rest"), " rest");
    }

    #[test]
    fn balances_nested_capture_brackets() {
        // A captured type can itself be a list (e.g. `closure[[int], atom]`),
        // nesting further `[`/`]` pairs inside the tag. A naive "stop at the
        // first `]`" strip would truncate at `closure[[int]` and leave
        // `, atom] rest` dangling.
        let input = "closure[[int], atom] rest";
        assert_eq!(strip(input), " rest");

        // Pin the bite: show what the naive (non-balanced) strip would have
        // produced, and confirm it differs from the correct result above.
        let naive_tag_end = input.find(']').expect("input has a `]`");
        let naive_remainder = &input[naive_tag_end + 1..];
        assert_eq!(naive_remainder, ", atom] rest");
        assert_ne!(naive_remainder, strip(input));
    }

    #[test]
    fn leaves_an_adjacent_unrelated_list_untouched() {
        assert_eq!(strip("closure[int] [str]"), " [str]");
    }

    #[test]
    fn on_unbalanced_input_consumes_to_end_of_string() {
        // `format_closure_lit_suffix` (compiler2::types::format) always emits
        // balanced brackets, so unbalanced input is unreachable from a real
        // render today. This pins the current behavior — consume to
        // end-of-string rather than backing off — rather than leaving it as
        // an untested surprise, so a future refactor changes it on purpose
        // or not at all.
        assert_eq!(strip("closure[int, [int]"), "");
    }

    #[test]
    fn stable_type_text_strips_the_capture_tag_call_edges_carry() {
        // Mirrors the real shape a call-edge snapshot renders: a volatile
        // `#<id>` suffix immediately followed by the closure literal's
        // capture tag, both of which `stable_type_text` treats as noise.
        let tel = ConfiguredTelemetry::new();
        let world = World::new(&tel);
        let rendered = "(a0_p0) -> a0_r#14closure[int, atom] => int".to_string();
        assert_eq!(stable_type_text(&world, rendered), "(a0_p0) -> a0_r => int");
    }
}
