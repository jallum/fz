//! Canonical compiler2 facts for fixtures2 compiler contracts.
//!
//! These facts are derived from compiler2's settled semantic closure rather
//! than old-world dump text. Stable fixture-facing identity comes from
//! source provenance: callsite spans and owner-relative lambda provenance.

use std::collections::HashMap;

use crate::compiler::source::Span;
use crate::fz_ir::FnId;

use super::body::{CallSiteId, LoweredBody, LoweredTail};
use super::identity::{ActivationKey, FunctionId, RootId};
use super::semantic::{CallSiteSummary, SelectedCallee};
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

pub(crate) fn canonical_call_edge_facts(world: &World<'_>, root: RootId) -> Vec<CanonicalCallEdgeFact> {
    let closure = world.semantic_closure(root);
    let mut labels = HashMap::new();
    let mut activations = closure.activations.into_iter().collect::<Vec<_>>();
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
                input_types: target.input_types.iter().map(|ty| world.types().display(ty)).collect(),
                return_ty: target
                    .return_ty
                    .map(|ty| world.types().display(&ty))
                    .unwrap_or_else(|| "none".to_string()),
            })
            .collect(),
        return_ty: summary
            .return_ty
            .map(|ty| world.types().display(&ty))
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
        activation.input.iter().map(|ty| world.types().display(ty)).collect(),
    )
}

fn activation_label(world: &World<'_>, activation: &ActivationKey, labels: &mut HashMap<FunctionId, String>) -> String {
    format!(
        "{}[{}]",
        canonical_function_label(world, activation.function, labels),
        activation
            .input
            .iter()
            .map(|ty| world.types().display(ty))
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
