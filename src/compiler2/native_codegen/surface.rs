//! Planner-free input surface for compiler2-owned native codegen.
//!
//! The old native driver starts from planner-owned artifacts, but compiler2's
//! in-house backend only needs a narrower set of codegen facts: the prepared
//! fz-IR bodies, their per-body typing/dispatch facts, ABI lanes,
//! callable-boundary inventory, and a few module-wide metadata tables.
//! `NativeCodegenSurface` owns that handoff so planner-owned wrappers stay
//! outside compiler2 native codegen.

use super::{ArgRepr, CodegenError, MidFlightArgShape};
use crate::compiler2::NativeBody;
use crate::compiler2::artifact::NativeCallableBoundaryId;
use crate::diag::Diagnostics;
use crate::fz_ir::{FnId, FnIr, Module};
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeCallableBoundarySurface {
    pub boundary_id: NativeCallableBoundaryId,
    pub identity_fn: FnId,
    pub target_fn: FnId,
    pub capture_count: usize,
    pub capture_key: Vec<crate::types::KeySlot<crate::compiler2::Ty>>,
    pub capture_reprs: Vec<ArgRepr>,
    pub arg_reprs: Vec<ArgRepr>,
    pub return_diverges: bool,
    pub return_reprs: Vec<ArgRepr>,
    pub return_tuple_arity: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeClosureTargetSurface {
    pub capture_count: usize,
    pub capture_reprs: Vec<ArgRepr>,
    pub arg_reprs: Vec<ArgRepr>,
}

impl NativeClosureTargetSurface {
    /// Captures then args, in target-body compiled-param order -- the flat
    /// physical ABI this surface asserts for its `target_fn`.
    pub(crate) fn flattened_param_reprs(&self) -> Vec<ArgRepr> {
        self.capture_reprs
            .iter()
            .chain(self.arg_reprs.iter())
            .copied()
            .collect()
    }
}

/// Surface-vs-body ABI agreement, enforced exactly where code shaped from
/// the BODY's compiled `param_reprs` meets code shaped from the SURFACE:
/// the closure-lit direct-call path (`resolve_direct_closure_surface` in
/// terminator.rs, guarding `push_direct_closure_args` and the direct
/// `call`/`return_call` against the target's declared signature). That is
/// the only seam where the two worlds must be lane-for-lane identical.
///
/// It is deliberately NOT a registry-wide or packaging-time rule. A
/// published surface may be a strict superset of the body's params and
/// still be sound, because for a closure target the surface itself defines
/// the whole entry world self-consistently: `build_fn_sigs` declares the
/// entry signature from `surface.arg_reprs`, `harness_closure_target`
/// partitions entry params by the same surface, and indirect callers
/// marshal through the runtime env -- extra published lanes are passed and
/// ignored. Live proof: `resource_index_payload_private` runs green with a
/// boundary publishing one arg lane for a zero-param body; a registry-wide
/// body-agreement check reds it. Producer-consistency (two producers
/// binding one target must agree on the full surface, capture/arg split
/// included) is the registry's own invariant, enforced at
/// `register_closure_target_surface` in driver.rs.
pub(crate) fn require_closure_target_surface_agreement(
    target_fn: FnId,
    context: &str,
    published: &NativeClosureTargetSurface,
    compiled: &[ArgRepr],
) -> Result<(), CodegenError> {
    let published_flat = published.flattened_param_reprs();
    if published_flat == compiled {
        return Ok(());
    }
    Err(CodegenError::new(
        crate::compiler2::artifact::incompatible_physical_abi_message(
            format_args!("closure target fn {}", target_fn.0),
            context,
            format_args!(
                "published surface (capture_reprs={:?}, arg_reprs={:?}, {} lane(s) total)",
                published.capture_reprs,
                published.arg_reprs,
                published_flat.len(),
            ),
            format_args!(
                "the target's compiled ABI ({:?}, {} lane(s) total)",
                compiled,
                compiled.len()
            ),
        ),
    ))
}

/// Direct-dispatch consumption also requires the call's argument count to
/// agree with the target's declared argument-LANE count. `target.arg_reprs`
/// is the target's own compiled per-LANE ABI: a semantic argument whose
/// transport shape spans more than one physical lane (e.g. a 2-lane
/// accumulator) advances `arg_reprs` by more than one entry for that one
/// logical argument. The call's own `args`, by contrast, is per-SEMANTIC-
/// argument: each logical call argument has already been collapsed to one
/// materialized value (boxed generically, if needed, for the closure's
/// indirect calling convention) before it reaches this consumption point.
/// There is no lossless way to re-expand one already-materialized value
/// back into its target's several constituent lanes here -- doing so would
/// require per-argument lane-width bookkeeping this surface does not carry
/// and a runtime decode of an opaque boxed value that does not exist. So,
/// exactly like `require_closure_target_surface_agreement`, a length
/// disagreement here must fail cleanly rather than silently under-fill the
/// physical call (previously: a raw cranelift verifier "argument count"
/// panic, or worse, an in-bounds but wrong-repr coercion when the counts
/// happened to coincide).
pub(crate) fn require_direct_closure_call_arity_agreement(
    target_fn: FnId,
    context: &str,
    call_arg_count: usize,
    target: &NativeClosureTargetSurface,
) -> Result<(), CodegenError> {
    if call_arg_count == target.arg_reprs.len() {
        return Ok(());
    }
    Err(CodegenError::new(
        crate::compiler2::artifact::incompatible_physical_abi_message(
            format_args!("closure target fn {}", target_fn.0),
            context,
            format_args!("a call site supplying {call_arg_count} semantic argument(s)"),
            format_args!(
                "the target's published argument lanes ({:?}, {} lane(s) total)",
                target.arg_reprs,
                target.arg_reprs.len()
            ),
        ),
    ))
}

pub(crate) struct NativeCodegenSurface<'a> {
    pub module: &'a Module,
    pub diagnostics: Diagnostics,
    pub main_fn_id: Option<FnId>,
    /// Number of populated body slots, fixed at construction so telemetry
    /// reads stored state instead of re-counting at emit points.
    pub spec_count: usize,
    pub body_slots: Vec<Option<NativeCodegenBody<'a>>>,
    pub callable_boundaries: BTreeMap<u32, NativeCallableBoundarySurface>,
    pub closure_targets: HashMap<FnId, NativeClosureTargetSurface>,
    pub mid_flight_cont_keys: Vec<(u32, Vec<MidFlightArgShape>)>,
    pub param_reprs: Vec<Vec<ArgRepr>>,
    pub halt_reprs: Vec<ArgRepr>,
    pub return_diverges: Vec<bool>,
    pub native_abi_fns: HashSet<FnId>,
    pub cont_target_fns: HashSet<FnId>,
    pub cont_fns: HashSet<FnId>,
    pub fn_halt_kinds: HashMap<u32, u32>,
}

pub(crate) struct NativeCodegenBody<'a> {
    pub codegen_id: u32,
    pub fn_idx: usize,
    pub fn_id: FnId,
    pub native_body: &'a NativeBody,
    pub body: &'a FnIr,
    pub display_name: String,
}

impl<'a> NativeCodegenSurface<'a> {
    pub(crate) fn body(&self, codegen_id: u32) -> &NativeCodegenBody<'a> {
        self.body_slots
            .get(codegen_id as usize)
            .and_then(Option::as_ref)
            .unwrap_or_else(|| panic!("missing codegen body for id {codegen_id}"))
    }

    pub(crate) fn body_fn_id(&self, codegen_id: u32) -> FnId {
        self.body(codegen_id).fn_id
    }

    pub(crate) fn body_id_for_fn(&self, fn_id: FnId) -> Option<u32> {
        self.body_slots
            .get(fn_id.0 as usize)
            .and_then(Option::as_ref)
            .map(|body| body.codegen_id)
    }

    pub(crate) fn callable_boundary(&self, boundary_id: u32) -> Option<&NativeCallableBoundarySurface> {
        self.callable_boundaries.get(&boundary_id)
    }

    pub(crate) fn callable_boundary_for_identity(&self, identity_fn: FnId) -> Option<&NativeCallableBoundarySurface> {
        self.callable_boundaries
            .values()
            .find(|boundary| boundary.identity_fn == identity_fn)
    }

    pub(crate) fn closure_target(&self, target_fn: FnId) -> Option<&NativeClosureTargetSurface> {
        self.closure_targets.get(&target_fn)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pins the missing-invariant guard's intent: a closure-target's
    /// published lane surface (captures then args) that agrees with the
    /// resolved target's own compiled ABI must pass silently -- this is
    /// the ordinary case (e.g. `enum_take_drop_split`'s fallback-boundary
    /// candidates when they genuinely share one physical ABI).
    #[test]
    fn agreeing_surface_and_compiled_abi_pass() {
        let published = NativeClosureTargetSurface {
            capture_count: 1,
            capture_reprs: vec![ArgRepr::RawAtom],
            arg_reprs: vec![ArgRepr::RawInt],
        };
        let compiled = vec![ArgRepr::RawAtom, ArgRepr::RawInt];
        require_closure_target_surface_agreement(FnId(137), "a direct closure call", &published, &compiled)
            .expect("identical capture+arg surfaces must agree with the compiled ABI");
    }

    /// Pins the actual `enum_predicate_search` defect this ticket fixes: a
    /// boundary publishes one extra arg lane (3 total: 1 capture + 2 args)
    /// for a target whose body actually compiled to 2 param lanes. Before
    /// this guard, that mismatch reached cranelift's own call-site
    /// construction and either tripped the verifier ("mismatched argument
    /// count: got 4, expected 5") or a later raw `panic!` -- never a clean,
    /// readable diagnostic. The guard must catch it as a plain `Err`
    /// instead, through production types (no test-only shims): the exact
    /// `NativeClosureTargetSurface`/`ArgRepr` types native codegen builds
    /// and compares at the direct-call consumption point.
    #[test]
    fn mismatched_surface_and_compiled_abi_produce_a_clean_error_not_a_panic() {
        let published = NativeClosureTargetSurface {
            capture_count: 1,
            capture_reprs: vec![ArgRepr::RawAtom],
            arg_reprs: vec![ArgRepr::RawInt, ArgRepr::RawAtom],
        };
        let compiled = vec![ArgRepr::RawAtom, ArgRepr::RawInt];
        let err = require_closure_target_surface_agreement(FnId(137), "a direct closure call", &published, &compiled)
            .expect_err("a published surface with an extra lane must be rejected, not silently accepted");
        let message = err.to_string();
        assert!(
            message.contains("closure target fn 137"),
            "error should name the offending target fn: {message}"
        );
        assert!(
            message.contains("incompatible physical ABI"),
            "error should use the same 'incompatible physical ABI' idiom as the fallback-boundary guard: {message}"
        );
        assert!(
            message.contains("a direct closure call"),
            "error should name the consumption-point context: {message}"
        );
    }

    /// A surface whose reprs are reordered (same multiset, different
    /// sequence) must also be rejected: physical ABI agreement is
    /// positional, not just a count/multiset match.
    #[test]
    fn reordered_surface_disagrees_with_compiled_abi() {
        let published = NativeClosureTargetSurface {
            capture_count: 0,
            capture_reprs: vec![],
            arg_reprs: vec![ArgRepr::RawInt, ArgRepr::RawAtom],
        };
        let compiled = vec![ArgRepr::RawAtom, ArgRepr::RawInt];
        require_closure_target_surface_agreement(FnId(1), "a direct closure call", &published, &compiled)
            .expect_err("reordered lanes are a real physical-ABI disagreement");
    }

    /// Ordinary case for the arity guard: a call site whose semantic
    /// argument count matches the target's published argument-LANE count
    /// one-for-one must pass silently (the common case, where no semantic
    /// argument spans more than one physical lane).
    #[test]
    fn matching_call_arity_and_arg_lane_count_pass() {
        let target = NativeClosureTargetSurface {
            capture_count: 1,
            capture_reprs: vec![ArgRepr::RawAtom],
            arg_reprs: vec![ArgRepr::RawInt, ArgRepr::ValueRef],
        };
        require_direct_closure_call_arity_agreement(FnId(7), "a direct closure call", 2, &target)
            .expect("one semantic argument per published argument lane must agree");
    }

    /// Pins the fz-k22.17 defect: a target whose accumulator argument
    /// compiled to a 2-lane shape publishes 3 argument lanes total (2 for
    /// the accumulator + 1 for the element) for a call site that only
    /// supplies 2 already-materialized semantic arguments (accumulator,
    /// element) -- one materialized value per logical argument, not per
    /// lane. Before this guard, `push_direct_closure_args` zipped `args`
    /// against `target.arg_reprs` by semantic index and silently under-
    /// filled the physical call (3 args + self + cont pushed vs 4 + self +
    /// cont declared), surfacing later as a bare cranelift verifier
    /// "argument count" panic. The guard must catch it as a clean `Err`.
    #[test]
    fn under_supplied_multi_lane_argument_produces_a_clean_error_not_a_panic() {
        let target = NativeClosureTargetSurface {
            capture_count: 0,
            capture_reprs: vec![],
            arg_reprs: vec![ArgRepr::RawInt, ArgRepr::ValueRef, ArgRepr::ValueRef],
        };
        let err = require_direct_closure_call_arity_agreement(FnId(137), "a direct closure call", 2, &target)
            .expect_err("2 materialized semantic arguments cannot fill 3 declared argument lanes");
        let message = err.to_string();
        assert!(
            message.contains("closure target fn 137"),
            "error should name the offending target fn: {message}"
        );
        assert!(
            message.contains("incompatible physical ABI"),
            "error should use the same 'incompatible physical ABI' idiom as the sibling guard: {message}"
        );
        assert!(
            message.contains("a direct closure call"),
            "error should name the consumption-point context: {message}"
        );
    }
}
