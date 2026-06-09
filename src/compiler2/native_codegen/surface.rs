//! Planner-free input surface for compiler2-owned native codegen.
//!
//! The old native driver starts from planner-owned artifacts, but the backend
//! fork only needs a narrower set of codegen facts: the prepared fz-IR bodies,
//! their per-body typing/dispatch facts, ABI lanes, callable-entry inventory,
//! and a few module-wide metadata tables. `NativeCodegenSurface` owns that
//! handoff so the planner wrapper can stay outside compiler2 native codegen.

use super::{ArgRepr, MidFlightArgShape};
use crate::compiler2::NativeBody;
use crate::diag::Diagnostics;
use crate::frontend::spec_registry::SpecRegistry;
use crate::fz_ir::{FnId, FnIr, Module};
use crate::ir_planner::{SpecPlan, fn_types::SpecKey};
use crate::types::{Ty, Types};
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeCallableEntrySurface {
    pub capture_count: usize,
    pub capture_key: Vec<crate::types::KeySlot>,
}

pub(crate) struct NativeCodegenSurface<'a> {
    pub module: &'a Module,
    pub diagnostics: Diagnostics,
    pub main_fn_id: Option<FnId>,
    /// Dense body-id slots consumed by compiler2 native codegen. Old planned
    /// code currently uses SpecId here; future Compiler2-native callers can
    /// choose any stable body numbering they want.
    pub body_slots: Vec<Option<NativeCodegenBody<'a>>>,
    /// Resolver for call-edge targets and callable-entry obligations.
    pub body_registry: SpecRegistry,
    pub callable_entries: BTreeMap<u32, NativeCallableEntrySurface>,
    pub mid_flight_cont_keys: Vec<(u32, Vec<MidFlightArgShape>)>,
    pub param_reprs: Vec<Vec<ArgRepr>>,
    pub return_reprs: Vec<ArgRepr>,
    pub native_abi_fns: HashSet<FnId>,
    pub cont_target_fns: HashSet<FnId>,
    pub cont_fns: HashSet<FnId>,
    pub closure_capture_counts: HashMap<FnId, usize>,
    pub cont_extras_count: HashMap<FnId, usize>,
    pub fn_halt_kinds: HashMap<u32, u32>,
}

pub(crate) struct NativeCodegenBody<'a> {
    pub codegen_id: u32,
    pub fn_idx: usize,
    pub fn_id: FnId,
    pub spec_key: SpecKey,
    pub spec_plan: SpecPlan,
    pub native_body: Option<&'a NativeBody>,
    pub body: &'a FnIr,
    pub display_name: String,
    pub reachable: bool,
}

impl<'a> NativeCodegenSurface<'a> {
    pub(crate) fn body(&self, codegen_id: u32) -> &NativeCodegenBody<'a> {
        self.body_slots
            .get(codegen_id as usize)
            .and_then(Option::as_ref)
            .unwrap_or_else(|| panic!("missing codegen body for id {codegen_id}"))
    }

    pub(crate) fn body_key(&self, codegen_id: u32) -> &SpecKey {
        &self.body(codegen_id).spec_key
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

    pub(crate) fn body_id_for_key<T: Types<Ty = Ty>>(&self, t: &T, key: &SpecKey) -> Option<u32> {
        self.body_registry.resolve_spec_key(t, key).map(|sid| sid.0)
    }
}
