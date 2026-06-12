//! Planner-free input surface for compiler2-owned native codegen.
//!
//! The old native driver starts from planner-owned artifacts, but compiler2's
//! in-house backend only needs a narrower set of codegen facts: the prepared
//! fz-IR bodies, their per-body typing/dispatch facts, ABI lanes,
//! callable-entry inventory, and a few module-wide metadata tables.
//! `NativeCodegenSurface` owns that handoff so planner-owned wrappers stay
//! outside compiler2 native codegen.

use super::{ArgRepr, MidFlightArgShape};
use crate::compiler2::NativeBody;
use crate::diag::Diagnostics;
use crate::fz_ir::{FnId, FnIr, Module};
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeCallableEntrySurface {
    pub target_fn: FnId,
    pub capture_count: usize,
    pub capture_key: Vec<crate::types::KeySlot<crate::compiler2::Ty>>,
}

pub(crate) struct NativeCodegenSurface<'a> {
    pub module: &'a Module,
    pub diagnostics: Diagnostics,
    pub main_fn_id: Option<FnId>,
    /// Number of populated body slots, fixed at construction so telemetry
    /// reads stored state instead of re-counting at emit points.
    pub spec_count: usize,
    pub body_slots: Vec<Option<NativeCodegenBody<'a>>>,
    pub callable_entries: BTreeMap<u32, NativeCallableEntrySurface>,
    pub mid_flight_cont_keys: Vec<(u32, Vec<MidFlightArgShape>)>,
    pub param_reprs: Vec<Vec<ArgRepr>>,
    pub return_reprs: Vec<ArgRepr>,
    pub native_abi_fns: HashSet<FnId>,
    pub cont_target_fns: HashSet<FnId>,
    pub cont_fns: HashSet<FnId>,
    pub closure_capture_counts: HashMap<FnId, usize>,
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
}
