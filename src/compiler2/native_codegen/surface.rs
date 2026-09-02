//! Planner-free input surface for compiler2-owned native codegen.
//!
//! The old native driver starts from planner-owned artifacts, but compiler2's
//! in-house backend only needs a narrower set of codegen facts: the prepared
//! fz-IR bodies, their per-body typing/dispatch facts, ABI lanes,
//! callable-boundary inventory, and a few module-wide metadata tables.
//! `NativeCodegenSurface` owns that handoff so planner-owned wrappers stay
//! outside compiler2 native codegen.

use super::{ArgRepr, MidFlightArgShape};
use crate::compiler2::NativeBody;
use crate::compiler2::artifact::NativeCallableBoundaryId;
use crate::diag::Diagnostics;
use crate::fz_ir::{FnId, FnIr, Module};
use crate::runtime_type_predicate::{CallableShape, CallableShapes};
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeCallableBoundarySurface {
    pub boundary_id: NativeCallableBoundaryId,
    pub identity_fn: FnId,
    /// The construction this boundary mints, as a runtime test names it: the
    /// function, and the projected capture types it closed over. `None` for a
    /// boundary over a callable that names no function, which no finite test
    /// can list.
    pub shape: Option<CallableShape>,
    pub target_fn: FnId,
    pub capture_count: usize,
    pub capture_reprs: Vec<ArgRepr>,
    pub arg_reprs: Vec<ArgRepr>,
    pub task_halt_repr: Option<ArgRepr>,
}

pub(crate) struct NativeCodegenSurface<'a> {
    pub module: &'a Module,
    pub diagnostics: Diagnostics,
    pub main_fn_id: Option<FnId>,
    pub body_slots: Vec<Option<NativeCodegenBody<'a>>>,
    pub callable_boundaries: BTreeMap<u32, NativeCallableBoundarySurface>,
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

    /// Every boundary whose construction a test ENUMERATES: the same function,
    /// closed over a capture layout inside the one the test names
    /// (fz-kdt.127). A test for "is this value one of these constructions"
    /// compares the value's code word against exactly these addresses, and
    /// never loads a capture.
    pub(crate) fn callable_boundaries_enumerated_by<'s>(
        &'s self,
        callables: &'s CallableShapes,
    ) -> impl Iterator<Item = &'s NativeCallableBoundarySurface> + 's {
        self.callable_boundaries
            .values()
            .filter(move |boundary| boundary.shape.as_ref().is_some_and(|shape| callables.enumerates(shape)))
    }
}
