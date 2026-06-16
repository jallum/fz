use std::collections::HashSet;

use super::RootId;
use super::transport::{
    BoundaryDescr, BoundaryId, CallableDescr, CallableId, CodegenSeam, ExecutableSymbol, LaneId, ShapeDescr, ShapeId,
    TransportPlan, TransportPosition,
};
use super::world::World;

pub(crate) trait TransportPlanTestHandler {
    fn transport_plan_defined(&self, world: &World<'_>, root: RootId);
}

pub(crate) fn default_transport_plan_test_handlers<'a>() -> Vec<Box<dyn TransportPlanTestHandler + 'a>> {
    vec![Box::new(TransportPlanGraphValidator)]
}

struct TransportPlanGraphValidator;

impl TransportPlanTestHandler for TransportPlanGraphValidator {
    fn transport_plan_defined(&self, world: &World<'_>, root: RootId) {
        let errors = validate_transport_plan_graph(world, root);
        assert!(
            errors.is_empty(),
            "transport plan for root {} is not vertically closed:\n{}",
            root.as_u32(),
            errors.join("\n")
        );
    }
}

fn validate_transport_plan_graph(world: &World<'_>, root: RootId) -> Vec<String> {
    let Some(plan) = world.transport().plans().get(root) else {
        return vec![format!("root {} has no committed transport plan", root.as_u32())];
    };
    let interners = world.transport().interners();
    let mut cx = ValidationContext {
        world,
        shape_ids: interners.shapes().map(|(id, _)| id).collect(),
        lane_ids: interners.lanes().map(|(id, _)| id).collect(),
        callable_ids: interners.callables().map(|(id, _)| id).collect(),
        boundary_ids: interners.boundaries().map(|(id, _)| id).collect(),
        executable_membership: plan.executable_membership.iter().cloned().collect(),
        visited_shapes: HashSet::new(),
        visited_callables: HashSet::new(),
        visited_boundaries: HashSet::new(),
        errors: Vec::new(),
    };
    cx.validate_plan(plan);
    cx.errors
}

struct ValidationContext<'a, 'w> {
    world: &'a World<'w>,
    shape_ids: HashSet<ShapeId>,
    lane_ids: HashSet<LaneId>,
    callable_ids: HashSet<CallableId>,
    boundary_ids: HashSet<BoundaryId>,
    executable_membership: HashSet<ExecutableSymbol>,
    visited_shapes: HashSet<ShapeId>,
    visited_callables: HashSet<CallableId>,
    visited_boundaries: HashSet<BoundaryId>,
    errors: Vec<String>,
}

impl ValidationContext<'_, '_> {
    fn validate_plan(&mut self, plan: &TransportPlan) {
        self.validate_executable(&plan.entry, "transport plan entry executable");
        for (position, shape) in plan.positions.iter() {
            self.validate_executable(position_executable(position), "transport position executable");
            self.validate_shape(*shape, plan, "transport position");
        }
        for fact in plan.codegen_seam_facts.iter() {
            self.validate_lane(fact.lane, "codegen seam fact lane");
            if let Some(shape) = fact.shape {
                self.validate_shape(shape, plan, "codegen seam fact shape");
            }
            match fact.seam {
                CodegenSeam::CallableBoundary { boundary } | CodegenSeam::FirstClassPublication { boundary } => {
                    self.validate_boundary(boundary, plan, "codegen seam boundary");
                }
                CodegenSeam::FunctionEntry { .. }
                | CodegenSeam::BlockParam { .. }
                | CodegenSeam::ReturnDelivery { .. }
                | CodegenSeam::ContinuationEntry { .. }
                | CodegenSeam::TailCall { .. }
                | CodegenSeam::ExternBoundary { .. } => {
                    if let Some(executable) = seam_executable(&fact.seam) {
                        self.validate_executable(executable, "codegen seam executable");
                    }
                }
            }
        }
        for (callable, facts) in plan.callables.iter() {
            self.validate_callable(*callable, plan, "callable fact key");
            for executable in facts.resolutions.iter() {
                self.validate_executable(executable, "callable fact resolution");
            }
            for surface in facts.direct_surfaces.iter() {
                for shape in surface.iter().copied() {
                    self.validate_shape(shape, plan, "callable direct surface");
                }
            }
            for lane in facts.capture_lanes.iter().copied() {
                self.validate_lane(lane, "callable fact capture lane");
            }
            for boundary in facts.boundary_ids.iter().copied() {
                self.validate_boundary(boundary, plan, "callable fact boundary");
            }
        }
        for (boundary, facts) in plan.boundaries.iter() {
            self.validate_boundary(*boundary, plan, "boundary fact key");
            for publication in facts.publications.iter() {
                let Some(shape) = plan.positions.get(publication).copied() else {
                    self.errors.push(format!(
                        "boundary {:?} publishes missing position {:?}",
                        boundary, publication
                    ));
                    continue;
                };
                self.validate_shape(shape, plan, "boundary publication position");
            }
        }
    }

    fn validate_shape(&mut self, shape: ShapeId, plan: &TransportPlan, context: &str) {
        if !self.shape_ids.contains(&shape) {
            self.errors
                .push(format!("{context} references unknown shape {:?}", shape));
            return;
        }
        if !self.visited_shapes.insert(shape) {
            return;
        }
        match self.world.transport().interners().shape(shape) {
            ShapeDescr::Nothing => {}
            ShapeDescr::Lane(lane) => self.validate_lane(*lane, "shape lane"),
            ShapeDescr::Tuple(items) => {
                for item in items.iter().copied() {
                    self.validate_shape(item, plan, "tuple shape child");
                }
            }
            ShapeDescr::Callable(callable) => self.validate_callable(*callable, plan, "callable shape"),
        }
    }

    fn validate_callable(&mut self, callable: CallableId, plan: &TransportPlan, context: &str) {
        if !self.callable_ids.contains(&callable) {
            self.errors
                .push(format!("{context} references unknown callable {:?}", callable));
            return;
        }
        if !plan.callables.contains_key(&callable) {
            self.errors.push(format!(
                "{context} references callable {:?} without plan facts",
                callable
            ));
        }
        if !self.visited_callables.insert(callable) {
            return;
        }
        let descr = self.world.transport().interners().callable(callable);
        self.validate_callable_descr(descr, plan);
    }

    fn validate_callable_descr(&mut self, descr: &CallableDescr, plan: &TransportPlan) {
        for shape in descr.capture_shapes.iter().copied() {
            self.validate_shape(shape, plan, "callable descriptor capture shape");
        }
        for lane in descr.capture_lanes.iter().copied() {
            self.validate_lane(lane, "callable descriptor capture lane");
        }
        for surface in descr.contract_surfaces.iter() {
            for shape in surface.iter().copied() {
                self.validate_shape(shape, plan, "callable descriptor contract surface");
            }
        }
    }

    fn validate_boundary(&mut self, boundary: BoundaryId, plan: &TransportPlan, context: &str) {
        if !self.boundary_ids.contains(&boundary) {
            self.errors
                .push(format!("{context} references unknown boundary {:?}", boundary));
            return;
        }
        if !self.visited_boundaries.insert(boundary) {
            return;
        }
        let descr = self.world.transport().interners().boundary(boundary);
        self.validate_boundary_descr(boundary, descr, plan);
    }

    fn validate_boundary_descr(&mut self, boundary: BoundaryId, descr: &BoundaryDescr, plan: &TransportPlan) {
        self.validate_callable(descr.callable, plan, "boundary descriptor callable");
        for shape in descr.surface_arg_shapes.iter().copied() {
            self.validate_shape(shape, plan, "boundary descriptor surface arg shape");
        }
        for lane in descr.published_capture_lanes.iter().copied() {
            self.validate_lane(lane, "boundary descriptor published capture lane");
        }
        for lane in descr.published_arg_lanes.iter().copied() {
            self.validate_lane(lane, "boundary descriptor published arg lane");
        }
        self.validate_shape(
            descr.published_return_shape,
            plan,
            "boundary descriptor published return shape",
        );
        for lane in descr.published_return_lanes.iter().copied() {
            self.validate_lane(lane, "boundary descriptor published return lane");
        }
        if !plan
            .callables
            .get(&descr.callable)
            .is_some_and(|facts| facts.boundary_ids.contains(&boundary))
        {
            self.errors.push(format!(
                "boundary {:?} is not listed by callable {:?} facts",
                boundary, descr.callable
            ));
        }
    }

    fn validate_lane(&mut self, lane: LaneId, context: &str) {
        if !self.lane_ids.contains(&lane) {
            self.errors
                .push(format!("{context} references unknown lane {:?}", lane));
        }
    }

    fn validate_executable(&mut self, executable: &ExecutableSymbol, context: &str) {
        if !self.executable_membership.contains(executable) {
            self.errors.push(format!(
                "{context} references executable outside root membership: {:?}",
                executable
            ));
        }
    }
}

fn position_executable(position: &TransportPosition) -> &ExecutableSymbol {
    match position {
        TransportPosition::ExecutableInput { executable, .. }
        | TransportPosition::ExecutableReturn { executable }
        | TransportPosition::ResumePayload { executable, .. }
        | TransportPosition::CallArg { executable, .. }
        | TransportPosition::EntryCapture { executable, .. }
        | TransportPosition::Value { executable, .. } => executable,
    }
}

fn seam_executable(seam: &CodegenSeam) -> Option<&ExecutableSymbol> {
    match seam {
        CodegenSeam::FunctionEntry { executable, .. }
        | CodegenSeam::BlockParam { executable, .. }
        | CodegenSeam::ReturnDelivery { executable }
        | CodegenSeam::ContinuationEntry { executable, .. }
        | CodegenSeam::TailCall { executable, .. }
        | CodegenSeam::ExternBoundary { executable } => Some(executable),
        CodegenSeam::CallableBoundary { .. } | CodegenSeam::FirstClassPublication { .. } => None,
    }
}
