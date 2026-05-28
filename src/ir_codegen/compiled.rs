#![allow(unused_imports)]

use super::*;
use crate::fz_ir::{
    BinOp, Const, Cont, ExternId, FnId, FnIr, Module, Prim, ReceiveAfter, ReceiveClause, Stmt,
    Term, UnOp,
};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

/// One separately compiled source module before link-time/runtime-global
/// state is assembled.
///
/// The `code` field carries module-local IR. Interface fields carry the
/// contract facts the linker validates before a runnable image exists.
#[derive(Debug, Clone)]
pub struct CompiledUnit {
    pub module: Option<crate::modules::identity::ModuleName>,
    pub code: Module,
    pub module_plan: Option<crate::ir_planner::ModulePlan>,
    pub exports: Vec<crate::modules::interface::InterfaceFn>,
    pub interface_fingerprint: Vec<String>,
    pub interface: Option<crate::modules::interface::ModuleInterface>,
}

impl CompiledUnit {
    #[cfg(test)]
    pub fn from_ir_module(
        code: Module,
        interface: Option<crate::modules::interface::ModuleInterface>,
        _diagnostics: crate::diag::Diagnostics,
    ) -> Self {
        Self::from_ir_module_with_plan(code, None, interface, _diagnostics)
    }

    pub fn from_ir_module_with_plan(
        code: Module,
        module_plan: Option<crate::ir_planner::ModulePlan>,
        interface: Option<crate::modules::interface::ModuleInterface>,
        _diagnostics: crate::diag::Diagnostics,
    ) -> Self {
        let module = interface
            .as_ref()
            .map(|interface| interface.name.clone())
            .or_else(|| {
                crate::modules::identity::ModuleName::parse_dotted(code.module_path()).ok()
            });
        let exports = interface
            .as_ref()
            .map(|interface| interface.exports.clone())
            .unwrap_or_default();
        let interface_fingerprint = interface
            .as_ref()
            .map(|interface| interface.fingerprint_inputs.clone())
            .unwrap_or_default();
        Self {
            module,
            code,
            module_plan,
            exports,
            interface_fingerprint,
            interface,
        }
    }
}

/// Linked runnable image: runtime-global JIT state plus execution entrypoints.
pub struct CompiledImage {
    inner: CompiledModule,
    metadata: Option<RuntimeImageMetadata>,
}

pub struct CompiledProgram {
    pub executable: CompiledModule,
    pub unit: CompiledUnit,
    pub runtime: RuntimeUnitMetadata,
}

impl CompiledProgram {
    pub fn new(unit: CompiledUnit, executable: CompiledModule) -> Self {
        let runtime =
            RuntimeUnitMetadata::from_compiled_module(unit.module.clone(), &unit, &executable);
        Self {
            executable,
            unit,
            runtime,
        }
    }

    pub fn link_image_with_telemetry(
        self,
        tel: &dyn crate::telemetry::Telemetry,
    ) -> Result<CompiledImage, ImageLinkError> {
        match self.link_image() {
            Ok(image) => {
                tel.event(&["fz", "link", "succeeded"], crate::metadata! { units: 1 });
                Ok(image)
            }
            Err(err) => {
                tel.event(
                    &["fz", "link", "failed"],
                    crate::metadata! { error: err.to_string() },
                );
                Err(err)
            }
        }
    }

    fn link_image(self) -> Result<CompiledImage, ImageLinkError> {
        let _linked_ir = link_ir_units(std::slice::from_ref(&self.unit))?;
        let metadata = RuntimeImageMetadata::link_units(std::slice::from_ref(&self.runtime))
            .map_err(ImageLinkError::RuntimeMetadata)?;
        Ok(CompiledImage {
            inner: self.executable,
            metadata: Some(metadata),
        })
    }
}

impl CompiledImage {
    pub fn from_linked(linked: CompiledModule) -> Self {
        Self {
            inner: linked,
            metadata: None,
        }
    }

    pub fn from_linked_with_telemetry(
        tel: &dyn crate::telemetry::Telemetry,
        units: usize,
        linked: CompiledModule,
    ) -> Self {
        tel.event(
            &["fz", "link", "succeeded"],
            crate::metadata! { units: units as i64 },
        );
        Self::from_linked(linked)
    }

    pub fn metadata(&self) -> Option<&RuntimeImageMetadata> {
        self.metadata.as_ref()
    }

    pub fn compiled_module(&self) -> &CompiledModule {
        &self.inner
    }
}

unsafe impl Send for CompiledImage {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImageLinkError {
    InterfaceFingerprintMismatch {
        module: Option<crate::modules::identity::ModuleName>,
    },
    UnresolvedExternalCalls {
        module: Option<crate::modules::identity::ModuleName>,
    },
    MissingImport {
        requester: Option<crate::modules::identity::ModuleName>,
        import: crate::modules::identity::ExportKey,
    },
    DuplicateProvider {
        import: crate::modules::identity::ExportKey,
    },
    RuntimeMetadata(RuntimeMetadataLinkError),
    MissingPlannerFacts {
        module: Option<crate::modules::identity::ModuleName>,
    },
}

impl std::fmt::Display for ImageLinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InterfaceFingerprintMismatch { module } => write!(
                f,
                "compiled unit `{}` does not implement its recorded interface fingerprint",
                module
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| "<root>".to_string())
            ),
            Self::UnresolvedExternalCalls { module } => write!(
                f,
                "compiled unit `{}` still has unresolved external module calls",
                module
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| "<root>".to_string())
            ),
            Self::MissingImport { requester, import } => write!(
                f,
                "module `{}` imports missing export `{}`",
                requester
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| "<root>".to_string()),
                import
            ),
            Self::DuplicateProvider { import } => {
                write!(f, "export `{}` has more than one provider", import)
            }
            Self::RuntimeMetadata(err) => write!(f, "{}", err),
            Self::MissingPlannerFacts { module } => write!(
                f,
                "compiled unit `{}` is missing planner facts required for linked codegen",
                module
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| "<root>".to_string())
            ),
        }
    }
}

impl std::error::Error for ImageLinkError {}

pub struct LinkedIr {
    pub module: Module,
    pub module_plan: Option<crate::ir_planner::ModulePlan>,
}

pub fn link_ir_units(units: &[CompiledUnit]) -> Result<Module, ImageLinkError> {
    let mut linker = IrUnitLinker::new();
    for unit in units {
        linker.add_unit(unit)?;
    }
    linker.finish().map(|linked| linked.module)
}

pub fn link_ir_units_with_plan(units: &[CompiledUnit]) -> Result<LinkedIr, ImageLinkError> {
    let mut linker = IrUnitLinker::new();
    for unit in units {
        linker.add_unit(unit)?;
    }
    linker.finish_with_plan()
}

#[derive(Default)]
struct IrUnitLinker {
    linked: Module,
    linked_plan: Option<crate::ir_planner::ModulePlan>,
    missing_planner_facts: Option<Option<crate::modules::identity::ModuleName>>,
    export_map: BTreeMap<crate::modules::identity::ExportKey, FnId>,
}

impl IrUnitLinker {
    fn new() -> Self {
        let mut linker = Self::default();
        linker.linked.atom_names.extend([
            "nil".to_string(),
            "true".to_string(),
            "false".to_string(),
        ]);
        linker
    }

    fn add_unit(&mut self, unit: &CompiledUnit) -> Result<(), ImageLinkError> {
        if let Some(interface) = &unit.interface
            && interface.fingerprint_inputs != unit.interface_fingerprint
        {
            return Err(ImageLinkError::InterfaceFingerprintMismatch {
                module: unit.module.clone(),
            });
        }

        let fn_map = self.copy_fns(unit);
        self.copy_externs(unit, &fn_map);
        self.copy_external_edges(unit, &fn_map);
        self.copy_protocol_facts(unit, &fn_map);
        self.copy_specs(unit, &fn_map);
        self.copy_planner_facts(unit, &fn_map);
        self.copy_type_facts(unit);
        self.copy_exports(unit, &fn_map)?;
        Ok(())
    }

    fn finish(mut self) -> Result<LinkedIr, ImageLinkError> {
        self.resolve_external_call_edges_in_plan();
        match self.linked.rewrite_external_calls_for_lto(&self.export_map) {
            Ok(_) => Ok(LinkedIr {
                module: self.linked,
                module_plan: self.linked_plan,
            }),
            Err(crate::fz_ir::ExternalLinkError::MissingTarget(import)) => {
                let requester = self
                    .linked
                    .external_call_edges
                    .iter()
                    .find(|edge| edge.target == import)
                    .and_then(|edge| module_for_linked_fn(&self.linked, edge.callsite.caller));
                Err(ImageLinkError::MissingImport { requester, import })
            }
            Err(crate::fz_ir::ExternalLinkError::MissingCallsite(callsite)) => {
                let module = module_for_linked_fn(&self.linked, callsite.caller);
                Err(ImageLinkError::UnresolvedExternalCalls { module })
            }
        }
    }

    fn finish_with_plan(self) -> Result<LinkedIr, ImageLinkError> {
        if self.missing_planner_facts.is_some() {
            return Err(ImageLinkError::MissingPlannerFacts {
                module: self.missing_planner_facts.flatten(),
            });
        }
        self.finish()
    }

    fn copy_fns(&mut self, unit: &CompiledUnit) -> BTreeMap<FnId, FnId> {
        let mut map = BTreeMap::new();
        let base = self.linked.fns.len() as u32;
        for (offset, f) in unit.code.fns.iter().enumerate() {
            let new_id = FnId(base + offset as u32);
            map.insert(f.id, new_id);
        }
        for f in &unit.code.fns {
            let copied = self.remap_fn(f.clone(), &map, &unit.code.atom_names);
            self.linked.fn_idx.insert(copied.id, self.linked.fns.len());
            self.linked.fns.push(copied);
        }
        for old in &unit.code.boundary_fns {
            if let Some(new) = map.get(old) {
                self.linked.boundary_fns.insert(*new);
            }
        }
        map
    }

    fn copy_externs(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) {
        let mut extern_map = HashMap::new();
        for ext in &unit.code.externs {
            let new_id = ExternId(self.linked.externs.len() as u32);
            extern_map.insert(ext.id, new_id);
            let mut copied = ext.clone();
            copied.id = new_id;
            self.linked
                .extern_idx
                .insert(copied.id, self.linked.externs.len());
            self.linked.externs.push(copied);
        }
        if !extern_map.is_empty() {
            for f in self.linked.fns.iter_mut().rev().take(fn_map.len()) {
                remap_fn_externs(f, &extern_map);
            }
        }
    }

    fn copy_external_edges(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) {
        self.linked
            .external_call_edges
            .extend(unit.code.external_call_edges.iter().map(|edge| {
                let mut edge = edge.clone();
                if let Some(caller) = fn_map.get(&edge.callsite.caller) {
                    edge.callsite.caller = *caller;
                }
                edge
            }));
    }

    fn copy_protocol_facts(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) {
        self.linked.protocol_call_targets.extend(
            unit.code
                .protocol_call_targets
                .iter()
                .filter_map(|(fid, target)| fn_map.get(fid).map(|new| (*new, target.clone()))),
        );
        self.linked
            .protocol_registry
            .protocols
            .extend(unit.code.protocol_registry.protocols.clone());
        self.linked
            .protocol_registry
            .impls
            .extend(unit.code.protocol_registry.impls.clone());
    }

    fn copy_specs(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) {
        self.linked.declared_specs.extend(
            unit.code
                .declared_specs
                .iter()
                .filter_map(|(fid, spec)| fn_map.get(fid).map(|new| (*new, spec.clone()))),
        );
    }

    fn copy_planner_facts(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) {
        let Some(plan) = &unit.module_plan else {
            self.missing_planner_facts
                .get_or_insert_with(|| unit.module.clone());
            return;
        };
        merge_module_plan(&mut self.linked_plan, remap_module_plan(plan, fn_map));
    }

    fn resolve_external_call_edges_in_plan(&mut self) {
        let Some(plan) = &mut self.linked_plan else {
            return;
        };
        for spec in plan.specs.values_mut() {
            for (callsite, edge_plan) in &mut spec.call_edges {
                let crate::ir_planner::fn_types::CallEdgeTarget::External {
                    target,
                    input,
                    demand,
                } = &edge_plan.target
                else {
                    continue;
                };
                if let Some(fn_id) = self.export_map.get(target).copied() {
                    let _ = crate::fz_ir::rewrite_external_callsite_for_link(
                        &mut self.linked,
                        callsite,
                        fn_id,
                    );
                    edge_plan.target = crate::ir_planner::fn_types::CallEdgeTarget::Local(
                        crate::ir_planner::fn_types::SpecKey {
                            fn_id,
                            input: input.clone(),
                            demand: demand.clone(),
                        },
                    );
                }
            }
        }
    }

    fn copy_type_facts(&mut self, unit: &CompiledUnit) {
        self.linked
            .opaque_inners
            .extend(unit.code.opaque_inners.clone());
        self.linked
            .brand_inners
            .extend(unit.code.brand_inners.clone());
    }

    fn copy_exports(
        &mut self,
        unit: &CompiledUnit,
        fn_map: &BTreeMap<FnId, FnId>,
    ) -> Result<(), ImageLinkError> {
        let Some(module) = &unit.module else {
            return Ok(());
        };
        for export in &unit.exports {
            let key = crate::modules::identity::ExportKey::new(
                module.clone(),
                export.name.clone(),
                export.arity,
            );
            let qualified = format!("{}.{}", module, export.name);
            let target = unit
                .code
                .fns
                .iter()
                .find(|f| f.name == qualified && f.block(f.entry).params.len() == export.arity)
                .and_then(|f| fn_map.get(&f.id).copied());
            if let Some(target) = target
                && self.export_map.insert(key.clone(), target).is_some()
            {
                return Err(ImageLinkError::DuplicateProvider { import: key });
            }
        }
        if let Some(interface) = &unit.interface {
            for protocol_impl in &interface.protocol_impls {
                for callback in &protocol_impl.callbacks {
                    let qualified = format!("{}.{}", callback.module, callback.name);
                    let target = unit
                        .code
                        .fns
                        .iter()
                        .find(|f| {
                            f.name == qualified && f.block(f.entry).params.len() == callback.arity
                        })
                        .and_then(|f| fn_map.get(&f.id).copied());
                    if let Some(target) = target
                        && self.export_map.insert(callback.clone(), target).is_some()
                    {
                        return Err(ImageLinkError::DuplicateProvider {
                            import: callback.clone(),
                        });
                    }
                }
            }
        }
        Ok(())
    }

    fn remap_fn(
        &mut self,
        mut f: FnIr,
        fn_map: &BTreeMap<FnId, FnId>,
        atom_names: &[String],
    ) -> FnIr {
        f.id = fn_map[&f.id];
        for block in &mut f.blocks {
            for stmt in &mut block.stmts {
                remap_stmt(stmt, fn_map, &mut self.linked.atom_names, atom_names);
            }
            remap_term(&mut block.terminator, fn_map);
        }
        f
    }
}

fn merge_module_plan(
    out: &mut Option<crate::ir_planner::ModulePlan>,
    incoming: crate::ir_planner::ModulePlan,
) {
    match out {
        Some(existing) => {
            existing.specs.extend(incoming.specs);
            existing
                .effective_returns
                .extend(incoming.effective_returns);
            existing.any_key_specs.extend(incoming.any_key_specs);
            existing.spec_precedence.extend(incoming.spec_precedence);
            existing.effect_summaries.extend(incoming.effect_summaries);
            existing.dead_branches.extend(incoming.dead_branches);
            #[cfg(test)]
            existing.closure_handles.extend(incoming.closure_handles);
        }
        None => *out = Some(incoming),
    }
}

fn remap_module_plan(
    plan: &crate::ir_planner::ModulePlan,
    fn_map: &BTreeMap<FnId, FnId>,
) -> crate::ir_planner::ModulePlan {
    crate::ir_planner::ModulePlan {
        specs: plan
            .specs
            .iter()
            .map(|(key, spec)| (remap_spec_key(key, fn_map), remap_spec_plan(spec, fn_map)))
            .collect(),
        effective_returns: plan
            .effective_returns
            .iter()
            .map(|(key, ty)| (remap_spec_key(key, fn_map), ty.clone()))
            .collect(),
        any_key_specs: plan
            .any_key_specs
            .iter()
            .filter_map(|(fid, key)| fn_map.get(fid).map(|new| (*new, key.clone())))
            .collect(),
        spec_precedence: plan
            .spec_precedence
            .iter()
            .map(|(key, value)| (remap_spec_key(key, fn_map), *value))
            .collect(),
        effect_summaries: plan
            .effect_summaries
            .iter()
            .map(|(key, value)| (remap_spec_key(key, fn_map), *value))
            .collect(),
        dead_branches: plan
            .dead_branches
            .iter()
            .filter_map(|((fid, block), dead)| fn_map.get(fid).map(|new| ((*new, *block), *dead)))
            .collect(),
        #[cfg(test)]
        closure_handles: plan
            .closure_handles
            .iter()
            .filter_map(|(fid, captures)| fn_map.get(fid).map(|new| (*new, captures.clone())))
            .collect(),
    }
}

fn remap_spec_plan(
    spec: &crate::ir_planner::SpecPlan,
    fn_map: &BTreeMap<FnId, FnId>,
) -> crate::ir_planner::SpecPlan {
    crate::ir_planner::SpecPlan {
        vars: spec.vars.clone(),
        block_envs: spec.block_envs.clone(),
        fn_constants: spec
            .fn_constants
            .iter()
            .filter_map(|(var, fid)| fn_map.get(fid).map(|new| (*var, *new)))
            .collect(),
        reachable_blocks: spec.reachable_blocks.clone(),
        dead_branches: spec.dead_branches.clone(),
        call_edges: spec
            .call_edges
            .iter()
            .map(|(callsite, edge)| {
                (
                    remap_callsite(callsite, fn_map),
                    remap_call_edge_plan(edge, fn_map),
                )
            })
            .collect(),
        extern_marshals: spec.extern_marshals.clone(),
    }
}

fn remap_callsite(
    callsite: &crate::fz_ir::CallsiteId,
    fn_map: &BTreeMap<FnId, FnId>,
) -> crate::fz_ir::CallsiteId {
    let mut out = callsite.clone();
    if let Some(caller) = fn_map.get(&out.caller) {
        out.caller = *caller;
    }
    out
}

fn remap_call_edge_plan(
    edge: &crate::ir_planner::fn_types::CallEdgePlan,
    fn_map: &BTreeMap<FnId, FnId>,
) -> crate::ir_planner::fn_types::CallEdgePlan {
    crate::ir_planner::fn_types::CallEdgePlan {
        target: match &edge.target {
            crate::ir_planner::fn_types::CallEdgeTarget::Local(key) => {
                crate::ir_planner::fn_types::CallEdgeTarget::Local(remap_spec_key(key, fn_map))
            }
            crate::ir_planner::fn_types::CallEdgeTarget::External {
                target,
                input,
                demand,
            } => crate::ir_planner::fn_types::CallEdgeTarget::External {
                target: target.clone(),
                input: input.clone(),
                demand: demand.clone(),
            },
        },
        return_use: edge.return_use.clone(),
        return_context: edge
            .return_context
            .as_ref()
            .map(|plan| remap_return_context_plan(plan, fn_map)),
    }
}

fn remap_return_context_plan(
    plan: &crate::ir_planner::fn_types::ReturnContextPlan,
    fn_map: &BTreeMap<FnId, FnId>,
) -> crate::ir_planner::fn_types::ReturnContextPlan {
    use crate::ir_planner::fn_types::ReturnContextPlan;
    match plan {
        ReturnContextPlan::DirectContinuation {
            continuation,
            result_param,
            tail_ty,
        } => ReturnContextPlan::DirectContinuation {
            continuation: remapped_fn_id(*continuation, fn_map),
            result_param: *result_param,
            tail_ty: tail_ty.clone(),
        },
        ReturnContextPlan::ConsThenDirect {
            continuation,
            pivot,
            tail,
            tail_ty,
        } => ReturnContextPlan::ConsThenDirect {
            continuation: remapped_fn_id(*continuation, fn_map),
            pivot: *pivot,
            tail: *tail,
            tail_ty: tail_ty.clone(),
        },
        ReturnContextPlan::ContinuationListTailBridge {
            continuation,
            pivot,
            tail,
            tail_ty,
        } => ReturnContextPlan::ContinuationListTailBridge {
            continuation: remapped_fn_id(*continuation, fn_map),
            pivot: *pivot,
            tail: *tail,
            tail_ty: tail_ty.clone(),
        },
        ReturnContextPlan::ContinuationEmptyTail {
            continuation,
            target,
            tail_ty,
        } => ReturnContextPlan::ContinuationEmptyTail {
            continuation: remapped_fn_id(*continuation, fn_map),
            target: remap_spec_key(target, fn_map),
            tail_ty: tail_ty.clone(),
        },
        ReturnContextPlan::TailCallDestination {
            callee,
            source,
            tail,
            tail_ty,
        } => ReturnContextPlan::TailCallDestination {
            callee: remapped_fn_id(*callee, fn_map),
            source: *source,
            tail: *tail,
            tail_ty: tail_ty.clone(),
        },
    }
}

fn remap_spec_key(
    key: &crate::ir_planner::fn_types::SpecKey,
    fn_map: &BTreeMap<FnId, FnId>,
) -> crate::ir_planner::fn_types::SpecKey {
    let mut out = key.clone();
    out.fn_id = remapped_fn_id(out.fn_id, fn_map);
    out
}

fn remapped_fn_id(fid: FnId, fn_map: &BTreeMap<FnId, FnId>) -> FnId {
    fn_map.get(&fid).copied().unwrap_or(fid)
}

fn module_for_linked_fn(
    module: &Module,
    fn_id: FnId,
) -> Option<crate::modules::identity::ModuleName> {
    module
        .fn_idx
        .get(&fn_id)
        .and_then(|idx| module.fns.get(*idx))
        .and_then(|f| {
            if f.owner_module.is_empty() {
                None
            } else {
                crate::modules::identity::ModuleName::parse_dotted(&f.owner_module).ok()
            }
        })
}

fn remap_stmt(
    stmt: &mut Stmt,
    fn_map: &BTreeMap<FnId, FnId>,
    linked_atoms: &mut Vec<String>,
    unit_atoms: &[String],
) {
    let Stmt::Let(_, prim) = stmt;
    remap_prim(prim, fn_map, linked_atoms, unit_atoms);
}

fn remap_prim(
    prim: &mut Prim,
    fn_map: &BTreeMap<FnId, FnId>,
    linked_atoms: &mut Vec<String>,
    unit_atoms: &[String],
) {
    match prim {
        Prim::Const(Const::Atom(id)) => {
            if let Some(name) = unit_atoms.get(*id as usize) {
                let new_id = intern_linked_atom(linked_atoms, name);
                *id = new_id;
            }
        }
        Prim::MakeClosure(_, fid, _) => remap_fn_id(fid, fn_map),
        _ => {}
    }
}

fn remap_fn_externs(f: &mut FnIr, extern_map: &HashMap<ExternId, ExternId>) {
    for block in &mut f.blocks {
        for Stmt::Let(_, prim) in &mut block.stmts {
            if let Prim::Extern(id, _) = prim
                && let Some(new_id) = extern_map.get(id)
            {
                *id = *new_id;
            }
        }
    }
}

fn remap_term(term: &mut Term, fn_map: &BTreeMap<FnId, FnId>) {
    match term {
        Term::Call {
            callee,
            continuation,
            ..
        } => {
            remap_fn_id(callee, fn_map);
            remap_cont(continuation, fn_map);
        }
        Term::TailCall { callee, .. } => remap_fn_id(callee, fn_map),
        Term::CallClosure { continuation, .. } | Term::Receive { continuation, .. } => {
            remap_cont(continuation, fn_map);
        }
        Term::ReceiveMatched { clauses, after, .. } => {
            for clause in clauses {
                remap_receive_clause(clause, fn_map);
            }
            if let Some(after) = after {
                remap_receive_after(after, fn_map);
            }
        }
        Term::Goto(_, _)
        | Term::If { .. }
        | Term::TailCallClosure { .. }
        | Term::Return(_)
        | Term::Halt(_) => {}
    }
}

fn remap_cont(cont: &mut Cont, fn_map: &BTreeMap<FnId, FnId>) {
    remap_fn_id(&mut cont.fn_id, fn_map);
}

fn remap_receive_clause(clause: &mut ReceiveClause, fn_map: &BTreeMap<FnId, FnId>) {
    if let Some(guard) = &mut clause.guard {
        remap_fn_id(guard, fn_map);
    }
    remap_fn_id(&mut clause.body, fn_map);
}

fn remap_receive_after(after: &mut ReceiveAfter, fn_map: &BTreeMap<FnId, FnId>) {
    remap_fn_id(&mut after.body, fn_map);
}

fn remap_fn_id(fid: &mut FnId, fn_map: &BTreeMap<FnId, FnId>) {
    if let Some(new) = fn_map.get(fid) {
        *fid = *new;
    }
}

fn intern_linked_atom(atoms: &mut Vec<String>, name: &str) -> u32 {
    if let Some(idx) = atoms.iter().position(|existing| existing == name) {
        idx as u32
    } else {
        let idx = atoms.len() as u32;
        atoms.push(name.to_string());
        idx
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RuntimeEntrypoints {
    pub resume: bool,
    pub main: bool,
    pub spawn: bool,
    pub drain_dtor: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuntimeStaticClosure {
    pub closure_schema_id: u32,
    pub fn_id: u32,
    pub halt_kind: u32,
}

#[derive(Debug, Clone)]
pub struct RuntimeUnitMetadata {
    pub module: Option<crate::modules::identity::ModuleName>,
    pub atoms: Vec<String>,
    pub schemas: Vec<Schema>,
    pub frame_sizes: Vec<u32>,
    pub exported_symbols: BTreeMap<String, u32>,
    pub imported_refs: Vec<crate::modules::identity::ExportKey>,
    pub static_closures: Vec<RuntimeStaticClosure>,
    pub halt_kinds: BTreeMap<u32, u32>,
    pub entrypoints: RuntimeEntrypoints,
}

impl RuntimeUnitMetadata {
    #[cfg(test)]
    pub fn from_ir_module(
        module: Option<crate::modules::identity::ModuleName>,
        ir: &Module,
    ) -> Self {
        Self {
            module,
            atoms: ir.atom_names.clone(),
            schemas: ir.schemas.clone(),
            frame_sizes: Vec::new(),
            exported_symbols: BTreeMap::new(),
            imported_refs: ir
                .external_call_edges
                .iter()
                .map(|edge| edge.target.clone())
                .collect(),
            static_closures: Vec::new(),
            halt_kinds: BTreeMap::new(),
            entrypoints: RuntimeEntrypoints::default(),
        }
    }

    pub fn from_compiled_module(
        module: Option<crate::modules::identity::ModuleName>,
        unit: &CompiledUnit,
        compiled: &CompiledModule,
    ) -> Self {
        let schemas = {
            let registry = compiled.user_schemas.borrow();
            (0..registry.len())
                .map(|id| registry.get(id as u32).clone())
                .collect()
        };
        let exported_symbols = unit
            .module
            .as_ref()
            .map(|module| {
                unit.exports
                    .iter()
                    .enumerate()
                    .map(|(idx, export)| {
                        (
                            format!("{}.{}/{}", module, export.name, export.arity),
                            idx as u32,
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        Self {
            module,
            atoms: compiled.atom_names.clone(),
            schemas,
            frame_sizes: compiled.frame_sizes.clone(),
            exported_symbols,
            imported_refs: unit
                .code
                .external_call_edges
                .iter()
                .map(|edge| edge.target.clone())
                .collect(),
            static_closures: compiled
                .static_closure_targets
                .iter()
                .map(
                    |(closure_schema_id, fn_id, _, halt_kind)| RuntimeStaticClosure {
                        closure_schema_id: *closure_schema_id,
                        fn_id: *fn_id,
                        halt_kind: *halt_kind,
                    },
                )
                .collect(),
            halt_kinds: compiled
                .fn_halt_kinds
                .iter()
                .map(|(fn_id, halt_kind)| (*fn_id, *halt_kind))
                .collect(),
            entrypoints: RuntimeEntrypoints {
                resume: true,
                main: true,
                spawn: true,
                drain_dtor: true,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeUnitRelocations {
    pub input_index: usize,
    pub atom_ids: Vec<u32>,
    pub schema_ids: Vec<u32>,
    pub frame_ids: Vec<u32>,
}

#[derive(Debug, Clone)]
pub struct RuntimeImageMetadata {
    pub atoms: Vec<String>,
    pub schemas: Vec<Schema>,
    pub frame_sizes: Vec<u32>,
    pub exported_symbols: BTreeMap<String, u32>,
    pub imported_refs: Vec<crate::modules::identity::ExportKey>,
    pub static_closures: Vec<(usize, RuntimeStaticClosure)>,
    pub halt_kinds: BTreeMap<u32, u32>,
    pub entrypoints: RuntimeEntrypoints,
    pub relocations: Vec<RuntimeUnitRelocations>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeMetadataLinkError {
    DuplicateModule(crate::modules::identity::ModuleName),
    DuplicateExport(String),
}

impl std::fmt::Display for RuntimeMetadataLinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateModule(module) => {
                write!(f, "runtime metadata for module `{}` appears twice", module)
            }
            Self::DuplicateExport(symbol) => {
                write!(f, "runtime export `{}` appears twice", symbol)
            }
        }
    }
}

impl std::error::Error for RuntimeMetadataLinkError {}

impl RuntimeImageMetadata {
    pub fn link_units(units: &[RuntimeUnitMetadata]) -> Result<Self, RuntimeMetadataLinkError> {
        let mut seen_modules = BTreeSet::new();
        for unit in units {
            if let Some(module) = &unit.module
                && !seen_modules.insert(module.clone())
            {
                return Err(RuntimeMetadataLinkError::DuplicateModule(module.clone()));
            }
        }

        let atom_keys: BTreeSet<String> = units
            .iter()
            .flat_map(|unit| unit.atoms.iter().cloned())
            .collect();
        let atoms: Vec<String> = atom_keys.into_iter().collect();
        let atom_ids: BTreeMap<String, u32> = atoms
            .iter()
            .enumerate()
            .map(|(id, atom)| (atom.clone(), id as u32))
            .collect();

        let mut schema_by_key = BTreeMap::new();
        for unit in units {
            for schema in &unit.schemas {
                schema_by_key
                    .entry(schema_key(schema))
                    .or_insert_with(|| schema.clone());
            }
        }
        let schemas: Vec<Schema> = schema_by_key.values().cloned().collect();
        let schema_ids: BTreeMap<String, u32> = schema_by_key
            .keys()
            .enumerate()
            .map(|(id, key)| (key.clone(), id as u32))
            .collect();

        let mut unit_order: Vec<usize> = (0..units.len()).collect();
        unit_order.sort_by_key(|idx| unit_sort_key(&units[*idx], *idx));

        let mut relocations_by_input: Vec<Option<RuntimeUnitRelocations>> = vec![None; units.len()];
        let mut frame_sizes = Vec::new();
        let mut halt_kinds = BTreeMap::new();
        let mut static_closures = Vec::new();
        let mut exported_symbols = BTreeMap::new();
        let mut imported_refs = BTreeSet::new();
        let mut entrypoints = RuntimeEntrypoints::default();

        for input_index in unit_order {
            let unit = &units[input_index];
            let atom_relocs = unit
                .atoms
                .iter()
                .map(|atom| atom_ids[atom])
                .collect::<Vec<_>>();
            let schema_relocs = unit
                .schemas
                .iter()
                .map(|schema| schema_ids[&schema_key(schema)])
                .collect::<Vec<_>>();
            let frame_base = frame_sizes.len() as u32;
            let frame_relocs = (0..unit.frame_sizes.len())
                .map(|local| frame_base + local as u32)
                .collect::<Vec<_>>();
            frame_sizes.extend(unit.frame_sizes.iter().copied());
            for (local_fn_id, halt_kind) in &unit.halt_kinds {
                if let Some(global_fn_id) = frame_relocs.get(*local_fn_id as usize) {
                    halt_kinds.insert(*global_fn_id, *halt_kind);
                }
            }
            for (symbol, fn_id) in &unit.exported_symbols {
                if exported_symbols
                    .insert(symbol.clone(), frame_base + *fn_id)
                    .is_some()
                {
                    return Err(RuntimeMetadataLinkError::DuplicateExport(symbol.clone()));
                }
            }
            imported_refs.extend(unit.imported_refs.iter().cloned());
            static_closures.extend(
                unit.static_closures
                    .iter()
                    .cloned()
                    .map(|closure| (input_index, closure)),
            );
            entrypoints.resume |= unit.entrypoints.resume;
            entrypoints.main |= unit.entrypoints.main;
            entrypoints.spawn |= unit.entrypoints.spawn;
            entrypoints.drain_dtor |= unit.entrypoints.drain_dtor;
            relocations_by_input[input_index] = Some(RuntimeUnitRelocations {
                input_index,
                atom_ids: atom_relocs,
                schema_ids: schema_relocs,
                frame_ids: frame_relocs,
            });
        }

        static_closures.sort();
        Ok(Self {
            atoms,
            schemas,
            frame_sizes,
            exported_symbols,
            imported_refs: imported_refs.into_iter().collect(),
            static_closures,
            halt_kinds,
            entrypoints,
            relocations: relocations_by_input
                .into_iter()
                .map(|r| r.expect("relocation slot filled for every input unit"))
                .collect(),
        })
    }

    #[cfg(test)]
    pub fn render_stable(&self) -> String {
        let mut lines = Vec::new();
        lines.push(format!("atoms={}", self.atoms.join(",")));
        lines.push(format!(
            "schemas={}",
            self.schemas
                .iter()
                .map(schema_key)
                .collect::<Vec<_>>()
                .join(",")
        ));
        lines.push(format!(
            "frames={}",
            self.frame_sizes
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ));
        lines.push(format!(
            "exports={}",
            self.exported_symbols
                .iter()
                .map(|(symbol, id)| format!("{}:{}", symbol, id))
                .collect::<Vec<_>>()
                .join(",")
        ));
        lines.push(format!(
            "imports={}",
            self.imported_refs
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ));
        lines.join("\n")
    }
}

fn unit_sort_key(unit: &RuntimeUnitMetadata, input_index: usize) -> String {
    unit.module
        .as_ref()
        .map(ToString::to_string)
        .unwrap_or_else(|| format!("~{}", input_index))
}

fn schema_key(schema: &Schema) -> String {
    let fields = schema
        .fields
        .iter()
        .map(|field| format!("{}:{:?}", field.offset, field.kind))
        .collect::<Vec<_>>()
        .join("|");
    format!("{}:{}:[{}]", schema.name, schema.size, fields)
}

/// Compiled module: persistent JITModule + per-fn ptr table + schemas. The
/// host runs a fn via `compiled.run(fn_id)` (constructs an internal default
/// Process) or `compiled.run_in(fn_id, &mut Process)` (caller-owned Process).
pub struct CompiledModule {
    pub(super) _module: JITModule,
    /// fz_fn_id -> compiled fn ptr.
    pub(super) fn_ptrs: HashMap<u32, *const u8>,
    /// User-data SchemaRegistry. Shared with every Process built by
    /// `make_process()` through its Heap.
    pub(crate) user_schemas: std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>,
    /// Per-fn frame size (bytes), indexed by FnId.0. Consumed by
    /// `fz_alloc_frame_dyn` for fns whose id is only known dynamically
    /// (closure invocation).
    pub(crate) frame_sizes: Vec<u32>,
    /// Heap-registered schema ids for the bitstring reader/result tuples.
    /// None means no bitstring prim is present in this module.
    pub(crate) bs_tuple_arity1_schema: Option<u32>,
    pub(crate) bs_tuple_arity3_schema: Option<u32>,
    /// Atom names indexed by id. Copied into each Process so
    /// `any_value::debug::render` can spell atoms as `:name`.
    pub(crate) atom_names: Vec<String>,
    pub(crate) diagnostics: crate::diag::Diagnostics,
    /// Zero-capture closure-target spec singletons resolved to code
    /// addresses at JIT-finalize time. `make_process` allocates one
    /// 24-byte off-heap closure per entry into `Process.static_closures`.
    /// See docs/cps-in-clif.md §8.2.
    pub(crate) static_closure_targets: Vec<(u32, u32, *const u8, u32 /* halt_kind */)>,
    /// SystemV→Tail-CC shim `fz_spawn_entry(closure) -> i64`. Allocates a
    /// halt-cont and indirect-calls the zero-arg closure with
    /// `(self, halt_cont)`. Used by `Runtime::spawn_closure`.
    pub(crate) spawn_entry_addr: *const u8,
    /// SystemV→Tail-CC shim `fz_main_entry(main_fp) -> i64`. Allocates a
    /// halt-cont and indirect-calls main with `(halt_cont)`. Used by
    /// `Runtime::spawn(fn_id)` / `CompiledModule::run_internal`.
    pub(crate) main_entry_addr: *const u8,
    /// SystemV→Tail-CC shim `fz_drain_dtor_entry(closure, payload_ref) -> i64`.
    /// The scheduler calls this once per entry on
    /// `process.heap.pending_dtors` at task-exit; dispatches the dtor
    /// closure with payload + a fresh Strict halt-cont.
    pub(crate) drain_dtor_entry_addr: *const u8,
    /// Finalized addresses of the three `fz_halt_cont_body_{tagged,i64,f64}`
    /// Tail-CC fns, indexed by repr kind (0=ValueRef, 1=RawInt, 2=RawF64).
    /// Null slots (unused reprs in this program) are populated lazily by
    /// `fz_get_halt_cont` at first use.
    pub(crate) halt_cont_body_addrs: [*const u8; 3],
    /// Per-FnId halt-cont singleton kind (the entry fn's any-key return
    /// repr). The Rust scheduler picks the matching
    /// `process.halt_cont_singletons[kind]` when dispatching via
    /// `fz_main_entry`. Default kind 0 (ValueRef) when absent.
    pub(crate) fn_halt_kinds: HashMap<u32, u32>,
    /// Single `fz_resume(cont) -> i64` SystemV shim. Reads the code
    /// pointer through the runtime closure ABI and tail-calls the
    /// continuation body with `cont` as self. Bound args live in the
    /// outcome closure env, so arity is invisible to the shim.
    pub(crate) resume_addr: *const u8,
}

impl CompiledModule {
    /// Typer-side diagnostics collected during `compile`. Includes both
    /// warnings and errors; drivers must route through
    /// `diag::report_or_exit` so error-severity entries actually halt.
    pub fn diagnostics(&self) -> &crate::diag::Diagnostics {
        &self.diagnostics
    }
}

unsafe impl Send for CompiledModule {}

impl CompiledModule {
    pub fn fn_ptr(&self, fn_id: FnId) -> Option<*const u8> {
        self.fn_ptrs.get(&fn_id.0).copied()
    }

    /// Construct a fresh Process bound to this module's compile-time data
    /// (SchemaRegistry, frame_sizes, bs_tuple_arity*_schema). Multiple
    /// Processes can be made from the same CompiledModule and run
    /// concurrently (one worker at a time per Process; libdispatch model).
    pub fn make_process(&self) -> Process {
        let mut p = Process {
            heap: fz_runtime::heap::Heap::new(64 * 1024, std::rc::Rc::clone(&self.user_schemas)),
            halt_value: 0,
            bs_builder: None,
            frame_sizes: self.frame_sizes.clone(),
            atom_names: self.atom_names.clone(),
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
            pid: 0,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
            parked_matched: None,
            runnable_closure: std::ptr::null_mut(),
            halt_cont_singletons: [std::ptr::null_mut(); 3],
            pending_closure_entry: std::ptr::null_mut(),
            pending_main_entry: std::ptr::null_mut(),
            pending_main_entry_fn_id: 0,
            static_closures: Vec::new(),
            static_closure_bufs: Vec::new(),
            quiet_quanta: 0,
            scheduler_yields: 0,
            interpreter_yields: 0,
            reductions_remaining: fz_runtime::process::DEFAULT_REDUCTIONS_PER_QUANTUM,
            reductions_per_quantum: fz_runtime::process::DEFAULT_REDUCTIONS_PER_QUANTUM,
            reductions_executed: 0,
            reduction_yields: 0,
            allocation_pressure_yields: 0,
            yield_reasons: 0,
            pending_yield_continuation_margin_before_bytes: 0,
            max_yield_continuation_bytes: 0,
            min_yield_continuation_margin_before_bytes: 0,
            min_yield_continuation_margin_after_bytes: 0,
        };
        // One static singleton per zero-cap closure-target spec.
        // See docs/cps-in-clif.md §8.2.
        p.init_static_closures(&self.static_closure_targets);
        // Seed all three halt-cont singletons; each slot's body sig
        // matches its repr kind (ValueRef / RawInt / RawF64).
        p.init_halt_cont_singletons(self.halt_cont_body_addrs);
        p.heap.reset_alloc_stats();
        p
    }

    /// Run one quantum for a Process. Resumes from `process.next_frame`
    /// (which the caller — typically the Runtime in src/runtime.rs — must
    /// have set to a fresh entry frame or the saved continuation from a
    /// prior yield). The caller is responsible for CURRENT_PROCESS
    /// install/uninstall; we just trampoline. On halt the trampoline
    /// returns null; we write that back to process.next_frame so the
    /// caller can observe completion.
    pub(crate) fn run_quantum(&self, process: &mut Process) {
        /// Park-time GC trigger (cps-in-clif §7). Called at every
        /// shim-return boundary; if `heap.should_gc()` is set, runs
        /// Cheney over every scheduler-owned heap root (mailbox,
        /// receive templates, runnable + pending entry closures) and
        /// rewrites those pointers to their to-space copies.
        fn park_time_gc(process: &mut Process) {
            if !process.needs_boundary_gc() {
                return;
            }

            fn closure_root(ptr: *mut u8) -> fz_runtime::any_value::AnyValue {
                if ptr.is_null() {
                    fz_runtime::any_value::AnyValue::null()
                } else if let Some(value) =
                    fz_runtime::any_value::AnyValue::decode_tagged_heap_bits(ptr as u64)
                {
                    value
                } else {
                    fz_runtime::any_value::AnyValue::heap_ptr(
                        ptr,
                        fz_runtime::any_value::ValueKind::CLOSURE,
                    )
                }
            }

            fn closure_bits(value: fz_runtime::any_value::AnyValue) -> *mut u8 {
                if value.kind() == fz_runtime::any_value::ValueKind::NULL {
                    std::ptr::null_mut()
                } else {
                    value.heap_addr().expect("scheduler closure root")
                }
            }

            fn push_closure_root(
                roots: &mut Vec<fz_runtime::any_value::AnyValue>,
                ptr: *mut u8,
            ) -> Option<usize> {
                if ptr.is_null() {
                    None
                } else {
                    let idx = roots.len();
                    roots.push(closure_root(ptr));
                    Some(idx)
                }
            }

            let mut mailbox_roots: Vec<fz_runtime::any_value::AnyValueRef> =
                process.mailbox.iter().copied().collect();

            let parked_clause_start = 0usize;
            let mut roots: Vec<fz_runtime::any_value::AnyValue> = Vec::new();
            if let Some(park) = process.parked_matched.as_ref() {
                roots.extend(park.clause_bodies.iter().map(|&p| closure_root(p)));
                roots.push(closure_root(park.after_cont));
            }

            let runnable_idx = push_closure_root(&mut roots, process.runnable_closure);
            let pending_closure_idx = push_closure_root(&mut roots, process.pending_closure_entry);

            let mut null_root = std::ptr::null_mut();
            process.heap.gc_with_value_and_any_value_ref_roots(
                &mut null_root,
                &mut roots,
                &mut mailbox_roots,
            );

            process.mailbox.clear();
            process.mailbox.extend(mailbox_roots);

            if let Some(park) = process.parked_matched.as_mut() {
                for (i, body) in park.clause_bodies.iter_mut().enumerate() {
                    *body = closure_bits(roots[parked_clause_start + i]);
                }
                let after_idx = parked_clause_start + park.clause_bodies.len();
                park.after_cont = closure_bits(roots[after_idx]);
            }

            if let Some(idx) = runnable_idx {
                process.runnable_closure = closure_bits(roots[idx]);
            }

            if let Some(idx) = pending_closure_idx {
                process.pending_closure_entry = closure_bits(roots[idx]);
            }

            process.heap.clear_should_gc_flag();
            process.clear_yield_reasons();
        }

        // Selective-receive initial scan. Hit sets runnable_closure and
        // cancels the after-timer via the scheduler hook; Miss blocks the
        // task; NotApplicable is a no-op.
        match fz_runtime::sched::initial_scan(process) {
            fz_runtime::sched::ScanOutcome::Hit => {
                // Fall through to the dispatch branch below.
            }
            fz_runtime::sched::ScanOutcome::Miss => {
                process.next_frame = std::ptr::null_mut();
                return;
            }
            fz_runtime::sched::ScanOutcome::NotApplicable => {}
        }
        fn run_scheduler_closure(resume_addr: *const u8, process: &mut Process, closure: *mut u8) {
            let closure = fz_runtime::any_value::AnyValueRef::from_heap_object(
                fz_runtime::any_value::ValueKind::CLOSURE,
                closure as *const u8,
            )
            .expect("scheduler closure ref")
            .raw_word();
            let process_ptr = process as *mut Process;
            let _ = unsafe { fz_runtime::pinned_abi::call1(resume_addr, process_ptr, closure) };
        }

        // One dispatch decision per quantum. Variants are listed in
        // scheduling-priority order; the classifier returns the first
        // match. Receive wakeup beats fresh main-entry beats fresh
        // closure-entry; Idle is the no-work fallthrough.
        enum Dispatch {
            // Receive wakeup: a matcher hit (from sender-probe,
            // after-timer fire, or the initial-scan above) picked the
            // winning clause and bound values into the outcome closure
            // env. Dispatch through the single SystemV `fz_resume(cont)`
            // shim.
            RunnableClosure(*mut u8),
            // Fresh main-style task entry: fn ptr queued by
            // `Runtime::spawn` or `run_internal`. Dispatch via
            // `fz_main_entry`; the body runs synchronously to halt or
            // Receive.
            MainEntry { fp: *mut u8, kind: usize },
            // Fresh task entry: closure queued by
            // `Runtime::spawn_closure`. Dispatch via `fz_spawn_entry`;
            // the body runs synchronously to halt or Receive. On Receive
            // it parks a matcher record and the next wakeup
            // materializes runnable_closure.
            ClosureEntry(*mut u8),
            // All fz fns are Tail-CC; dispatch flows through the three
            // SystemV shims above. No uniform fns exist, so no
            // frame-by-frame trampoline loop is needed.
            Idle,
        }

        let dispatch = if let Some(closure) = process.take_runnable_closure() {
            Dispatch::RunnableClosure(closure)
        } else if !process.pending_main_entry.is_null() {
            let fp = process.pending_main_entry;
            process.pending_main_entry = std::ptr::null_mut();
            // Pick the halt-cont singleton matching the entry fn's
            // return-repr kind.
            let kind = self
                .fn_halt_kinds
                .get(&process.pending_main_entry_fn_id)
                .copied()
                .unwrap_or(0) as usize;
            Dispatch::MainEntry { fp, kind }
        } else if !process.pending_closure_entry.is_null() {
            let cl_ptr = process.pending_closure_entry;
            process.pending_closure_entry = std::ptr::null_mut();
            Dispatch::ClosureEntry(cl_ptr)
        } else {
            Dispatch::Idle
        };

        match dispatch {
            Dispatch::RunnableClosure(closure) => {
                run_scheduler_closure(self.resume_addr, process, closure);
                process.next_frame = std::ptr::null_mut();
                park_time_gc(process);
            }
            Dispatch::MainEntry { fp, kind } => {
                let halt_cl = fz_runtime::any_value::AnyValueRef::from_heap_object(
                    fz_runtime::any_value::ValueKind::CLOSURE,
                    process.halt_cont_singletons[kind] as *const u8,
                )
                .expect("halt continuation ref")
                .raw_word();
                let process_ptr = process as *mut Process;
                let _ = unsafe {
                    fz_runtime::pinned_abi::call2(
                        self.main_entry_addr,
                        process_ptr,
                        fp as u64,
                        halt_cl,
                    )
                };
                process.next_frame = std::ptr::null_mut();
                park_time_gc(process);
            }
            Dispatch::ClosureEntry(cl_ptr) => {
                let cl_ref = fz_runtime::any_value::AnyValueRef::from_heap_object(
                    fz_runtime::any_value::ValueKind::CLOSURE,
                    cl_ptr as *const u8,
                )
                .expect("pending closure ref")
                .raw_word();
                let process_ptr = process as *mut Process;
                let _ = unsafe {
                    fz_runtime::pinned_abi::call1(self.spawn_entry_addr, process_ptr, cl_ref)
                };
                process.next_frame = std::ptr::null_mut();
                park_time_gc(process);
            }
            Dispatch::Idle => {
                process.next_frame = std::ptr::null_mut();
            }
        }
    }
}

#[cfg(test)]
impl CompiledModule {
    /// Registered zero-capture closure-target specs.
    pub fn static_closure_targets(&self) -> &[(u32, u32, *const u8, u32)] {
        &self.static_closure_targets
    }

    /// Run the trampoline with `fn_id` as the entry fn, using a fresh Process
    /// stashed in DEFAULT_PROCESS for post-run inspection.
    pub fn run(&self, fn_id: FnId) -> i64 {
        DEFAULT_PROCESS.with(|c| *c.borrow_mut() = Some(self.make_process()));
        let ptr = DEFAULT_PROCESS.with(|c| {
            let mut b = c.borrow_mut();
            b.as_mut().unwrap() as *mut Process
        });
        let _current_process = fz_runtime::process::CurrentProcessGuard::install(ptr);
        self.run_internal(fn_id)
    }

    /// Run with a caller-owned Process.
    pub fn run_in(&self, fn_id: FnId, process: &mut Process) -> i64 {
        let ptr = process as *mut Process;
        let _current_process = fz_runtime::process::CurrentProcessGuard::install(ptr);
        self.run_internal(fn_id)
    }

    pub(crate) fn run_internal(&self, fn_id: FnId) -> i64 {
        let fp = self
            .fn_ptrs
            .get(&fn_id.0)
            .copied()
            .unwrap_or_else(|| panic!("no fn ptr for entry {}", fn_id.0));
        // Drive the process through ordinary bounded-quantum scheduling until
        // it halts. There is no unbounded special case: every quantum spends
        // the normal reduction budget and yields at its boundary. With a
        // single process the yielded continuation is simply the next thing
        // dispatched, so the loop reschedules it — exactly mirroring
        // `Runtime::run`'s per-process handling, minus the registry.
        {
            let process = current_process();
            process.pending_main_entry = fp as *mut u8;
            process.pending_main_entry_fn_id = fn_id.0;
            loop {
                // Running before the quantum is what distinguishes a
                // mid-flight yield (still Running, continuation produced)
                // from a receive-park (state flipped to Blocked) afterward.
                process.state = ProcessState::Running;
                process.reset_reduction_budget();
                self.run_quantum(process);
                let mid_flight =
                    process.state == ProcessState::Running && !process.runnable_closure.is_null();
                if !mid_flight {
                    // Halted, parked, or idle: a single-process run is done.
                    break;
                }
                // Mid-flight yield: do scheduler-boundary maintenance and let
                // the next quantum resume through the runnable continuation.
                process
                    .boundary_maintenance::<()>(|p| {
                        p.heap
                            .gc_process_roots(&mut p.runnable_closure, &mut p.mailbox);
                        Ok(())
                    })
                    .expect("single-process boundary maintenance is infallible");
                process.state = ProcessState::Ready;
            }
        }
        // Single-shot entry path: flush surviving MSO resources and run
        // their dtor closures as fz code before returning. Mirrors the
        // task-exit drain in `Runtime::run_until_idle` and
        // `aot_run_queue_loop`.
        {
            let proc_mut = current_process();
            fz_runtime::procbin::mso_drop_all_deferred(&mut proc_mut.heap);
            while let Some((closure, payload_ref)) = proc_mut.heap.pending_dtors.pop_front() {
                let process_ptr = proc_mut as *mut Process;
                let _ = unsafe {
                    fz_runtime::pinned_abi::call2(
                        self.drain_dtor_entry_addr,
                        process_ptr,
                        closure,
                        payload_ref,
                    )
                };
            }
        }
        current_process().halt_value
    }
}

#[cfg(test)]
impl CompiledImage {
    pub fn run(&self, fn_id: FnId) -> i64 {
        self.inner.run(fn_id)
    }
}

/// Everything `compile_with_backend` collects during the shared pipeline,
/// handed to the backend's `emit_metadata_carriers` and `finalize`.
///
/// The fz user `Module` (post type-rewrite) is intentionally NOT here —
/// backends only need the codegen metadata at finalize time. They've
/// already seen the module while declaring fns and compiling bodies.
pub struct CompiledMetadata {
    pub fn_ids: HashMap<u32, FuncId>,
    pub user_schemas: std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>,
    pub frame_sizes: Vec<u32>,
    pub atom_names: Vec<String>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    /// Sorted list of tuple arities the program will allocate. JIT ignores
    /// it (its runtime shares `user_schemas`); AOT bakes it into a `.data`
    /// symbol so `fz_aot_setup` re-registers the same `Tuple{N}` schemas in
    /// matching order.
    pub tuple_arities: Vec<u32>,
    pub diagnostics: crate::diag::Diagnostics,
    /// FnId of fz user `main`, if present. AOT needs it to wire the C
    /// `main` shim; JIT keeps it as a convenience for the run path.
    pub main_fn_id: Option<FnId>,
    /// Zero-capture closure-target specs as `(cl_sid, fn_id, stub_func_id,
    /// halt_kind)`. JIT finalize resolves stub_func_id to a code address;
    /// `make_process` populates `Process.static_closures` from the result.
    pub static_closure_targets: Vec<(u32, u32, FuncId, u32 /* halt_kind */)>,
    pub spawn_entry_id: FuncId,
    pub main_entry_id: FuncId,
    pub drain_dtor_entry_id: FuncId,
    /// Three `fz_halt_cont_body` fns indexed by repr kind (0=ValueRef,
    /// 1=RawInt, 2=RawF64). Sigs: (ValueRef|i64|f64, i64) -> i64 tail.
    /// Bodies call the matching `halt_implicit_*` and return 0.
    pub halt_cont_body_ids: [FuncId; 3],
    /// Per-FnId halt-cont singleton kind (the entry fn's any-key return
    /// repr). The Rust scheduler picks the matching halt_cont_singletons
    /// slot when dispatching via `fz_main_entry`.
    pub fn_halt_kinds: HashMap<u32, u32>,
    /// See `CompiledModule::resume_addr`.
    pub resume_id: FuncId,
}
