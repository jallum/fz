#![allow(unused_imports)]

use super::*;
use crate::diag::Diagnostics;
#[cfg(test)]
use crate::exec::runtime::{ProcessExitCapture, Runtime};
use crate::fz_ir::{
    BinOp, CallsiteId, Const, Cont, ExternId, ExternalLinkError, FnId, FnIr, Module, Prim, ReceiveAfter, ReceiveClause,
    Stmt, Term, UnOp, rewrite_external_callsite_for_link,
};
use crate::ir_planner::fn_types::{
    BodyKey, CallEdgePlan, CallEdgeTarget, CallableCapability, ReturnContract, ReturnStrategy, SpecKey,
};
use crate::ir_planner::{ModulePlan, SpecPlan};
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{InterfaceFn, ModuleInterface};
use crate::telemetry::Telemetry;
use crate::telemetry::bus::ConfiguredTelemetry;
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
use fz_runtime::any_value::{AnyValue, AnyValueRef, ValueKind};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema, SchemaRegistry};
use fz_runtime::pinned_abi::call1;
use fz_runtime::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Node};
use fz_runtime::sched::{ScanOutcome, initial_scan};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::ptr::null_mut;
use std::rc::Rc;
use std::slice::from_ref;
use std::sync::Arc;

/// One separately compiled source module before link-time/runtime-global
/// state is assembled.
///
/// The `code` field carries module-local IR. Interface fields carry the
/// contract facts the linker validates before a runnable image exists.
#[derive(Debug, Clone)]
pub struct CompiledUnit {
    pub module: Option<ModuleName>,
    pub code: Module,
    pub module_plan: Option<ModulePlan>,
    pub interfaces: BTreeMap<ModuleName, ModuleInterface>,
    pub interface_fingerprints: BTreeMap<ModuleName, Vec<String>>,
}

impl CompiledUnit {
    #[cfg(test)]
    pub fn from_ir_module(
        code: Module,
        interfaces: BTreeMap<ModuleName, ModuleInterface>,
        _diagnostics: Diagnostics,
    ) -> Self {
        Self::from_ir_module_with_plan(code, None, interfaces, _diagnostics)
    }

    pub fn from_ir_module_with_plan(
        code: Module,
        module_plan: Option<ModulePlan>,
        interfaces: BTreeMap<ModuleName, ModuleInterface>,
        _diagnostics: Diagnostics,
    ) -> Self {
        let module = if interfaces.len() == 1 {
            interfaces.keys().next().cloned()
        } else {
            ModuleName::parse_dotted(code.module_path()).ok()
        };
        let interface_fingerprints = interfaces
            .iter()
            .map(|(module, interface)| (module.clone(), interface.fingerprint_inputs.clone()))
            .collect();
        Self {
            module,
            code,
            module_plan,
            interfaces,
            interface_fingerprints,
        }
    }

    pub fn with_code_and_plan(mut self, code: Module, module_plan: ModulePlan) -> Self {
        self.code = code;
        self.module_plan = Some(module_plan);
        self
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
        let runtime = RuntimeUnitMetadata::from_compiled_module(unit.module.clone(), &unit, &executable);
        Self {
            executable,
            unit,
            runtime,
        }
    }

    pub fn link_image_with_telemetry(self, tel: &dyn Telemetry) -> Result<CompiledImage, ImageLinkError> {
        match self.link_image() {
            Ok(image) => {
                tel.event(&["fz", "link", "succeeded"], crate::metadata! { units: 1 });
                Ok(image)
            }
            Err(err) => {
                tel.event(&["fz", "link", "failed"], crate::metadata! { error: err.to_string() });
                Err(err)
            }
        }
    }

    fn link_image(self) -> Result<CompiledImage, ImageLinkError> {
        let _linked_ir = link_ir_units(from_ref(&self.unit))?;
        let metadata =
            RuntimeImageMetadata::link_units(from_ref(&self.runtime)).map_err(ImageLinkError::RuntimeMetadata)?;
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

    pub fn from_linked_with_telemetry(tel: &dyn Telemetry, units: usize, linked: CompiledModule) -> Self {
        tel.event(&["fz", "link", "succeeded"], crate::metadata! { units: units as i64 });
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
        module: Option<ModuleName>,
    },
    UnresolvedExternalCalls {
        module: Option<ModuleName>,
    },
    MissingImport {
        requester: Option<ModuleName>,
        import: ExportKey,
    },
    DuplicateProvider {
        import: ExportKey,
    },
    RuntimeMetadata(RuntimeMetadataLinkError),
}

impl fmt::Display for ImageLinkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        }
    }
}

impl Error for ImageLinkError {}

pub fn link_ir_units(units: &[CompiledUnit]) -> Result<Module, ImageLinkError> {
    let mut linker = IrUnitLinker::new();
    for unit in units {
        linker.add_unit(unit)?;
    }
    linker.finish()
}

#[derive(Default)]
struct IrUnitLinker {
    linked: Module,
    linked_plan: Option<ModulePlan>,
    export_map: BTreeMap<ExportKey, FnId>,
    next_fn_id: u32,
}

impl IrUnitLinker {
    fn new() -> Self {
        let mut linker = Self::default();
        linker
            .linked
            .atom_names
            .extend(["nil".to_string(), "true".to_string(), "false".to_string()]);
        linker
    }

    fn add_unit(&mut self, unit: &CompiledUnit) -> Result<(), ImageLinkError> {
        for (module, interface) in &unit.interfaces {
            let expected = unit
                .interface_fingerprints
                .get(module)
                .cloned()
                .unwrap_or_default();
            if interface.fingerprint_inputs != expected {
                return Err(ImageLinkError::InterfaceFingerprintMismatch {
                    module: Some(module.clone()),
                });
            }
        }

        let mut fn_map = self.copy_fns(unit);
        self.copy_named_surface(unit, &mut fn_map);
        self.copy_externs(unit, &fn_map);
        self.copy_external_edges(unit, &fn_map);
        self.copy_protocol_facts(unit, &fn_map);
        self.copy_specs(unit, &fn_map);
        self.copy_planner_facts(unit, &fn_map);
        self.copy_type_facts(unit);
        self.copy_exports(unit, &fn_map)?;
        Ok(())
    }

    /// Resolve external call edges (using the merged planner facts) and rewrite
    /// stub callsites to their linked targets. Mutates `self.linked` in place;
    /// both finish paths share it.
    fn resolve_links(&mut self) -> Result<(), ImageLinkError> {
        self.resolve_external_call_edges_in_plan();
        match self.linked.rewrite_external_calls_for_lto(&self.export_map) {
            Ok(_) => Ok(()),
            Err(ExternalLinkError::MissingTarget(import)) => {
                let requester = self
                    .linked
                    .external_call_edges
                    .iter()
                    .find(|edge| edge.target == import)
                    .and_then(|edge| module_for_linked_fn(&self.linked, edge.callsite.caller));
                Err(ImageLinkError::MissingImport { requester, import })
            }
            Err(ExternalLinkError::MissingCallsite(callsite)) => {
                let module = module_for_linked_fn(&self.linked, callsite.caller);
                Err(ImageLinkError::UnresolvedExternalCalls { module })
            }
        }
    }

    fn finish(mut self) -> Result<Module, ImageLinkError> {
        self.resolve_links()?;
        Ok(self.linked)
    }

    fn copy_fns(&mut self, unit: &CompiledUnit) -> BTreeMap<FnId, FnId> {
        let mut map = BTreeMap::new();
        let base = self.next_fn_id;
        for (offset, f) in unit.code.fns.iter().enumerate() {
            let new_id = FnId(base + offset as u32);
            map.insert(f.id, new_id);
        }
        self.next_fn_id = base + unit.code.fns.len() as u32;
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

    fn copy_named_surface(&mut self, unit: &CompiledUnit, fn_map: &mut BTreeMap<FnId, FnId>) {
        for entry in &unit.code.named_fns {
            let linked_fn_id = if let Some(mapped) = fn_map.get(&entry.fn_id).copied() {
                mapped
            } else {
                let new_id = FnId(self.next_fn_id);
                self.next_fn_id += 1;
                fn_map.insert(entry.fn_id, new_id);
                new_id
            };
            if self
                .linked
                .named_fns
                .iter()
                .any(|existing| existing.name == entry.name && existing.arity == entry.arity)
            {
                continue;
            }
            self.linked.named_fns.push(crate::fz_ir::NamedFnSurfaceEntry {
                name: entry.name.clone(),
                arity: entry.arity,
                fn_id: linked_fn_id,
            });
        }
    }

    fn copy_externs(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) {
        let mut extern_map = HashMap::new();
        for ext in &unit.code.externs {
            let new_id = ExternId(self.linked.externs.len() as u32);
            extern_map.insert(ext.id, new_id);
            let mut copied = ext.clone();
            copied.id = new_id;
            self.linked.extern_idx.insert(copied.id, self.linked.externs.len());
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
                .filter_map(|(fid, spec)| fn_map.get(fid).copied().map(|new| (new, spec.clone()))),
        );
        self.linked.function_correspondence.extend(
            unit.code
                .function_correspondence
                .iter()
                .filter_map(|(fid, groups)| fn_map.get(fid).copied().map(|new| (new, groups.clone()))),
        );
        self.linked.continuation_provenance.extend(
            unit.code
                .continuation_provenance
                .iter()
                .filter_map(|(fid, provenance)| fn_map.get(fid).copied().map(|new| (new, provenance.clone()))),
        );
    }

    fn copy_planner_facts(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) {
        // A unit without planner facts simply contributes none; the linker's
        // internal `linked_plan` only needs to cover the edges it resolves, and
        // the compile pipeline plans the linked module before codegen.
        if let Some(plan) = &unit.module_plan {
            merge_module_plan(&mut self.linked_plan, remap_module_plan(plan, fn_map));
        }
    }

    fn resolve_external_call_edges_in_plan(&mut self) {
        let structural_edges: HashSet<_> = self
            .linked
            .external_call_edges
            .iter()
            .map(|edge| edge.callsite.clone())
            .collect();
        let mut rewritten_plan_edges = HashSet::new();
        let Some(plan) = &mut self.linked_plan else {
            return;
        };
        for spec in plan.specs.values_mut() {
            for (callsite, edge_plan) in &mut spec.call_edges {
                let CallEdgeTarget::External { target, input, demand } = &edge_plan.target else {
                    continue;
                };
                if let Some(fn_id) = self.export_map.get(target).copied() {
                    if !structural_edges.contains(callsite) && rewritten_plan_edges.insert(callsite.clone()) {
                        let _ = rewrite_external_callsite_for_link(&mut self.linked, callsite, fn_id);
                    }
                    edge_plan.target = CallEdgeTarget::Local(SpecKey {
                        fn_id,
                        input: input.clone(),
                        demand: demand.clone(),
                    });
                }
            }
        }
    }

    fn copy_type_facts(&mut self, unit: &CompiledUnit) {
        self.linked.opaque_inners.extend(unit.code.opaque_inners.clone());
        self.linked.brand_inners.extend(unit.code.brand_inners.clone());
        self.linked.struct_schemas.extend(unit.code.struct_schemas.clone());
    }

    fn copy_exports(&mut self, unit: &CompiledUnit, fn_map: &BTreeMap<FnId, FnId>) -> Result<(), ImageLinkError> {
        for (module, interface) in &unit.interfaces {
            for export in &interface.exports {
                let key = ExportKey::new(module.clone(), export.name.clone(), export.arity);
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
            for protocol_impl in &interface.protocol_impls {
                for callback in &protocol_impl.callbacks {
                    let qualified = format!("{}.{}", callback.module, callback.name);
                    let target = unit
                        .code
                        .fns
                        .iter()
                        .find(|f| f.name == qualified && f.block(f.entry).params.len() == callback.arity)
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

    fn remap_fn(&mut self, mut f: FnIr, fn_map: &BTreeMap<FnId, FnId>, atom_names: &[String]) -> FnIr {
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

fn merge_module_plan(out: &mut Option<ModulePlan>, incoming: ModulePlan) {
    match out {
        Some(existing) => {
            existing.specs.extend(incoming.specs);
            existing.reachable_specs.extend(incoming.reachable_specs);
            existing.spec_roles.extend(incoming.spec_roles);
            existing.effective_returns.extend(incoming.effective_returns);
            existing.any_key_specs.extend(incoming.any_key_specs);
            existing.spec_precedence.extend(incoming.spec_precedence);
            existing.fn_effects.extend(incoming.fn_effects);
            existing.dead_branches.extend(incoming.dead_branches);
            existing.return_capabilities.extend(incoming.return_capabilities);
        }
        None => *out = Some(incoming),
    }
}

fn remap_module_plan(plan: &ModulePlan, fn_map: &BTreeMap<FnId, FnId>) -> ModulePlan {
    ModulePlan {
        specs: plan
            .specs
            .iter()
            .map(|(key, spec)| (remap_spec_key(key, fn_map), remap_spec_plan(spec, fn_map)))
            .collect(),
        reachable_specs: plan
            .reachable_specs
            .iter()
            .map(|key| remap_spec_key(key, fn_map))
            .collect(),
        spec_roles: plan
            .spec_roles
            .iter()
            .map(|(key, role)| (remap_body_key(key, fn_map), *role))
            .collect(),
        effective_returns: plan
            .effective_returns
            .iter()
            .map(|(key, ty)| (remap_body_key(key, fn_map), ty.clone()))
            .collect(),
        any_key_specs: plan
            .any_key_specs
            .iter()
            .filter_map(|(fid, key)| fn_map.get(fid).map(|new| (*new, key.clone())))
            .collect(),
        spec_precedence: plan
            .spec_precedence
            .iter()
            .map(|(key, value)| (remap_body_key(key, fn_map), *value))
            .collect(),
        fn_effects: plan
            .fn_effects
            .iter()
            .filter_map(|(fid, value)| fn_map.get(fid).map(|new| (*new, *value)))
            .collect(),
        dead_branches: plan
            .dead_branches
            .iter()
            .filter_map(|((fid, block), dead)| fn_map.get(fid).map(|new| ((*new, *block), *dead)))
            .collect(),
        return_capabilities: plan
            .return_capabilities
            .iter()
            .filter_map(|(fid, cap)| fn_map.get(fid).map(|new| (*new, *cap)))
            .collect(),
    }
}

fn remap_spec_plan(spec: &SpecPlan, fn_map: &BTreeMap<FnId, FnId>) -> SpecPlan {
    SpecPlan {
        vars: spec.vars.clone(),
        block_envs: spec.block_envs.clone(),
        callable_capabilities: spec
            .callable_capabilities
            .iter()
            .filter_map(|(var, capability)| {
                remap_callable_capability(capability, fn_map).map(|capability| (*var, capability))
            })
            .collect(),
        reachable_blocks: spec.reachable_blocks.clone(),
        dead_branches: spec.dead_branches.clone(),
        call_edges: spec
            .call_edges
            .iter()
            .map(|(callsite, edge)| (remap_callsite(callsite, fn_map), remap_call_edge_plan(edge, fn_map)))
            .collect(),
        callable_entry_targets: spec.callable_entry_targets.clone(),
        extern_marshals: spec.extern_marshals.clone(),
        brand_inners: spec.brand_inners.clone(),
        opaque_inners: spec.opaque_inners.clone(),
    }
}

fn remap_callable_capability(
    capability: &CallableCapability,
    fn_map: &BTreeMap<FnId, FnId>,
) -> Option<CallableCapability> {
    match capability {
        CallableCapability::KnownFn(fid) => fn_map.get(fid).copied().map(CallableCapability::KnownFn),
        CallableCapability::KnownClosure {
            fn_id,
            captures,
            capture_capabilities,
        } => fn_map
            .get(fn_id)
            .copied()
            .map(|fn_id| CallableCapability::KnownClosure {
                fn_id,
                captures: captures.clone(),
                capture_capabilities: capture_capabilities
                    .iter()
                    .map(|capability| {
                        capability
                            .as_ref()
                            .and_then(|capability| remap_callable_capability(capability, fn_map))
                    })
                    .collect(),
            }),
        CallableCapability::OpaqueCallable => Some(CallableCapability::OpaqueCallable),
    }
}

fn remap_callsite(callsite: &CallsiteId, fn_map: &BTreeMap<FnId, FnId>) -> CallsiteId {
    let mut out = callsite.clone();
    if let Some(caller) = fn_map.get(&out.caller) {
        out.caller = *caller;
    }
    out
}

fn remap_call_edge_plan(edge: &CallEdgePlan, fn_map: &BTreeMap<FnId, FnId>) -> CallEdgePlan {
    CallEdgePlan {
        target: match &edge.target {
            CallEdgeTarget::Local(key) => CallEdgeTarget::Local(remap_spec_key(key, fn_map)),
            CallEdgeTarget::External { target, input, demand } => CallEdgeTarget::External {
                target: target.clone(),
                input: input.clone(),
                demand: demand.clone(),
            },
        },
        return_contract: edge
            .return_contract
            .as_ref()
            .map(|contract| remap_return_contract(contract, fn_map)),
    }
}

fn remap_return_contract(contract: &ReturnContract, fn_map: &BTreeMap<FnId, FnId>) -> ReturnContract {
    ReturnContract::new(
        remap_spec_key(&contract.target, fn_map),
        remap_return_strategy(&contract.strategy),
    )
}

fn remap_return_strategy(strategy: &ReturnStrategy) -> ReturnStrategy {
    match strategy {
        ReturnStrategy::Value => ReturnStrategy::Value,
        ReturnStrategy::TupleFields(arity) => ReturnStrategy::TupleFields(*arity),
        ReturnStrategy::ForwardedDemand(demand) => ReturnStrategy::ForwardedDemand(demand.clone()),
    }
}

fn remap_spec_key(key: &SpecKey, fn_map: &BTreeMap<FnId, FnId>) -> SpecKey {
    let mut out = key.clone();
    out.fn_id = remapped_fn_id(out.fn_id, fn_map);
    out
}

fn remap_body_key(key: &BodyKey, fn_map: &BTreeMap<FnId, FnId>) -> BodyKey {
    let mut out = key.clone();
    out.fn_id = remapped_fn_id(out.fn_id, fn_map);
    out
}

fn remapped_fn_id(fid: FnId, fn_map: &BTreeMap<FnId, FnId>) -> FnId {
    fn_map.get(&fid).copied().unwrap_or(fid)
}

fn module_for_linked_fn(module: &Module, fn_id: FnId) -> Option<ModuleName> {
    module
        .fn_idx
        .get(&fn_id)
        .and_then(|idx| module.fns.get(*idx))
        .and_then(|f| {
            if f.owner_module.is_empty() {
                None
            } else {
                ModuleName::parse_dotted(&f.owner_module).ok()
            }
        })
}

fn remap_stmt(stmt: &mut Stmt, fn_map: &BTreeMap<FnId, FnId>, linked_atoms: &mut Vec<String>, unit_atoms: &[String]) {
    let Stmt::Let(_, prim) = stmt;
    remap_prim(prim, fn_map, linked_atoms, unit_atoms);
}

fn remap_prim(prim: &mut Prim, fn_map: &BTreeMap<FnId, FnId>, linked_atoms: &mut Vec<String>, unit_atoms: &[String]) {
    match prim {
        Prim::Const(Const::Atom(id)) => {
            if let Some(name) = unit_atoms.get(*id as usize) {
                let new_id = intern_linked_atom(linked_atoms, name);
                *id = new_id;
            }
        }
        Prim::StructField(_, field) => {
            intern_linked_atom(linked_atoms, field);
        }
        Prim::MakeFnRef(_, fid) | Prim::MakeClosure(_, fid, _) => remap_fn_id(fid, fn_map),
        _ => {}
    }
}

fn remap_fn_externs(f: &mut FnIr, extern_map: &HashMap<ExternId, ExternId>) {
    for block in &mut f.blocks {
        for Stmt::Let(_, prim) in &mut block.stmts {
            if let Prim::Extern(_, id, _) = prim
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
            callee, continuation, ..
        } => {
            remap_fn_id(callee, fn_map);
            remap_cont(continuation, fn_map);
        }
        Term::TailCall { callee, .. } => remap_fn_id(callee, fn_map),
        Term::CallClosure { continuation, .. } => {
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
        Term::Goto(_, _) | Term::If { .. } | Term::TailCallClosure { .. } | Term::Return(_) | Term::Halt(_) => {}
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
    pub module: Option<ModuleName>,
    pub atoms: Vec<String>,
    pub schemas: Vec<Schema>,
    pub frame_sizes: Vec<u32>,
    pub exported_symbols: BTreeMap<String, u32>,
    pub imported_refs: Vec<ExportKey>,
    pub static_closures: Vec<RuntimeStaticClosure>,
    pub halt_kinds: BTreeMap<u32, u32>,
    pub entrypoints: RuntimeEntrypoints,
}

impl RuntimeUnitMetadata {
    #[cfg(test)]
    pub fn from_ir_module(module: Option<ModuleName>, ir: &Module) -> Self {
        Self {
            module,
            atoms: ir.atom_names.clone(),
            schemas: ir.schemas.clone(),
            frame_sizes: Vec::new(),
            exported_symbols: BTreeMap::new(),
            imported_refs: ir.external_call_edges.iter().map(|edge| edge.target.clone()).collect(),
            static_closures: Vec::new(),
            halt_kinds: BTreeMap::new(),
            entrypoints: RuntimeEntrypoints::default(),
        }
    }

    pub fn from_compiled_module(module: Option<ModuleName>, unit: &CompiledUnit, compiled: &CompiledModule) -> Self {
        let schemas = {
            let registry = compiled.user_schemas.borrow();
            (0..registry.len()).map(|id| registry.get(id as u32).clone()).collect()
        };
        let exported_symbols = unit
            .interfaces
            .iter()
            .flat_map(|(module, interface)| {
                interface
                    .exports
                    .iter()
                    .map(move |export| (format!("{}.{}/{}", module, export.name, export.arity), export.arity))
            })
            .enumerate()
            .map(|(idx, (name, _arity))| (name, idx as u32))
            .collect();
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
                .map(|(closure_schema_id, fn_id, _, halt_kind)| RuntimeStaticClosure {
                    closure_schema_id: *closure_schema_id,
                    fn_id: *fn_id,
                    halt_kind: *halt_kind,
                })
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
    pub imported_refs: Vec<ExportKey>,
    pub static_closures: Vec<(usize, RuntimeStaticClosure)>,
    pub halt_kinds: BTreeMap<u32, u32>,
    pub entrypoints: RuntimeEntrypoints,
    pub relocations: Vec<RuntimeUnitRelocations>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeMetadataLinkError {
    DuplicateModule(ModuleName),
    DuplicateExport(String),
}

impl fmt::Display for RuntimeMetadataLinkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl Error for RuntimeMetadataLinkError {}

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

        let atom_keys: BTreeSet<String> = units.iter().flat_map(|unit| unit.atoms.iter().cloned()).collect();
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
            let atom_relocs = unit.atoms.iter().map(|atom| atom_ids[atom]).collect::<Vec<_>>();
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
                if exported_symbols.insert(symbol.clone(), frame_base + *fn_id).is_some() {
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
            self.schemas.iter().map(schema_key).collect::<Vec<_>>().join(",")
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
/// host runs a program by spawning it on a `Runtime` (`Runtime::new(module)`
/// then `spawn` + `run_until_idle`); the test-only `run(fn_id)` is a thin
/// one-task wrapper over exactly that.
pub struct CompiledModule {
    pub(super) _module: JITModule,
    /// fz_fn_id -> compiled fn ptr.
    pub(super) fn_ptrs: HashMap<u32, *const u8>,
    /// User-data SchemaRegistry. Shared with every Process built by
    /// `make_process()` through its Heap.
    pub(crate) user_schemas: Rc<RefCell<SchemaRegistry>>,
    /// Per-fn frame size (bytes), indexed by FnId.0. Consumed by
    /// `fz_alloc_frame_dyn` for fns whose id is only known dynamically
    /// (closure invocation).
    pub(crate) frame_sizes: Vec<u32>,
    /// Heap-registered schema ids for the bitstring reader/result tuples.
    /// None means no bitstring prim is present in this module.
    pub(crate) bs_tuple_arity1_schema: Option<u32>,
    pub(crate) bs_tuple_arity3_schema: Option<u32>,
    /// Atom names indexed by id. The compile-time source for this module's
    /// `node` atom table.
    pub(crate) atom_names: Vec<String>,
    /// Node-global state (atom table + frame sizes) shared by every Process
    /// `make_process` builds, by `Rc` clone — so spawning copies a pointer,
    /// not the tables, and runtime-interned atoms are consistent across the
    /// module's processes.
    pub(crate) node: Rc<Node>,
    pub(crate) diagnostics: Diagnostics,
    /// Zero-capture closure-target spec singletons resolved to code
    /// addresses at JIT-finalize time. `make_process` allocates one
    /// 24-byte off-heap closure per entry into `Process.static_closures`.
    /// See docs/cps-in-clif.md §8.2.
    pub(crate) static_closure_targets: Vec<(u32, u32, *const u8, u32 /* halt_kind */)>,
    /// Tail-CC `fz_entry_thunk(self) -> i64` body. A fresh task's `runnable`
    /// is an entry-thunk closure whose code is this address; resumed through
    /// `fz_resume`, it supplies the inner closure's halt-cont and launches it.
    /// `Runtime::spawn`/`spawn_closure` mint thunks pointing here.
    pub(crate) entry_thunk_addr: *const u8,
    /// Tail-CC `fz_main_trampoline(self, cont) -> i64` body. A main-style
    /// entry's synthetic inner closure has this as its code; it reads the raw
    /// `(cont)` main fn pointer from capture[0] and tail-calls `main_fp(cont)`.
    /// `Runtime::spawn` mints main inner closures pointing here.
    pub(crate) main_trampoline_addr: *const u8,
    /// SystemV→Tail-CC shim `fz_drain_dtor_entry(closure, payload_ref) -> i64`.
    /// The scheduler calls this once per entry on
    /// `process.heap.pending_dtors` at task-exit; dispatches the dtor
    /// closure with payload + a fresh Strict halt-cont.
    pub(crate) drain_dtor_entry_addr: *const u8,
    /// Finalized addresses of the four `fz_halt_cont_body_{tagged,i64,f64,atom}`
    /// Tail-CC fns, indexed by repr kind (0=ValueRef, 1=RawInt, 2=RawF64,
    /// 3=RawAtom).
    /// Null slots (unused reprs in this program) are populated lazily by
    /// `fz_get_halt_cont` at first use.
    pub(crate) halt_cont_body_addrs: [*const u8; 4],
    /// Per-FnId halt-cont singleton kind (the entry fn's any-key return
    /// repr). `Runtime::spawn` stamps this kind onto a main-style entry's
    /// synthetic inner closure so `fz_entry_thunk` resolves the matching
    /// halt-cont. Default kind 0 (ValueRef) when absent.
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
    pub fn diagnostics(&self) -> &Diagnostics {
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
        // One construction site for every engine: `Process::from_consts`
        // (SIZE_TABLE[0] starter heap, grows under GC; static-closure and
        // halt-cont singletons seeded from the consts). The JIT path used to
        // hand-roll the heap as a flat 64 KiB buffer, which never crossed the
        // allocation watermark — so `fz run` observed zero allocation-pressure
        // yields where the AOT binary yielded and GC'd, breaking JIT/AOT stats
        // parity. Routing through the shared constructor keeps the heap and
        // field defaults identical; this path adds only the per-module
        // compile-time tables (see docs/cps-in-clif.md §8.2) and the
        // alloc-stats reset the compiled path wants on a fresh process.
        let consts = CompiledModuleConsts {
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
            static_closure_targets: self.static_closure_targets.clone(),
            halt_cont_body_addrs: self.halt_cont_body_addrs,
        };
        let mut p = Process::from_consts(
            Rc::clone(&self.node),
            Rc::clone(&self.user_schemas),
            &consts,
            0,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        );
        p.heap.reset_alloc_stats();
        p
    }

    /// Run one quantum for a Process. Resumes from `process.next_frame`
    /// (which the caller — typically the Runtime in src/exec/runtime.rs — must
    /// have set to a fresh entry frame or the saved continuation from a
    /// prior yield). The caller sets the pinned register to this process (and
    /// `process.ctx` / `heap.owner`); we just trampoline. On halt the trampoline
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

            fn closure_root(ptr: *mut u8) -> AnyValue {
                if ptr.is_null() {
                    AnyValue::null()
                } else if let Some(value) = AnyValue::decode_tagged_heap_bits(ptr as u64) {
                    value
                } else {
                    AnyValue::heap_ptr(ptr, ValueKind::CLOSURE)
                }
            }

            fn closure_bits(value: AnyValue) -> *mut u8 {
                if value.kind() == ValueKind::NULL {
                    null_mut()
                } else {
                    value.heap_addr().expect("scheduler closure root")
                }
            }

            fn push_closure_root(roots: &mut Vec<AnyValue>, ptr: *mut u8) -> Option<usize> {
                if ptr.is_null() {
                    None
                } else {
                    let idx = roots.len();
                    roots.push(closure_root(ptr));
                    Some(idx)
                }
            }

            let mut mailbox_roots: Vec<AnyValueRef> = process.mailbox.iter().copied().collect();

            let parked_clause_start = 0usize;
            let mut roots: Vec<AnyValue> = Vec::new();
            if let Some(park) = process.wait.as_ref() {
                roots.extend(park.clause_bodies.iter().map(|&p| closure_root(p)));
                roots.push(closure_root(park.after_cont));
            }

            // The single `runnable` closure (continuation or entry thunk) is
            // the one re-entry root. A fresh task's entry thunk reaches its
            // inner closure (and its captures) through this root, so no
            // separate pending-entry root is needed.
            let runnable_idx = push_closure_root(&mut roots, process.runnable_ptr());

            let mut null_root = null_mut();
            process
                .heap
                .gc_with_value_and_any_value_ref_roots(&mut null_root, &mut roots, &mut mailbox_roots);

            process.mailbox.clear();
            process.mailbox.extend(mailbox_roots);

            if let Some(park) = process.wait.as_mut() {
                for (i, body) in park.clause_bodies.iter_mut().enumerate() {
                    *body = closure_bits(roots[parked_clause_start + i]);
                }
                let after_idx = parked_clause_start + park.clause_bodies.len();
                park.after_cont = closure_bits(roots[after_idx]);
            }

            if let Some(idx) = runnable_idx {
                process.set_runnable_closure(closure_bits(roots[idx]));
            }

            process.heap.clear_should_gc_flag();
            process.clear_yield_reasons();
        }

        // Selective-receive initial scan. Hit moves the outcome into `runnable` and
        // cancels the after-timer via the scheduler hook; Miss blocks the
        // task; NotApplicable is a no-op.
        match initial_scan(process) {
            ScanOutcome::Hit => {
                // Fall through to the dispatch branch below.
            }
            ScanOutcome::Miss => {
                process.next_frame = null_mut();
                return;
            }
            ScanOutcome::NotApplicable => {}
        }
        fn run_scheduler_closure(resume_addr: *const u8, process: &mut Process, closure: *mut u8) {
            let closure = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure as *const u8)
                .expect("scheduler closure ref")
                .raw_word();
            let process_ptr = process as *mut Process;
            let _ = unsafe { call1(resume_addr, process_ptr, closure) };
        }

        // One re-entry verb. `runnable` is the only thing the scheduler
        // dispatches: a continuation (receive hit / after-timer fire /
        // mid-flight yield / initial-scan above) or a fresh-task entry thunk
        // (`Runtime::spawn`/`spawn_closure`). Both are `(self)`-callable
        // closures resumed through the single `fz_resume` shim — every fn is
        // Tail-CC, so no per-program trampoline loop is needed. A `None`
        // runnable is the no-work fallthrough.
        if let Some(closure) = process.take_runnable_closure() {
            run_scheduler_closure(self.resume_addr, process, closure);
            process.next_frame = null_mut();
            park_time_gc(process);
        } else {
            process.next_frame = null_mut();
        }
    }
}

#[cfg(test)]
impl CompiledModule {
    /// Registered zero-capture closure-target specs.
    pub fn static_closure_targets(&self) -> &[(u32, u32, *const u8, u32)] {
        &self.static_closure_targets
    }

    /// Run `fn_id` as the root task through the production scheduler and
    /// return that root task's halt value, even if the program spawns
    /// additional tasks. Tests that need the full exit stream attach their own
    /// telemetry capture and read `fz.runtime.process_exited` directly.
    pub fn run(&self, fn_id: FnId) -> i64 {
        // Observe the root task through the telemetry seam rather than reading
        // Runtime internals directly.
        let tel = ConfiguredTelemetry::new();
        let exits = ProcessExitCapture::new();
        tel.attach(&[], exits.handler());
        let mut rt = Runtime::new(self, 1).with_telemetry(&tel);
        let root_pid = rt.spawn(fn_id);
        rt.run_until_idle();
        exits.by_pid(root_pid).expect("root process_exited captured").halt_value
    }
}

#[cfg(test)]
impl CompiledImage {
    pub fn run(&self, fn_id: FnId) -> i64 {
        self.inner.run(fn_id)
    }
}

/// Everything planned codegen collects during the shared pipeline,
/// handed to the backend's `emit_metadata_carriers` and `finalize`.
///
/// The fz user `Module` (post type-rewrite) is intentionally NOT here —
/// backends only need the codegen metadata at finalize time. They've
/// already seen the module while declaring fns and compiling bodies.
pub struct CompiledMetadata {
    pub fn_ids: HashMap<u32, FuncId>,
    pub user_schemas: Rc<RefCell<SchemaRegistry>>,
    pub frame_sizes: Vec<u32>,
    pub atom_names: Vec<String>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    /// Sorted list of tuple arities the program will allocate. JIT ignores
    /// it (its runtime shares `user_schemas`); AOT bakes it into a `.data`
    /// symbol so `fz_aot_setup` re-registers the same `Tuple{N}` schemas in
    /// matching order.
    pub tuple_arities: Vec<u32>,
    /// Named source `defstruct` schemas in registration order. AOT bakes
    /// this into a data table so schema ids match the ids iconst'd into CLIF.
    pub named_schemas: Vec<(String, Vec<String>)>,
    pub diagnostics: Diagnostics,
    /// FnId of fz user `main`, if present. AOT needs it to wire the C
    /// `main` shim; JIT keeps it as a convenience for the run path.
    pub main_fn_id: Option<FnId>,
    /// Zero-capture closure-target specs as `(cl_sid, fn_id, stub_func_id,
    /// halt_kind)`. JIT finalize resolves stub_func_id to a code address;
    /// `make_process` populates `Process.static_closures` from the result.
    pub static_closure_targets: Vec<(u32, u32, FuncId, u32 /* halt_kind */)>,
    pub entry_thunk_id: FuncId,
    pub main_trampoline_id: FuncId,
    pub drain_dtor_entry_id: FuncId,
    /// Four `fz_halt_cont_body` fns indexed by repr kind (0=ValueRef,
    /// 1=RawInt, 2=RawF64, 3=RawAtom). Sigs:
    /// (ValueRef|i64|f64|atom-id, i64) -> i64 tail.
    /// Bodies call the matching `halt_implicit_*` and return 0.
    pub halt_cont_body_ids: [FuncId; 4],
    /// Per-FnId halt-cont singleton kind (the entry fn's any-key return
    /// repr). The Rust scheduler picks the matching halt_cont_singletons
    /// slot when dispatching via `fz_main_entry`.
    pub fn_halt_kinds: HashMap<u32, u32>,
    /// See `CompiledModule::resume_addr`.
    pub resume_id: FuncId,
}
