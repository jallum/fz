use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;

use crate::ast::{FnDef, Item, Program};
use crate::compiler::source::Id as SourceId;
use crate::diag::Diagnostic;
use crate::frontend::{macros, resolve};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::value::opaque;
use crate::telemetry::{Telemetry, TelemetryExt};
use crate::{measurements, metadata};

use super::code::CodeId;
use super::deps::ExactPattern;
use super::facts::{FactAggregator, Fingerprint};
use super::identity::{FunctionDef, FunctionId, ModuleId};
use super::namespace::{NamespaceHead, NamespaceStore, NamespaceSymbol};
use super::scheduler::{DriveDone, DriveResult, JobOutcome, Scheduler, StepResult};
use super::world::World;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum JobKey {
    IndexCode(CodeId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactKey {
    CodeIndexed(CodeId),
    ModuleDefined(ModuleId),
    FunctionDefined(FunctionId),
    LoweredBody(FunctionId),
    Activation(FunctionId),
    Executable(FunctionId),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct LatestRevision;

impl<J, F> FactAggregator<J, F, u64> for LatestRevision
where
    J: Eq + Hash,
{
    fn aggregate(&self, _key: &F, contributions: &std::collections::HashMap<J, u64>) -> Option<u64> {
        contributions.values().copied().max()
    }

    fn fingerprint(&self, _key: &F, aggregate: &u64) -> Fingerprint {
        Fingerprint::new(*aggregate)
    }
}

pub type Compiler2Scheduler = Scheduler<JobKey, FactKey, ExactPattern<FactKey>, u64, LatestRevision>;

#[derive(Debug, Clone)]
struct PendingFunction {
    id: FunctionId,
    module: Option<ModuleId>,
    ast: FnDef,
}

impl World {
    pub fn enqueue(&mut self, job: JobKey) -> bool {
        self.scheduler_mut().enqueue(job)
    }

    pub fn drive(&mut self, tel: &dyn Telemetry) -> DriveResult<JobKey> {
        let mut processed_jobs = 0;
        while let Some(job) = self.scheduler_mut().pop() {
            processed_jobs += 1;
            let outcome = self.run_job(&job, tel);
            match self.scheduler_mut().complete(job.clone(), outcome, tel) {
                StepResult::Applied { .. } => {}
                StepResult::Fatal { .. } => return DriveResult::Fatal { job },
            }
        }
        DriveResult::Done(DriveDone { processed_jobs })
    }

    fn run_job(
        &mut self,
        job: &JobKey,
        tel: &dyn Telemetry,
    ) -> JobOutcome<JobKey, FactKey, ExactPattern<FactKey>, u64> {
        match job {
            JobKey::IndexCode(code_id) => self.index_code(*code_id, tel),
        }
    }

    fn index_code(
        &mut self,
        code_id: CodeId,
        tel: &dyn Telemetry,
    ) -> JobOutcome<JobKey, FactKey, ExactPattern<FactKey>, u64> {
        let source_name = self
            .code()
            .name(code_id)
            .map(str::to_owned)
            .unwrap_or_else(|| format!("<code:{}>", code_id.as_u32()));
        let Some(source_text) = self.code().text(code_id).map(str::to_owned) else {
            return fatal_outcome(Diagnostic::error(
                crate::diag::codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                format!("compiler2 missing code text for code {}", code_id.as_u32()),
                crate::compiler::source::Span::DUMMY,
            ));
        };

        let _span = tel.span(
            &["fz", "compiler2", "index_code"],
            metadata! {
                code_id: code_id.as_u32() as u64,
                name: source_name.clone(),
            },
        );

        let program = match expanded_program(code_id, &source_name, &source_text, tel) {
            Ok(program) => program,
            Err(diagnostic) => return fatal_outcome(*diagnostic),
        };

        let mut module_names = program
            .module_interfaces
            .keys()
            .map(|name| name.dotted())
            .collect::<BTreeSet<_>>();
        let function_asts = program
            .items
            .iter()
            .filter_map(|item| match &**item {
                Item::Fn(def) => {
                    let (module_name, _) = split_function_name(&def.name);
                    if let Some(module_name) = module_name {
                        module_names.insert(module_name);
                    }
                    Some(def.clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        let mut module_ids = BTreeMap::new();
        for module_name in &module_names {
            let module_id = self.modules_mut().reference_named(module_name.clone());
            module_ids.insert(module_name.clone(), module_id);
        }

        let mut pending = Vec::new();
        let mut top_level_functions = BTreeMap::new();
        let mut top_level_macros = BTreeMap::new();
        let mut module_functions = std::collections::HashMap::new();
        let mut module_macros = std::collections::HashMap::new();

        for ast in function_asts {
            let arity = function_arity(&ast);
            let (module_name, local_name) = split_function_name(&ast.name);
            let module_id = module_name.as_ref().map(|name| module_ids[name]);
            let function_id = self.functions_mut().reference(module_id, local_name.clone(), arity);
            pending.push(PendingFunction {
                id: function_id,
                module: module_id,
                ast: ast.clone(),
            });

            let groups = match (module_id, ast.is_macro) {
                (None, false) => &mut top_level_functions,
                (None, true) => &mut top_level_macros,
                (Some(module_id), false) => module_functions.entry(module_id).or_insert_with(BTreeMap::new),
                (Some(module_id), true) => module_macros.entry(module_id).or_insert_with(BTreeMap::new),
            };
            groups.entry(local_name).or_insert_with(Vec::new).push(function_id);
        }

        let mut modules_head = self.namespaces().prelude_head();
        for (module_name, module_id) in &module_ids {
            modules_head =
                self.namespaces_mut()
                    .bind(modules_head, module_name.clone(), NamespaceSymbol::Module(*module_id));
        }
        let mut root_head = modules_head;
        root_head = bind_grouped(self.namespaces_mut(), root_head, &top_level_functions, false);
        root_head = bind_grouped(self.namespaces_mut(), root_head, &top_level_macros, true);

        let mut module_heads = std::collections::HashMap::new();
        let mut module_list = module_ids.values().copied().collect::<Vec<_>>();
        module_list.sort_by_key(|module_id| module_id.as_u32());
        let mut outputs = Vec::new();
        for module_id in &module_list {
            let mut head = modules_head;
            if let Some(bindings) = module_functions.get(module_id) {
                head = bind_grouped(self.namespaces_mut(), head, bindings, false);
            }
            if let Some(bindings) = module_macros.get(module_id) {
                head = bind_grouped(self.namespaces_mut(), head, bindings, true);
            }
            let revision = self.modules_mut().define(*module_id, code_id, head);
            module_heads.insert(*module_id, head);
            outputs.push((FactKey::ModuleDefined(*module_id), revision));
        }

        let mut function_ids = pending.iter().map(|function| function.id).collect::<Vec<_>>();
        function_ids.sort_by_key(|function_id| function_id.as_u32());
        for pending_fn in pending {
            let namespace = pending_fn
                .module
                .and_then(|module_id| module_heads.get(&module_id).copied())
                .unwrap_or(root_head);
            let revision = self
                .functions_mut()
                .define(pending_fn.id, FunctionDef::new(code_id, namespace, pending_fn.ast));
            outputs.push((FactKey::FunctionDefined(pending_fn.id), revision));
        }

        let code_revision = self
            .code_mut()
            .index(code_id, module_list.clone(), function_ids.clone());
        outputs.push((FactKey::CodeIndexed(code_id), code_revision));

        tel.execute(
            &["fz", "compiler2", "code", "indexed"],
            &measurements! {
                code_id: code_id.as_u32() as u64,
                modules: module_list.len() as u64,
                functions: function_ids.len() as u64,
            },
            &metadata! {
                name: source_name,
                module_ids: opaque(&module_list),
                function_ids: opaque(&function_ids),
            },
        );

        JobOutcome {
            outputs,
            ..JobOutcome::new()
        }
    }
}

fn fatal_outcome(diagnostic: Diagnostic) -> JobOutcome<JobKey, FactKey, ExactPattern<FactKey>, u64> {
    JobOutcome {
        fatal: Some(diagnostic),
        ..JobOutcome::new()
    }
}

fn expanded_program(
    code_id: CodeId,
    source_name: &str,
    source_text: &str,
    tel: &dyn Telemetry,
) -> Result<Program, Box<Diagnostic>> {
    let source_id = SourceId(code_id.as_u32());
    let tokens = Lexer::with_code_id_and_source_name(source_text, source_id, source_name.to_string())
        .tokenize(tel)
        .map_err(|error| Box::new(error.to_diagnostic()))?;
    let program = Parser::new(tokens)
        .parse_program(tel)
        .map_err(|error| Box::new(error.to_diagnostic()))?;

    let mut types = crate::types::new();
    let mut program =
        resolve::flatten_modules_with_interface_table(&mut types, program, resolve::InterfaceTable::new(), tel)
            .map_err(|error| Box::new(error.to_diagnostic()))?;
    macros::expand_program_with_types(&mut types, &mut program).map_err(|error| Box::new(error.to_diagnostic()))?;
    resolve::add_macro_requested_runtime_interfaces(&mut program, tel);
    Ok(program)
}

fn split_function_name(name: &str) -> (Option<String>, String) {
    match name.rsplit_once('.') {
        Some((module, local_name)) => (Some(module.to_string()), local_name.to_string()),
        None => (None, name.to_string()),
    }
}

fn function_arity(def: &FnDef) -> usize {
    if def.extern_abi.is_some() {
        def.extern_params.len()
    } else {
        def.clauses
            .first()
            .map(|clause| clause.params.len())
            .expect("functions should have at least one clause")
    }
}

fn bind_grouped(
    store: &mut NamespaceStore,
    mut head: NamespaceHead,
    bindings: &BTreeMap<String, Vec<FunctionId>>,
    is_macro: bool,
) -> NamespaceHead {
    for (name, ids) in bindings {
        let symbol = if is_macro {
            NamespaceSymbol::Macros(ids.clone())
        } else {
            NamespaceSymbol::Functions(ids.clone())
        };
        head = store.bind(head, name.clone(), symbol);
    }
    head
}
