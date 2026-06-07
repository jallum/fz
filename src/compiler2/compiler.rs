use crate::telemetry::Telemetry;

use super::ExecutableNeed;
use super::Job;
use super::code::CodeId;
use super::identity::RootId;
use super::scheduler::DriveOutcome;
use super::world::World;

/// Public front door for the side-by-side incremental compiler.
///
/// Code enters Compiler2 as compiler-owned source text, receives stable
/// identity immediately, and can then seed root-scoped semantic work without
/// invoking the legacy lowering or planner pipeline.
pub struct Compiler2<'a> {
    world: World<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeSubmission {
    pub name: Option<String>,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootSubmission {
    pub module_name: Option<String>,
    pub name: String,
    pub arity: usize,
    pub need: ExecutableNeed,
}

impl<'a> Compiler2<'a> {
    pub fn new(tel: &'a dyn Telemetry) -> Self {
        Self { world: World::new(tel) }
    }

    pub fn submit_code(&mut self, submission: CodeSubmission) -> CodeId {
        let CodeSubmission { name, text } = submission;
        self.world.submit_code(name, text)
    }

    /// Submits one root request and seeds whatever source-surface work it needs.
    pub fn submit_root(&mut self, submission: RootSubmission) -> RootId {
        let RootSubmission {
            module_name,
            name,
            arity,
            need,
        } = submission;
        self.world.submit_root(module_name, name, arity, need)
    }

    pub fn demand(&mut self, job: Job) -> bool {
        self.world.demand(job)
    }

    pub fn drive(&mut self) -> DriveOutcome<Job, super::FactKey> {
        self.world.drive()
    }
}
