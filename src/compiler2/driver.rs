use crate::telemetry::Telemetry;

use super::Job;
use super::code::CodeId;
use super::scheduler::DriveError;
use super::world::World;

/// Public front door for the side-by-side incremental compiler.
///
/// Code enters Compiler2 as compiler-owned source text, receives stable
/// identity immediately, and is indexed into owned expanded definitions without
/// invoking lowering or planning.
pub struct Compiler2<'a> {
    world: World<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeSubmission {
    pub name: Option<String>,
    pub text: String,
}

impl<'a> Compiler2<'a> {
    pub fn new(tel: &'a dyn Telemetry) -> Self {
        Self { world: World::new(tel) }
    }

    pub fn submit_code(&mut self, submission: CodeSubmission) -> CodeId {
        let CodeSubmission { name, text } = submission;
        self.world.submit_code(name, text)
    }

    pub fn demand(&mut self, job: Job) -> bool {
        self.world.demand(job)
    }

    pub fn drive(&mut self) -> Result<(), DriveError<Job>> {
        self.world.drive().map(|_| ())
    }
}
