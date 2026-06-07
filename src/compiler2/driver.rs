use crate::telemetry::{Telemetry, TelemetryExt};
use crate::{measurements, metadata};

use super::code::CodeId;
use super::index::JobKey;
use super::scheduler::DriveResult;
use super::world::World;

/// Public front door for the side-by-side incremental compiler.
///
/// Code enters Compiler2 as compiler-owned source text, receives stable
/// identity immediately, and is indexed into owned expanded definitions without
/// invoking lowering or planning.
#[derive(Default)]
pub struct Compiler2;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeSubmission {
    pub name: Option<String>,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Submission {
    pub code_id: CodeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubmitError {
    pub code_id: CodeId,
}

impl Compiler2 {
    pub fn new() -> Self {
        Self
    }

    pub fn submit_code(
        &mut self,
        world: &mut World,
        submission: CodeSubmission,
        tel: &dyn Telemetry,
    ) -> Result<Submission, SubmitError> {
        let _span = tel.span(
            &["fz", "compiler2", "submit_code"],
            metadata! {
                name: submission.name.as_deref().unwrap_or("<anonymous>"),
            },
        );
        let code_id = world
            .code_mut()
            .define(submission.name.clone(), submission.text.clone());
        tel.execute(
            &["fz", "compiler2", "code", "submitted"],
            &measurements! {
                code_id: code_id.as_u32() as u64,
                bytes: submission.text.len() as u64,
            },
            &metadata! {
                name: submission.name.as_deref().unwrap_or("<anonymous>"),
            },
        );

        world.enqueue(JobKey::IndexCode(code_id));
        match world.drive(tel) {
            DriveResult::Done(_) => Ok(Submission { code_id }),
            DriveResult::Fatal {
                job: JobKey::IndexCode(failed_code_id),
            } => Err(SubmitError {
                code_id: failed_code_id,
            }),
        }
    }
}
