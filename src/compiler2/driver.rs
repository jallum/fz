use crate::telemetry::{Telemetry, TelemetryExt};
use crate::{measurements, metadata};

use super::code::CodeId;
use super::world::World;

/// Public front door for the side-by-side incremental compiler.
///
/// The scaffold ticket keeps this intentionally narrow: code can enter the
/// Compiler2 world, receive stable identity, and emit Compiler2-local
/// telemetry without invoking the production compiler pipeline.
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

impl Compiler2 {
    pub fn new() -> Self {
        Self
    }

    pub fn submit_code(&mut self, world: &mut World, submission: CodeSubmission, tel: &dyn Telemetry) -> Submission {
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
        Submission { code_id }
    }
}
