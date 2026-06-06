use std::fmt;

use super::driver::CodeSubmission;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CodeId(u32);

impl CodeId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

impl fmt::Display for CodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "code#{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeRecord {
    name: Option<String>,
    text: String,
}

impl CodeRecord {
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn text(&self) -> &str {
        &self.text
    }
}

#[derive(Debug, Default)]
pub struct World {
    code: Vec<CodeRecord>,
}

impl World {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert_code(&mut self, submission: CodeSubmission) -> CodeId {
        let code_id = CodeId(self.code.len() as u32);
        self.code.push(CodeRecord {
            name: submission.name,
            text: submission.text,
        });
        code_id
    }

    pub fn code(&self, code_id: CodeId) -> Option<&CodeRecord> {
        self.code.get(code_id.0 as usize)
    }

    pub fn code_count(&self) -> usize {
        self.code.len()
    }
}
