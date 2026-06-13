//! Unified fixtures2 frontmatter.
//!
//! A fixtures2 source file may open with a comment-delimited block:
//!
//! ```text
//! #---
//! # purpose: closure call stays indirect
//! # paths: [jit, interp, aot, repl]
//! # root: main/0
//! # assert.metric.semantic.callsites: 2
//! # assert.edge: main/0[] | @66-71 | closure | main/0::lambda[@14-33]/1
//! # snapshot.call_edges: call_edges
//! #---
//! ```
//!
//! The language parser ignores the block as ordinary comments. Fixtures2
//! harnesses read it directly from raw source so one file remains the authority
//! for behavioural matrix metadata and compiler-shape contracts.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FixtureMetadata {
    pub purpose: Option<String>,
    pub matrix: FixtureMatrixMetadata,
    pub compiler: FixtureCompilerMetadata,
}

impl FixtureMetadata {
    pub fn participates_in_matrix(&self) -> bool {
        self.matrix.paths.is_some()
            || self.matrix.kind.is_some()
            || self.matrix.expect.is_some()
            || self.matrix.diagnostic_code.is_some()
            || self.matrix.defer.is_some()
            || self.matrix.oracle.is_some()
            || !self.matrix.budget_assertions.is_empty()
            || !self.matrix.path_timeouts.is_empty()
    }

    pub fn participates_in_compiler_contracts(&self) -> bool {
        self.compiler.root.is_some()
            || !self.compiler.metric_assertions.is_empty()
            || !self.compiler.edge_assertions.is_empty()
            || self.compiler.call_edge_snapshot.is_some()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FixtureMatrixMetadata {
    pub paths: Option<Vec<String>>,
    pub kind: Option<FixtureKind>,
    pub expect: Option<FixtureExpect>,
    pub diagnostic_code: Option<String>,
    pub defer: Option<String>,
    pub oracle: Option<String>,
    pub budget_assertions: Vec<BudgetAssertion>,
    pub path_timeouts: Vec<PathTimeout>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixtureKind {
    Run,
    Test,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixtureExpect {
    Success,
    Abort,
    Diagnostic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BudgetAssertion {
    pub name: String,
    pub expected: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathTimeout {
    pub path: String,
    pub seconds: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FixtureCompilerMetadata {
    pub root: Option<FixtureRoot>,
    pub metric_assertions: Vec<MetricAssertion>,
    pub edge_assertions: Vec<EdgeAssertion>,
    pub call_edge_snapshot: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixtureRoot {
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetricAssertion {
    pub name: String,
    pub expected: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EdgeAssertion {
    pub caller: String,
    pub callsite: String,
    pub dispatch: String,
    pub target: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixtureMetadataError {
    line: usize,
    message: String,
}

impl FixtureMetadataError {
    fn new(line: usize, message: impl Into<String>) -> Self {
        Self {
            line,
            message: message.into(),
        }
    }
}

impl fmt::Display for FixtureMetadataError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fixture metadata line {}: {}", self.line, self.message)
    }
}

pub fn parse_fixture_metadata(source: &str) -> Result<Option<FixtureMetadata>, FixtureMetadataError> {
    let mut lines = source.lines().enumerate();
    let Some((first_line_idx, first_line)) = lines.next() else {
        return Ok(None);
    };
    if first_line.trim() != "#---" {
        return Ok(None);
    }

    let mut metadata = FixtureMetadata::default();
    let mut closed = false;
    for (line_idx, raw_line) in lines {
        let line_no = line_idx + 1;
        if raw_line.trim() == "#---" {
            closed = true;
            break;
        }
        let Some(comment) = raw_line.strip_prefix('#') else {
            return Err(FixtureMetadataError::new(
                line_no,
                "frontmatter lines must start with `#` comment syntax",
            ));
        };
        let line = comment.trim_start();
        if line.is_empty() {
            continue;
        }
        let Some((raw_key, raw_value)) = line.split_once(':') else {
            return Err(FixtureMetadataError::new(
                line_no,
                "expected `key: value` inside fixtures2 frontmatter",
            ));
        };
        let key = raw_key.trim();
        let value = raw_value.trim();
        if value.is_empty() {
            return Err(FixtureMetadataError::new(line_no, format!("`{key}` requires a value")));
        }
        match key {
            "purpose" => set_singleton(&mut metadata.purpose, unquote(value).to_string(), line_no, key)?,
            "paths" => {
                set_singleton(
                    &mut metadata.matrix.paths,
                    parse_flow_seq(value, line_no)?,
                    line_no,
                    key,
                )?;
            }
            "kind" => {
                set_singleton(
                    &mut metadata.matrix.kind,
                    parse_kind(unquote(value), line_no)?,
                    line_no,
                    key,
                )?;
            }
            "expect" => {
                set_singleton(
                    &mut metadata.matrix.expect,
                    parse_expect(unquote(value), line_no)?,
                    line_no,
                    key,
                )?;
            }
            "diagnostic.code" => {
                set_singleton(
                    &mut metadata.matrix.diagnostic_code,
                    unquote(value).to_string(),
                    line_no,
                    key,
                )?;
            }
            "defer" => set_singleton(&mut metadata.matrix.defer, unquote(value).to_string(), line_no, key)?,
            "oracle" => set_singleton(&mut metadata.matrix.oracle, unquote(value).to_string(), line_no, key)?,
            "root" => set_singleton(&mut metadata.compiler.root, parse_root(value, line_no)?, line_no, key)?,
            "assert.edge" => metadata
                .compiler
                .edge_assertions
                .push(parse_edge_assertion(value, line_no)?),
            "snapshot.call_edges" => {
                set_singleton(
                    &mut metadata.compiler.call_edge_snapshot,
                    unquote(value).to_string(),
                    line_no,
                    key,
                )?;
            }
            _ if key.starts_with("assert.metric.") => metadata.compiler.metric_assertions.push(MetricAssertion {
                name: key["assert.metric.".len()..].to_string(),
                expected: parse_u64(value, line_no, key)?,
            }),
            _ if key.starts_with("budget.") => metadata.matrix.budget_assertions.push(BudgetAssertion {
                name: key.to_string(),
                expected: parse_u64(value, line_no, key)?,
            }),
            _ if key.starts_with("timeout.") => metadata.matrix.path_timeouts.push(parse_timeout(value, line_no, key)?),
            _ => {
                return Err(FixtureMetadataError::new(
                    line_no,
                    format!("unknown fixtures2 frontmatter key `{key}`"),
                ));
            }
        }
    }

    if !closed {
        return Err(FixtureMetadataError::new(
            first_line_idx + 1,
            "fixtures2 frontmatter block is missing its closing `#---`",
        ));
    }

    Ok(Some(metadata))
}

#[cfg(test)]
pub fn fixture_frontmatter_prefix_bytes(source: &str) -> Result<Option<u32>, FixtureMetadataError> {
    if !source.starts_with("#---") {
        return Ok(None);
    }
    let mut consumed = 0usize;
    for (line_idx, line) in source.split_inclusive('\n').enumerate() {
        consumed += line.len();
        if line.trim() == "#---" && line_idx > 0 {
            return Ok(Some(consumed as u32));
        }
    }
    Err(FixtureMetadataError::new(
        1,
        "fixtures2 frontmatter block is missing its closing `#---`",
    ))
}

fn set_singleton<T>(slot: &mut Option<T>, value: T, line_no: usize, key: &str) -> Result<(), FixtureMetadataError> {
    if slot.is_some() {
        return Err(FixtureMetadataError::new(
            line_no,
            format!("`{key}` may only appear once"),
        ));
    }
    *slot = Some(value);
    Ok(())
}

fn parse_flow_seq(value: &str, line_no: usize) -> Result<Vec<String>, FixtureMetadataError> {
    let inner = value
        .trim()
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .ok_or_else(|| FixtureMetadataError::new(line_no, format!("`paths` expects `[...]`, got `{value}`")))?;
    Ok(inner
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(|part| unquote(part).to_string())
        .collect())
}

fn unquote(value: &str) -> &str {
    let value = value.trim();
    if value.len() >= 2 && value.starts_with('"') && value.ends_with('"') {
        &value[1..value.len() - 1]
    } else {
        value
    }
}

fn parse_kind(value: &str, line_no: usize) -> Result<FixtureKind, FixtureMetadataError> {
    match value {
        "run" => Ok(FixtureKind::Run),
        "test" => Ok(FixtureKind::Test),
        _ => Err(FixtureMetadataError::new(
            line_no,
            format!("`kind` expects `run` or `test`, got `{value}`"),
        )),
    }
}

fn parse_expect(value: &str, line_no: usize) -> Result<FixtureExpect, FixtureMetadataError> {
    match value {
        "success" => Ok(FixtureExpect::Success),
        "abort" => Ok(FixtureExpect::Abort),
        "diagnostic" => Ok(FixtureExpect::Diagnostic),
        _ => Err(FixtureMetadataError::new(
            line_no,
            format!("`expect` expects `success`, `abort`, or `diagnostic`, got `{value}`"),
        )),
    }
}

fn parse_timeout(value: &str, line_no: usize, key: &str) -> Result<PathTimeout, FixtureMetadataError> {
    let path = key
        .strip_prefix("timeout.")
        .and_then(|suffix| suffix.strip_suffix("_secs"))
        .ok_or_else(|| {
            FixtureMetadataError::new(
                line_no,
                format!("timeout key must look like `timeout.<path>_secs`, got `{key}`"),
            )
        })?;
    Ok(PathTimeout {
        path: path.to_string(),
        seconds: parse_u64(value, line_no, key)?,
    })
}

fn parse_root(value: &str, line_no: usize) -> Result<FixtureRoot, FixtureMetadataError> {
    let Some((name, raw_arity)) = value.split_once('/') else {
        return Err(FixtureMetadataError::new(line_no, "root must look like `name/arity`"));
    };
    if name.trim().is_empty() {
        return Err(FixtureMetadataError::new(line_no, "root name may not be empty"));
    }
    Ok(FixtureRoot {
        name: name.trim().to_string(),
        arity: parse_usize(raw_arity.trim(), line_no, "root")?,
    })
}

fn parse_edge_assertion(value: &str, line_no: usize) -> Result<EdgeAssertion, FixtureMetadataError> {
    let parts = value.split('|').map(str::trim).collect::<Vec<_>>();
    if parts.len() != 4 || parts.iter().any(|part| part.is_empty()) {
        return Err(FixtureMetadataError::new(
            line_no,
            "edge assertion must look like `caller | callsite | dispatch | target`",
        ));
    }
    Ok(EdgeAssertion {
        caller: parts[0].to_string(),
        callsite: parts[1].to_string(),
        dispatch: parts[2].to_string(),
        target: parts[3].to_string(),
    })
}

fn parse_u64(value: &str, line_no: usize, key: &str) -> Result<u64, FixtureMetadataError> {
    value
        .parse::<u64>()
        .map_err(|_| FixtureMetadataError::new(line_no, format!("`{key}` expects an unsigned integer, got `{value}`")))
}

fn parse_usize(value: &str, line_no: usize, key: &str) -> Result<usize, FixtureMetadataError> {
    value
        .parse::<usize>()
        .map_err(|_| FixtureMetadataError::new(line_no, format!("`{key}` expects an unsigned integer, got `{value}`")))
}
