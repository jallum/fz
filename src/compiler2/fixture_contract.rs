//! Fixtures2 compiler-contract frontmatter.
//!
//! A fixtures2 source file may open with a comment-delimited block:
//!
//! ```text
//! #---
//! # purpose: closure call stays indirect
//! # root: main/0
//! # assert.metric.codegen.functions: 3
//! # assert.edge: main/0 | @66-71 | closure | main/0::lambda[@14-33]/1
//! # snapshot.call_edges: call_edges
//! #---
//! ```
//!
//! The language parser ignores it as ordinary comments. The compiler-contract
//! harness reads it directly from the raw fixture source so one file remains
//! the authority for both program text and compiler-shape expectations.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FixtureContract {
    pub purpose: Option<String>,
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
pub struct FixtureContractError {
    line: usize,
    message: String,
}

impl FixtureContractError {
    fn new(line: usize, message: impl Into<String>) -> Self {
        Self {
            line,
            message: message.into(),
        }
    }
}

impl fmt::Display for FixtureContractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fixture contract line {}: {}", self.line, self.message)
    }
}

pub fn parse_fixture_contract(source: &str) -> Result<Option<FixtureContract>, FixtureContractError> {
    let mut lines = source.lines().enumerate();
    let Some((first_line_idx, first_line)) = lines.next() else {
        return Ok(None);
    };
    if first_line.trim() != "#---" {
        return Ok(None);
    }

    let mut contract = FixtureContract::default();
    let mut closed = false;
    for (line_idx, raw_line) in lines {
        let line_no = line_idx + 1;
        if raw_line.trim() == "#---" {
            closed = true;
            break;
        }
        let Some(comment) = raw_line.strip_prefix('#') else {
            return Err(FixtureContractError::new(
                line_no,
                "contract lines must start with `#` comment syntax",
            ));
        };
        let line = comment.trim_start();
        if line.is_empty() {
            continue;
        }
        let Some((raw_key, raw_value)) = line.split_once(':') else {
            return Err(FixtureContractError::new(
                line_no,
                "expected `key: value` inside fixture contract",
            ));
        };
        let key = raw_key.trim();
        let value = raw_value.trim();
        if value.is_empty() {
            return Err(FixtureContractError::new(line_no, format!("`{key}` requires a value")));
        }
        match key {
            "purpose" => set_singleton(&mut contract.purpose, value.to_string(), line_no, key)?,
            "root" => set_singleton(&mut contract.root, parse_root(value, line_no)?, line_no, key)?,
            "assert.edge" => contract.edge_assertions.push(parse_edge_assertion(value, line_no)?),
            "snapshot.call_edges" => {
                set_singleton(&mut contract.call_edge_snapshot, value.to_string(), line_no, key)?;
            }
            _ if key.starts_with("assert.metric.") => contract.metric_assertions.push(MetricAssertion {
                name: key["assert.metric.".len()..].to_string(),
                expected: parse_u64(value, line_no, key)?,
            }),
            _ => {
                return Err(FixtureContractError::new(
                    line_no,
                    format!("unknown fixture contract key `{key}`"),
                ));
            }
        }
    }

    if !closed {
        return Err(FixtureContractError::new(
            first_line_idx + 1,
            "fixture contract block is missing its closing `#---`",
        ));
    }

    Ok(Some(contract))
}

#[cfg(test)]
pub fn fixture_contract_prefix_bytes(source: &str) -> Result<Option<u32>, FixtureContractError> {
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
    Err(FixtureContractError::new(
        1,
        "fixture contract block is missing its closing `#---`",
    ))
}

fn set_singleton<T>(slot: &mut Option<T>, value: T, line_no: usize, key: &str) -> Result<(), FixtureContractError> {
    if slot.is_some() {
        return Err(FixtureContractError::new(
            line_no,
            format!("`{key}` may only appear once"),
        ));
    }
    *slot = Some(value);
    Ok(())
}

fn parse_root(value: &str, line_no: usize) -> Result<FixtureRoot, FixtureContractError> {
    let Some((name, raw_arity)) = value.split_once('/') else {
        return Err(FixtureContractError::new(line_no, "root must look like `name/arity`"));
    };
    if name.trim().is_empty() {
        return Err(FixtureContractError::new(line_no, "root name may not be empty"));
    }
    Ok(FixtureRoot {
        name: name.trim().to_string(),
        arity: parse_usize(raw_arity.trim(), line_no, "root")?,
    })
}

fn parse_edge_assertion(value: &str, line_no: usize) -> Result<EdgeAssertion, FixtureContractError> {
    let parts = value.split('|').map(str::trim).collect::<Vec<_>>();
    if parts.len() != 4 || parts.iter().any(|part| part.is_empty()) {
        return Err(FixtureContractError::new(
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

fn parse_u64(value: &str, line_no: usize, key: &str) -> Result<u64, FixtureContractError> {
    value
        .parse::<u64>()
        .map_err(|_| FixtureContractError::new(line_no, format!("`{key}` expects an unsigned integer, got `{value}`")))
}

fn parse_usize(value: &str, line_no: usize, key: &str) -> Result<usize, FixtureContractError> {
    value
        .parse::<usize>()
        .map_err(|_| FixtureContractError::new(line_no, format!("`{key}` expects an unsigned integer, got `{value}`")))
}
