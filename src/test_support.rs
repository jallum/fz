//! Shared test helpers. Cuts the lex→parse→type boilerplate that nearly
//! every cross-module test repeats.

#![cfg(test)]

use crate::ast::Program;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::typer::Typer;

/// Lex, parse, and type a source string. Panics on any failure — these are
/// tests, malformed fixtures should fail loudly.
pub fn typed_program(src: &str) -> (Program, Typer) {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    let mut typer = Typer::new();
    typer.type_program(&prog);
    assert!(typer.errors.is_empty(), "type errors: {:?}", typer.errors);
    (prog, typer)
}

/// Per-test temp directory under the system temp root. Caller cleans up
/// nothing — we leak (it's tmpdir, OS will reclaim).
pub fn temp_dir(test_name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("fz-test-{}-{}", test_name, std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Write source to a file inside a fresh temp dir and return (src_path, dir).
pub fn write_fixture(test_name: &str, file_name: &str, src: &str) -> (std::path::PathBuf, std::path::PathBuf) {
    let dir = temp_dir(test_name);
    let path = dir.join(file_name);
    std::fs::write(&path, src).unwrap();
    (path, dir)
}
