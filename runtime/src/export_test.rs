//! Every C-ABI function this crate exports must be `#[unsafe(no_mangle)]`.
//!
//! The AOT door links this crate as a staticlib and defers unresolved symbols
//! to load time (`-Wl,-undefined,dynamic_lookup`, `src/aot_link.rs`). So a
//! function that loses the attribute still compiles, still links, and fails
//! only when a program that reaches it actually RUNS -- as `dyld: symbol not
//! found in flat namespace`, naming a symbol that is right there in the source.
//!
//! That is exactly how it broke: an edit anchored on the `pub extern` line
//! landed between an attribute and its function, silently moving the export
//! onto a private helper. Six fixtures went red on one door only.
//!
//! The check reads every source file in the crate, not one, and accepts both
//! spellings -- `pub unsafe extern "C"` is the majority form outside
//! `ir_runtime.rs`, and a check that only knew the other one would have
//! covered the minority.

use std::fs;
use std::path::{Path, PathBuf};

fn crate_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).expect("runtime sources are readable") {
        let path = entry.expect("readable dir entry").path();
        if path.is_dir() {
            crate_sources(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// True when an exported item's preceding attributes carry `no_mangle`.
///
/// Walks back over doc comments, other attributes (including multi-line ones)
/// and blank lines, so attribute ORDER and formatting do not decide the answer.
fn is_exported(lines: &[&str], item: usize) -> bool {
    lines[..item]
        .iter()
        .rev()
        .take_while(|line| {
            let line = line.trim();
            line.starts_with("//") || line.starts_with('#') || line.starts_with(')') || line.is_empty() || {
                // a continuation line of a multi-line attribute
                !line.ends_with(';') && !line.ends_with('}') && !line.ends_with('{')
            }
        })
        .any(|line| line.contains("no_mangle"))
}

#[test]
fn every_exported_c_function_is_no_mangle() {
    let mut sources = Vec::new();
    crate_sources(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("src").as_path(),
        &mut sources,
    );
    assert!(
        sources.len() > 5,
        "expected to find the crate's sources, got {sources:?}"
    );

    let mut unexported: Vec<String> = Vec::new();
    for path in &sources {
        let source = fs::read_to_string(path).expect("source is readable");
        let lines: Vec<&str> = source.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            let trimmed = line.trim_start();
            let exports_c_abi =
                trimmed.starts_with("pub extern \"C\" fn ") || trimmed.starts_with("pub unsafe extern \"C\" fn ");
            if exports_c_abi && !is_exported(&lines, index) {
                let name = path.file_name().expect("named file").to_string_lossy();
                unexported.push(format!("{name}:{}: {trimmed}", index + 1));
            }
        }
    }

    assert!(
        unexported.is_empty(),
        "these are exported to the AOT link but would be name-mangled, so a program reaching \
         them dies at load time rather than at build:\n{}",
        unexported.join("\n"),
    );
}
