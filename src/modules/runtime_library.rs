//! Built-in runtime library modules as separate-compilation inputs.
//!
//! The sources themselves are fz, and live in `lib/` at the repository root
//! rather than under `src/`. This is the Rust that embeds them, and so it is
//! where they are named and ordered.
//!
//! Compiler2 consumes these sources through its quoted front door, the same
//! path as user modules. This module intentionally exposes source text only;
//! the retired AST parser no longer builds runtime `Program` values here.

const RUNTIME_PRELUDE_FZ: &str = include_str!("../../lib/runtime.fz");

struct RuntimeModuleSource {
    name: &'static str,
    source: &'static str,
}

const RUNTIME_MODULE_SOURCES: &[RuntimeModuleSource] = &[
    RuntimeModuleSource {
        name: "Kernel",
        source: include_str!("../../lib/kernel.fz"),
    },
    RuntimeModuleSource {
        name: "Enumerable",
        source: include_str!("../../lib/enumerable.fz"),
    },
    RuntimeModuleSource {
        name: "Range",
        source: include_str!("../../lib/range.fz"),
    },
    RuntimeModuleSource {
        name: "Process",
        source: include_str!("../../lib/process.fz"),
    },
    RuntimeModuleSource {
        name: "List",
        source: include_str!("../../lib/list.fz"),
    },
    RuntimeModuleSource {
        name: "Map",
        source: include_str!("../../lib/map.fz"),
    },
    RuntimeModuleSource {
        name: "Keyword",
        source: include_str!("../../lib/keyword.fz"),
    },
    RuntimeModuleSource {
        name: "String",
        source: include_str!("../../lib/string.fz"),
    },
    RuntimeModuleSource {
        name: "Enum",
        source: include_str!("../../lib/enum.fz"),
    },
    RuntimeModuleSource {
        name: "Atom",
        source: include_str!("../../lib/atom.fz"),
    },
    RuntimeModuleSource {
        name: "Integer",
        source: include_str!("../../lib/integer.fz"),
    },
    RuntimeModuleSource {
        name: "Float",
        source: include_str!("../../lib/float.fz"),
    },
    RuntimeModuleSource {
        name: "StringChars",
        source: include_str!("../../lib/string_chars.fz"),
    },
    RuntimeModuleSource {
        name: "Json",
        source: include_str!("../../lib/json.fz"),
    },
    RuntimeModuleSource {
        name: "Utf8",
        source: include_str!("../../lib/utf8.fz"),
    },
];

pub fn prelude_source() -> &'static str {
    RUNTIME_PRELUDE_FZ
}

pub(crate) fn module_sources() -> impl Iterator<Item = (&'static str, &'static str)> {
    RUNTIME_MODULE_SOURCES.iter().map(|source| (source.name, source.source))
}

#[cfg(test)]
mod tests {
    #[test]
    fn enum_if_decisions_are_single_non_nested_value_choices() {
        let mut inside_doc = false;

        for (line_index, line) in include_str!("../../lib/enum.fz").lines().enumerate() {
            let doc_delimiter_count = line.match_indices("\"\"\"").count();
            if doc_delimiter_count > 0 {
                if doc_delimiter_count % 2 == 1 {
                    inside_doc = !inside_doc;
                }
                continue;
            }
            if inside_doc || line.trim_start().starts_with('#') {
                continue;
            }

            let if_count = line.match_indices("if ").count();
            if if_count == 0 {
                continue;
            }

            assert_eq!(
                if_count,
                1,
                "Enum decision nests `if` expressions on source line {}: {line}",
                line_index + 1,
            );
            assert!(
                line.contains("do:") && line.contains("else:"),
                "Enum decision is not a one-line value choice on source line {}: {line}",
                line_index + 1,
            );
        }
    }
}
