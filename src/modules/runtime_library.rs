//! Built-in runtime library modules as separate-compilation inputs.
//!
//! Compiler2 consumes these sources through its quoted front door, the same
//! path as user modules. This module intentionally exposes source text only;
//! the retired AST parser no longer builds runtime `Program` values here.

const RUNTIME_PRELUDE_FZ: &str = include_str!("runtime_library/runtime.fz");

struct RuntimeModuleSource {
    name: &'static str,
    source: &'static str,
}

const RUNTIME_MODULE_SOURCES: &[RuntimeModuleSource] = &[
    RuntimeModuleSource {
        name: "Kernel",
        source: include_str!("runtime_library/kernel.fz"),
    },
    RuntimeModuleSource {
        name: "Enumerable",
        source: include_str!("runtime_library/enumerable.fz"),
    },
    RuntimeModuleSource {
        name: "Range",
        source: include_str!("runtime_library/range.fz"),
    },
    RuntimeModuleSource {
        name: "Process",
        source: include_str!("runtime_library/process.fz"),
    },
    RuntimeModuleSource {
        name: "List",
        source: include_str!("runtime_library/list.fz"),
    },
    RuntimeModuleSource {
        name: "Map",
        source: include_str!("runtime_library/map.fz"),
    },
    RuntimeModuleSource {
        name: "Enum",
        source: include_str!("runtime_library/enum.fz"),
    },
    RuntimeModuleSource {
        name: "Utf8",
        source: include_str!("runtime_library/utf8.fz"),
    },
];

pub fn prelude_source() -> &'static str {
    RUNTIME_PRELUDE_FZ
}

pub(crate) fn module_sources() -> impl Iterator<Item = (&'static str, &'static str)> {
    RUNTIME_MODULE_SOURCES.iter().map(|source| (source.name, source.source))
}
