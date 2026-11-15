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
        name: "Collectable",
        source: include_str!("../../lib/collectable.fz"),
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
        name: "System",
        source: include_str!("../../lib/system.fz"),
    },
    RuntimeModuleSource {
        name: "File",
        source: include_str!("../../lib/file.fz"),
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
        name: "MapSet",
        source: include_str!("../../lib/map_set.fz"),
    },
    RuntimeModuleSource {
        name: "Tuple",
        source: include_str!("../../lib/tuple.fz"),
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
        name: "Exception",
        source: include_str!("../../lib/exception.fz"),
    },
    RuntimeModuleSource {
        name: "ArgumentError",
        source: include_str!("../../lib/exceptions/argument_error.fz"),
    },
    RuntimeModuleSource {
        name: "ArithmeticError",
        source: include_str!("../../lib/exceptions/arithmetic_error.fz"),
    },
    RuntimeModuleSource {
        name: "BadBooleanError",
        source: include_str!("../../lib/exceptions/bad_boolean_error.fz"),
    },
    RuntimeModuleSource {
        name: "BadMapError",
        source: include_str!("../../lib/exceptions/bad_map_error.fz"),
    },
    RuntimeModuleSource {
        name: "CaseClauseError",
        source: include_str!("../../lib/exceptions/case_clause_error.fz"),
    },
    RuntimeModuleSource {
        name: "CondClauseError",
        source: include_str!("../../lib/exceptions/cond_clause_error.fz"),
    },
    RuntimeModuleSource {
        name: "Enum.EmptyError",
        source: include_str!("../../lib/exceptions/enum_empty_error.fz"),
    },
    RuntimeModuleSource {
        name: "Enum.OutOfBoundsError",
        source: include_str!("../../lib/exceptions/enum_out_of_bounds_error.fz"),
    },
    RuntimeModuleSource {
        name: "ErlangError",
        source: include_str!("../../lib/exceptions/erlang_error.fz"),
    },
    RuntimeModuleSource {
        name: "File.CopyError",
        source: include_str!("../../lib/exceptions/file_copy_error.fz"),
    },
    RuntimeModuleSource {
        name: "File.Error",
        source: include_str!("../../lib/exceptions/file_error.fz"),
    },
    RuntimeModuleSource {
        name: "File.LinkError",
        source: include_str!("../../lib/exceptions/file_link_error.fz"),
    },
    RuntimeModuleSource {
        name: "File.RenameError",
        source: include_str!("../../lib/exceptions/file_rename_error.fz"),
    },
    RuntimeModuleSource {
        name: "FunctionClauseError",
        source: include_str!("../../lib/exceptions/function_clause_error.fz"),
    },
    RuntimeModuleSource {
        name: "JSON.DecodeError",
        source: include_str!("../../lib/exceptions/json_decode_error.fz"),
    },
    RuntimeModuleSource {
        name: "KeyError",
        source: include_str!("../../lib/exceptions/key_error.fz"),
    },
    RuntimeModuleSource {
        name: "MatchError",
        source: include_str!("../../lib/exceptions/match_error.fz"),
    },
    RuntimeModuleSource {
        name: "Protocol.UndefinedError",
        source: include_str!("../../lib/exceptions/protocol_undefined_error.fz"),
    },
    RuntimeModuleSource {
        name: "RuntimeError",
        source: include_str!("../../lib/exceptions/runtime_error.fz"),
    },
    RuntimeModuleSource {
        name: "TryClauseError",
        source: include_str!("../../lib/exceptions/try_clause_error.fz"),
    },
    RuntimeModuleSource {
        name: "UndefinedFunctionError",
        source: include_str!("../../lib/exceptions/undefined_function_error.fz"),
    },
    RuntimeModuleSource {
        name: "WithClauseError",
        source: include_str!("../../lib/exceptions/with_clause_error.fz"),
    },
    RuntimeModuleSource {
        name: "Float",
        source: include_str!("../../lib/float.fz"),
    },
    RuntimeModuleSource {
        name: "String.Chars",
        source: include_str!("../../lib/string_chars.fz"),
    },
    RuntimeModuleSource {
        name: "IO",
        source: include_str!("../../lib/io.fz"),
    },
    RuntimeModuleSource {
        name: "Stream",
        source: include_str!("../../lib/stream.fz"),
    },
    RuntimeModuleSource {
        name: "File.Stream",
        source: include_str!("../../lib/file_stream.fz"),
    },
    RuntimeModuleSource {
        name: "JSON",
        source: include_str!("../../lib/json.fz"),
    },
    RuntimeModuleSource {
        name: "Macro",
        source: include_str!("../../lib/macro.fz"),
    },
    RuntimeModuleSource {
        name: "OptionParser",
        source: include_str!("../../lib/option_parser.fz"),
    },
    RuntimeModuleSource {
        name: ":erlang",
        source: include_str!("../../lib/erlang.fz"),
    },
    RuntimeModuleSource {
        name: ":binary",
        source: include_str!("../../lib/binary.fz"),
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
