//! `tools/distill-telemetry.exs` reads a `--log-telemetry` JSONL stream and
//! prints, among other sections, a per-kind runs-vs-subjects census and the
//! cause of every wake. Both are pure counts over the stream's own
//! `time_ns`/`elapsed_ns` fields, so a fixed trace produces byte-identical
//! output on every machine and every run, and the whole of stdout is compared.
//!
//! `tests/distill_telemetry/main_returns_one.jsonl` (`def main(), do: 1`) is
//! the smallest program there is: 22 job runs over 20 subjects, 2 re-runs
//! (`ScopeCode`, 4 runs over 2 subjects). The cause table counts every
//! wake that started its job -- 12 of them, none already pending -- and one of those
//! (`ScopeCode` woken by the nested `def/1` macro root's
//! `Product(root_backend_product)` settling) arrives on
//! `work_graph.dependencies_moved`, not `work_graph.applied`, which is why
//! the distiller reads all three step-carrying events. The per-reason
//! `work_starts` counts sum to the 22 job runs. The trace was captured with:
//!
//!     cargo build
//!     target/debug/fz2 --log-telemetry tests/distill_telemetry/main_returns_one.jsonl \
//!         interp tests/distill_telemetry/main_returns_one.fz
//!
//! `main_returns_one.expected.txt` is what real `elixir` prints for that trace;
//! regenerate it with `elixir tools/distill-telemetry.exs
//! tests/distill_telemetry/main_returns_one.jsonl`. `fz2` running the same
//! script through `interp`, `run` and `build` must print it byte for byte.
//!
//! `tests/distill_telemetry/tied_rows.jsonl` (`def main(), do: Map.get(%{a: 1}, :a)`)
//! is a trace in which rows tie on the figure a table sorts by, at the `--top 32`
//! cut. Every table breaks ties by the row's own label, so the rows a cut keeps
//! do not depend on the order a map hands its entries back in, which Elixir
//! leaves unspecified and fz does not reproduce. `tied_rows.expected.txt` is what
//! `elixir tools/distill-telemetry.exs --top 32` prints for it. The trace is kept
//! as captured, with its wake `disposition` fields renamed to `admission`
//! (`enqueued` -> `started`): a fresh capture has different timings and may
//! not tie.
//!
//! Compiling the script is itself a measurement. One drive of the product
//! stack spends at most `PRODUCT_DRIVE_BUDGET` requests, and a compile runs
//! several drives; the pin below holds the script's compile to the numbers
//! `pull.drive.finished` and `pull.product.requested` report.

use std::env::temp_dir;
use std::fs::{File, read_to_string, remove_file};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
const SCRIPT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tools/distill-telemetry.exs");
const TRACE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/distill_telemetry/main_returns_one.jsonl"
);
const EXPECTED: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/distill_telemetry/main_returns_one.expected.txt"
);

const TIED_TRACE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/distill_telemetry/tied_rows.jsonl");
const TIED_EXPECTED: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/distill_telemetry/tied_rows.expected.txt"
);
const TIED_ARGS: [&str; 3] = ["--top", "32", TIED_TRACE];

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn expected_stdout() -> String {
    expectation(EXPECTED)
}

fn expectation(path: &str) -> String {
    read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"))
}

fn stdout_of_success(output: Output, what: &str) -> String {
    assert!(
        output.status.success(),
        "{what} exited {}:\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{what} wrote to stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap_or_else(|e| panic!("{what} stdout is UTF-8: {e}"))
}

fn assert_prints_expected(actual: &str, what: &str) {
    assert_prints(actual, &expected_stdout(), what);
}

fn assert_prints(actual: &str, expected: &str, what: &str) {
    assert!(
        actual == expected,
        "{what} did not print what real elixir prints for the same trace.\n--- expected ---\n{expected}\n--- actual ---\n{actual}"
    );
}

/// The reference: the checked-in expectation is what `elixir` prints today.
#[test]
fn elixir_prints_the_checked_in_expectation() {
    let output = Command::new("elixir")
        .arg(SCRIPT)
        .arg(TRACE)
        .output()
        .expect("spawn `elixir tools/distill-telemetry.exs` (is Elixir installed and on PATH?)");
    assert_prints_expected(&stdout_of_success(output, "elixir distill-telemetry.exs"), "elixir");
}

/// The reference for the trace whose rows tie at the cut.
#[test]
fn elixir_prints_the_checked_in_expectation_for_tied_rows() {
    let output = Command::new("elixir")
        .arg(SCRIPT)
        .args(TIED_ARGS)
        .output()
        .expect("spawn `elixir tools/distill-telemetry.exs` (is Elixir installed and on PATH?)");
    assert_prints(
        &stdout_of_success(output, "elixir distill-telemetry.exs --top 32"),
        &expectation(TIED_EXPECTED),
        "elixir, tied rows",
    );
}

/// The distiller under the interpreter prints exactly what elixir prints.
#[test]
fn interp_runs_the_distiller_as_elixir_does() {
    let output = Command::new(FZ2_BIN)
        .args(["interp", SCRIPT, TRACE])
        .output()
        .expect("invoke fz2 interp");
    assert_prints_expected(&stdout_of_success(output, "fz2 interp"), "fz2 interp");
}

/// The distiller under the JIT prints exactly what elixir prints.
#[test]
fn run_runs_the_distiller_as_elixir_does() {
    let output = Command::new(FZ2_BIN)
        .args(["run", SCRIPT, TRACE])
        .output()
        .expect("invoke fz2 run");
    assert_prints_expected(&stdout_of_success(output, "fz2 run"), "fz2 run");
}

/// The distiller built ahead of time prints exactly what elixir prints.
#[test]
fn build_links_the_distiller_that_prints_as_elixir_does() {
    let binary = unique_temp_path("fz2_distiller", ".bin");
    let build = Command::new(FZ2_BIN)
        .arg("build")
        .arg("-o")
        .arg(&binary)
        .arg(SCRIPT)
        .output()
        .expect("invoke fz2 build");
    stdout_of_success(build, "fz2 build");
    let run = Command::new(&binary).arg(TRACE).output();
    let tied = Command::new(&binary).args(TIED_ARGS).output();
    let _ = remove_file(&binary);
    let _ = remove_file(binary.with_extension("bin.o"));
    let run = run.expect("run the built distiller");
    assert_prints_expected(&stdout_of_success(run, "the built distiller"), "the built distiller");
    // Rows that tie at the cut are the same rows elixir keeps, whatever order
    // a map's entries come back in.
    let tied = tied.expect("run the built distiller over tied rows");
    assert_prints(
        &stdout_of_success(tied, "the built distiller, tied rows"),
        &expectation(TIED_EXPECTED),
        "the built distiller, tied rows",
    );
}

/// What a compile's telemetry says it spent on the product stack.
#[derive(Debug, PartialEq, Eq)]
struct CompileSpend {
    /// Every `pull.product.requested`, over all drives.
    requests: u64,
    /// `requests` of each `pull.drive.finished`, in drive order.
    drives: Vec<u64>,
    /// Every derivation the World's job completions filed, over all jobs.
    derivations: u64,
    /// Every read those derivations handed the World, counted per derivation.
    reads_handed: u64,
}

impl CompileSpend {
    fn largest_drive(&self) -> u64 {
        self.drives.iter().copied().max().unwrap_or(0)
    }
}

const REQUESTED_LINE: &str = r#"{"name":["fz","compiler2","pull","product","requested"]"#;
const APPLIED_LINE: &str = r#"{"name":["fz","compiler2","work_graph","applied"]"#;
const DRIVE_FINISHED_LINE: &str = r#"{"name":["fz","compiler2","pull","drive","finished"]"#;

fn read_compile_spend(trace: &Path) -> CompileSpend {
    let lines = BufReader::new(File::open(trace).unwrap_or_else(|e| panic!("open {}: {e}", trace.display())));
    let mut spend = CompileSpend {
        requests: 0,
        drives: Vec::new(),
        derivations: 0,
        reads_handed: 0,
    };
    for line in lines.lines() {
        let line = line.expect("telemetry line is UTF-8");
        if line.starts_with(REQUESTED_LINE) {
            spend.requests += 1;
        } else if line.starts_with(DRIVE_FINISHED_LINE) {
            let event: serde_json::Value = serde_json::from_str(&line).expect("drive event is JSON");
            let requests = event["metadata"]["requests"]
                .as_u64()
                .expect("drive.finished carries requests");
            spend.drives.push(requests);
        } else if line.starts_with(APPLIED_LINE) {
            let event: serde_json::Value = serde_json::from_str(&line).expect("applied event is JSON");
            let completion = &event["metadata"]["completion"];
            spend.derivations += completion["derivations"].as_u64().unwrap_or(0);
            spend.reads_handed += completion["reads_handed"].as_u64().unwrap_or(0);
        }
    }
    spend
}

// 18_324 -> 18_405 derivations, and 227 more reads: a binary that one user holds whole and
// another matches is asked for twice, whole and then matched, so the functions between them
// derive their demand once more: `JSON.decode/1` and its helpers, `String.take_bytes/2`,
// `String.graphemes/1`, `Kernel.inspect/1`.
// 18_405 -> 18_410 derivations, and more reads: `JSON.encode/1` writes into one
// accumulator, and its pass is the helpers `encode_into`, `key_into`, `string_into`, `walk`,
// `walk_scalar` and `append_run` in place of `encode_binary!` and `encode_key!`, so the
// distiller derives demand for more functions.
// 18_410 -> 18_335 derivations, and fewer reads: a `JSON` string decodes in one pass with
// the `utf8` segment, so `Utf8.next`'s result handling, `Utf8.from_codepoint` and the
// decoder's second pass are no longer compiled for decoding.
// 18_335 -> 18_334: `String.duplicate/2` is `:binary.copy/2`, so the doubling helper is no
// longer compiled.
// 18_334 -> 18_340: `Kernel.byte_size` narrows an `any` argument to `bitstring`, so `fz_bitstring_byte_extent/1` and `JSON.offset/2` each take one more activation.
// 18_340 -> 18_338: JSON's string clause is guarded by `is_binary` and no longer passes an alignment argument, so `string_into/3` and its two clauses are not compiled.
// 18_338 -> 18_339: `:erlang` defines `error/1`, and the distiller reaches `:erlang`, so
// defining the module derives one more function.
// 18_339 -> 18_342: `Kernel` defines `is_function/1`, `is_function/2` and
// `fz_function_arity/1`, and defining a module publishes each of its functions'
// source, one derivation each, whether or not the distiller calls them.
// 18_342 -> 18_344: `Kernel` defines `bit_size/1` and `fz_bitstring_bit_extent/1`, one
// derivation each, as above.
// 18_344 -> 18_345: `Kernel` defines `is_number/1`, one derivation, as above.
// 18_345 -> 19_800: a reach is a fact answered by a job of its own: 356 `DeriveStaticReach` runs
// (292 functions whose recursion is asked) and 1_202 `DeriveExecutableReach` runs (one per
// executable whose return a transport position names), less 104 runs elsewhere that no longer
// restart for a reach they were waiting on.
// 19_800 -> 19_850: the ordering operators' `binary` clause adds its `fz_op_*_bb` activation and splits the catch-all's `compare/2` activations, the same way the int and float clauses already do.
// 19_850 -> 19_810: a module is started once its enclosing scope exists, so each module's
// definition runs once fewer.
// 19_810 -> 19_811: the product waits on the distiller's own declarations
// being checked. It declares nothing, so the check is one `CheckDeclarations`.
// 19_811 -> 19_812: what a program can raise is a fact of that program, so the entry's handler
// no longer starts from the raises of the macros' programs. The entry publishes its own program's
// first raise and is analysed once more on it.
// 19_812 -> 19_806: `Enum.to_list/1` has a clause that builds a range's list itself.
// 19_806 -> 19_661: a first-class callable's boundary demand is not contributed back to its target's inputs, so the target's demand is not derived again for it.
// 19_661 -> 19_658: `String.to_integer` and `String.to_float` read through
// `Integer.parse` and `Float.parse`, so String defines three fewer private
// functions and its `DefineModule` notes three fewer.
// 19_658 -> 19_593: `JSON` decodes a `\uXXXX` by guarding on its hex digits and matches each
// simple escape in a clause of `escaped`, so `simple_escape`, `join_run`, `hex4_join` and the
// `:error` results they carried are no longer derived.
// 19_593 -> 19_589: Kernel no longer defines `assert/1,2` and `refute/1,2`.
// 19_589 -> 19_587: `File.read/1` reads through one `fz_file_read_rest` extern, so `File`
// defines `read_bytes`, `read_byte` and the `fgetc` extern no more and derives them no more.
// 19_587 -> 19_564: `JSON` adds an integer's digits as they are scanned and reports a wide one
// after a re-scan, so `integer_step`'s seven clauses and the `:overflow` they carried are gone.
// 19_564 -> 19_521: a closure call names the widest activation of each closure, so the
// narrower activations its closure callsites had settled are not derived.
// 19_521 -> 17_076: a call round a recursion cycle keeps the entering activation's key at the
// slots the cycle supplies, so the reduce families have fewer activations to derive.
const DERIVATIONS: u64 = 17_076;
// 111_876 -> 111_888: an extern that declares `raises:` reads the struct of
// the exception it names, to raise that struct. The distiller calls twelve
// such externs, and each contract reads `StructDefined` once.
// 111_888 -> 111_880: a replaced definition's source is part of the answer of
// the definition that replaces it, so `KeyError` and
// `Protocol.UndefinedError`, which override `message/1`, file one derivation
// for it, not two.
// 111_880 -> 112_107: the 227 reads of the demand derived once more.
// 112_107 -> 112_127: the reads of the encoder's helpers.
// 112_127 -> 111_800: the reads the one-pass decoder no longer derives.
// 111_800 -> 111_796: the same fall as `DERIVATIONS`.
// 111_796 -> 111_800: the same rise as `DERIVATIONS`.
// 111_800 -> 111_792: the same fall as `DERIVATIONS`.
// 111_792 -> 111_794: the reads of the same `:erlang.error/1` definition.
// 111_794 -> 111_812: the six reads each of the three new `Kernel` functions.
// 111_812 -> 111_824: the six reads each of the two new `Kernel` functions.
// 111_824 -> 111_830: the six reads of the new `Kernel.is_number/1`.
// 111_830 -> 156_110: a reach job reads the edge fact of every node it reaches, so each of its
// 1_558 runs hands the World one read per node of its cone.
// 156_110 -> 156_740: the same activations, each read once per derivation, and each reach
// job whose cone now holds the binary clause's activations reads them too.
// 156_740 -> 156_741: that check reads the source's index.
// 156_741 -> 156_747: the six reads of the entry's one more analysis, as in `DERIVATIONS`.
// 156_747 -> 156_894: `Enum.to_list/1`'s range clause is reachable where the distiller lists an
// `any` enumerable, so the reach jobs whose cones hold it read its activations too.
// 156_894 -> 155_916: the reads of those 145 derivations.
// 155_916 -> 155_904: String's three fewer private functions, four reads each.
// 155_904 -> 155_345: the reads of those 65 derivations.
// 155_345 -> 155_321: Kernel's four fewer functions, six reads each.
// 155_321 -> 155_313: the reads of File's 2 fewer derivations.
// 155_313 -> 155_014: the reads of those 23 derivations.
// 155_014 -> 154_544: the reads of those 43 derivations.
// 154_544 -> 128_751: the same, each activation read once per derivation.
const READS_HANDED: u64 = 128_751;

/// Compiling the distiller spends this much of the product stack. The largest
/// drive is the one `PRODUCT_DRIVE_BUDGET` bounds, so its headroom is the
/// margin before the compile stops with a budget error; the total and the
/// drive count say how the rest of the compile is spread.
#[test]
fn the_distiller_compiles_inside_the_product_drive_budget() {
    let trace = unique_temp_path("fz2_distiller_compile", ".jsonl");
    let output = Command::new(FZ2_BIN)
        .arg("--log-telemetry")
        .arg(&trace)
        .args(["interp", SCRIPT, TRACE])
        .output()
        .expect("invoke fz2 interp with telemetry");
    let stdout = stdout_of_success(output, "fz2 interp --log-telemetry");
    let spend = read_compile_spend(&trace);
    let _ = remove_file(&trace);
    assert_prints_expected(&stdout, "fz2 interp --log-telemetry");

    let measured = (spend.largest_drive(), spend.requests, spend.drives.len());
    assert_eq!(
        measured,
        // (47_681, 49_093, 28) -> (47_534, 48_946, 28): a non-recursive key collapses structure
        // nothing asks about to its class, as a recursive key does, so callers that differ only in
        // such freight share one activation.
        // (47_534, 48_946, 28) -> (47_447, 48_858, 28): `Enum.uniq` asks a map whether it has
        // seen a value, so the distiller no longer compiles a list scan for it.
        // (47_447, 48_858, 28) -> (47_803, 49_224, 28): `JSON` reads a number by its grammar
        // and converts its text with `Float.parse`, so the distiller compiles that grammar and
        // the parse.
        // (47_803, 49_224, 28) -> (48_886, 50_745, 65): the program's entry wraps `main` in the
        // handler that words an uncaught raise, so the compile also covers the exception modules
        // the distiller can raise and the banner that prints them, and each `defexception` in
        // those modules expands in a drive of its own.
        // (48_886, 50_745, 65) -> (49_041, 50_908, 66): `Enum.into` runs its reduction under a
        // handler that tells the collector `:halt` and raises again, so the distiller's `into`
        // calls compile that handler and `:erlang.raise/3`.
        // (49_041, 50_908, 66) -> (49_044, 50_911, 66): code after a map update's key check
        // reads the update's own value rather than the check's result, so that value is
        // carried through the check and its transport is asked for once more per carry.
        // (49_044, 50_911, 66) -> (48_664, 50_522, 66): a `JSON` string is one pass that matches
        // a multi-byte character with the `utf8` segment and appends `<<codepoint :: utf8>>`
        // for a `\u` escape, so the distiller no longer compiles `Utf8.next`'s result handling
        // or `Utf8.from_codepoint` for decoding.
        // (48_664, 50_522, 66) -> (48_666, 50_524, 66): `Kernel.byte_size` narrows an `any`
        // argument to `bitstring`, so `fz_bitstring_byte_extent/1` and `JSON.offset/2` each take
        // one more activation.
        // (48_666, 50_524, 66) -> (48_666, 50_530, 66): quoted metadata is a keyword list, so the
        // `panic` calls `Kernel.raise/1` and `Kernel.defexception/1` quote build a tuple inside a
        // list where they built a map, and each of those values is asked for its transport once.
        // (48_666, 50_530, 66) -> (46_243, 46_797, 26): a reach is a fact, so no product request
        // asks for one and no drive starts to serve one. The 4_813 reach requests are gone, and
        // the 35 drives that only served reach and the 5 root drives that only waited on one with
        // them (66 -> 26). A transport shape waiting on a reach is evaluated 1_202 times as
        // waiting on the fact, where it waited on the product 165 times: its reach is answered
        // by a job outside the drive, so the shape is requested again once that job lands
        // (30_289 -> 31_325 transport shape requests).
        // (46_243, 46_797, 26) -> (46_285, 46_839, 26): the ordering operators' `binary` clause adds its `fz_op_*_bb` activation and splits the catch-all's `compare/2` activations, the same way the int and float clauses already do.
        // (46_285, 46_839, 26) -> (46_237, 46_791, 26): `Enum.to_list/1` builds a range's list itself, so listing a range no longer reaches the reduce-and-reverse path.
        // (46_237, 46_791, 26) -> (46_402, 46_956, 26): a case arm's parameter is laid out by its
        // own demand, so each outcome parameter is a `Value` position the compile requests.
        // (46_402, 46_956, 26) -> (46_477, 47_031, 26): +75: each simple escape is its own clause of `escaped`; the added clauses cost transport_shape positions; authorized by the user
        // (46_477, 47_031, 26) -> (46_341, 46_629, 26): a literal made of constants is one
        // constant and a quote builds only the nodes above an `unquote`, so the values that were
        // their parts are no longer positions the compile requests.
        // (46_341, 46_629, 26) -> (46_264, 46_552, 26): `JSON` adds an integer's digits as they are scanned
        // and a wide integer raises `ArithmeticError`, so the compile no longer carries the
        // `:overflow` clauses of `integer_step`.
        // (46_264, 46_552, 26) -> (46_268, 46_556, 26): a closure call names the widest activation
        // of each closure, so 8 fewer callsites settle and 30 fewer jobs run; in the new order six
        // positions are asked for once more and two once fewer.
        // (46_268, 46_556, 26) -> (37_345, 37_633, 26): a call inside a recursion cycle keys the slots the cycle supplies from the cycle's entry, so the distiller's reduces compile one activation per cycle member where each ascent state had its own.
        (37_345, 37_633, 26),
        "(largest drive requests, total requests, drives) for the distiller's compile moved. \
         A fall is lowered in this pin; a rise is investigated first, because the largest drive \
         may not exceed PRODUCT_DRIVE_BUDGET (50,000)."
    );
    assert_eq!(
        (spend.derivations, spend.reads_handed),
        (DERIVATIONS, READS_HANDED),
        "(derivations, reads handed) the World's job completions took for the distiller's compile \
         moved. A fall is lowered in this pin; a rise is investigated first, because each read \
         handed to the World is paid for per derivation."
    );
}
