use std::process::Command;

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");

/// `fz help`, `fz --help`, and `fz -h` all print the same command tour to
/// stdout and exit 0. The body names every subcommand so the help cannot
/// silently fall out of step with the dispatch table.
#[test]
fn help_lists_every_command_on_stdout() {
    for flag in ["help", "--help", "-h"] {
        let out = Command::new(FZ_BIN)
            .arg(flag)
            .output()
            .unwrap_or_else(|e| panic!("spawn fz {flag}: {e}"));
        assert!(out.status.success(), "fz {flag} should exit 0, got {:?}", out.status);
        let stdout = String::from_utf8(out.stdout).expect("help is utf-8");
        for command in ["run", "build", "interp", "dump", "test", "repl"] {
            assert!(
                stdout.contains(command),
                "fz {flag} output should mention `{command}`; got:\n{stdout}"
            );
        }
        assert!(
            out.stderr.is_empty(),
            "fz {flag} should write nothing to stderr; got: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}
