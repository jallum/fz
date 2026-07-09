use super::*;

#[test]
fn coverage_target_uses_isolated_clean_runtime() {
    let exe = Path::new("/repo/target/llvm-cov-target/debug/fz");

    let plan = runtime_archive_plan(exe, None, false);

    assert_eq!(
        plan,
        RuntimeArchivePlan::IsolatedCoverageBuild {
            target_root: PathBuf::from("/repo/target"),
            profile: CargoProfile::Debug
        }
    );
}

#[test]
fn coverage_environment_uses_isolated_clean_runtime_even_outside_llvm_cov_target() {
    let exe = Path::new("/repo/target/debug/fz");

    let plan = runtime_archive_plan(exe, None, true);

    assert_eq!(
        plan,
        RuntimeArchivePlan::IsolatedCoverageBuild {
            target_root: PathBuf::from("/repo/target"),
            profile: CargoProfile::Debug
        }
    );
}

#[test]
fn explicit_runtime_archive_override_wins_over_coverage_detection() {
    let exe = Path::new("/repo/target/llvm-cov-target/debug/fz");
    let override_path = PathBuf::from("/tmp/libfz_runtime.a");

    let plan = runtime_archive_plan(exe, Some(override_path.clone()), true);

    assert_eq!(plan, RuntimeArchivePlan::EnvOverride(override_path));
}

#[test]
fn ordinary_debug_binary_uses_sibling_target_dir() {
    let exe = Path::new("/repo/target/debug/fz");

    let plan = runtime_archive_plan(exe, None, false);

    assert_eq!(
        plan,
        RuntimeArchivePlan::Sibling {
            target_dir: PathBuf::from("/repo/target/debug")
        }
    );
}

#[test]
fn deps_binary_uses_parent_target_dir() {
    let exe = Path::new("/repo/target/debug/deps/fz-abc123");

    let plan = runtime_archive_plan(exe, None, false);

    assert_eq!(
        plan,
        RuntimeArchivePlan::Sibling {
            target_dir: PathBuf::from("/repo/target/debug")
        }
    );
}

#[test]
fn release_coverage_target_preserves_release_profile() {
    let exe = Path::new("/repo/target/llvm-cov-target/release/fz");

    let plan = runtime_archive_plan(exe, None, false);

    assert_eq!(
        plan,
        RuntimeArchivePlan::IsolatedCoverageBuild {
            target_root: PathBuf::from("/repo/target"),
            profile: CargoProfile::Release
        }
    );
}

#[test]
fn clean_runtime_build_scrubs_coverage_and_target_env() {
    for key in [
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "RUSTDOCFLAGS",
        "CARGO_ENCODED_RUSTDOCFLAGS",
        "CARGO_BUILD_RUSTFLAGS",
        "RUSTC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS",
        "CARGO_TARGET_DIR",
        "LLVM_PROFILE_FILE",
        "LLVM_COV",
        "LLVM_PROFDATA",
        "CARGO_LLVM_COV",
        "CARGO_LLVM_COV_TARGET_DIR",
    ] {
        assert!(
            should_scrub_for_clean_runtime_build(OsStr::new(key)),
            "{key} should be scrubbed"
        );
    }

    assert!(!should_scrub_for_clean_runtime_build(OsStr::new("PATH")));
    assert!(!should_scrub_for_clean_runtime_build(OsStr::new("CARGO_HOME")));
}

/// Selection must come from Cargo's own artifact report, never from
/// filesystem mtime. Fabricate a decoy `libfz_runtime-*.a` whose mtime is
/// newer than the archive Cargo actually reports as this build's output; a
/// mtime-based picker would return the decoy, but the deterministic selector
/// must still return the archive named in the `compiler-artifact` message.
#[test]
fn runtime_staticlib_selection_ignores_decoy_newer_mtime_archive() {
    use std::fs::{create_dir_all, write as fs_write};
    use std::thread::sleep;
    use std::time::Duration;

    let dir = std::env::temp_dir().join(format!(
        "fz_aot_link_test_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    create_dir_all(&dir).expect("create temp dir");

    let authoritative = dir.join("libfz_runtime-19d6c6c451fa0f44.a");
    fs_write(&authoritative, b"real archive").expect("write authoritative archive");

    // Give the decoy a strictly newer mtime than the authoritative archive,
    // as would happen when a concurrent, unrelated build refreshes a stale
    // hashed archive mid-run.
    sleep(Duration::from_millis(10));
    let decoy = dir.join("libfz_runtime-deadbeefcafefeed.a");
    fs_write(&decoy, b"stale archive with a newer mtime").expect("write decoy archive");

    let authoritative_mtime = authoritative.metadata().unwrap().modified().unwrap();
    let decoy_mtime = decoy.metadata().unwrap().modified().unwrap();
    assert!(
        decoy_mtime > authoritative_mtime,
        "decoy must have the newer mtime for this test to prove anything"
    );

    let cargo_stdout = format!(
        concat!(
            r#"{{"reason":"compiler-artifact","package_id":"path+file:///repo/runtime#libc@0.2.0","target":{{"kind":["lib"],"name":"libc"}},"filenames":["/repo/target/debug/deps/liblibc-aaaa.rlib"]}}"#,
            "\n",
            r#"{{"reason":"build-script-executed","package_id":"path+file:///repo/runtime#fz-runtime@0.1.0"}}"#,
            "\n",
            r#"{{"reason":"compiler-artifact","package_id":"path+file:///repo/runtime#fz-runtime@0.1.0","target":{{"kind":["staticlib","rlib"],"name":"fz_runtime"}},"filenames":["{authoritative}","{rlib}"]}}"#,
        ),
        authoritative = authoritative.display(),
        rlib = dir.join("libfz_runtime-19d6c6c451fa0f44.rlib").display(),
    );

    let selected = runtime_staticlib_from_cargo_messages(cargo_stdout.as_bytes())
        .expect("cargo message names a staticlib artifact");

    assert_eq!(
        selected, authoritative,
        "selection must follow Cargo's compiler-artifact message, not the newer-mtime decoy"
    );
    assert_ne!(selected, decoy);

    let _ = std::fs::remove_dir_all(&dir);
}

/// A single cargo invocation can legitimately report `fz-runtime` more than
/// once (e.g. the lib target and a unit-test binary both trigger a
/// `compiler-artifact` message with `target.name == "fz_runtime"`). The
/// selector must pick deterministically rather than panic or pick
/// ambiguously; it does so by taking the FIRST matching message in stream
/// order (`Iterator::find_map` over `lines()`), so this pins "first match
/// wins" as the intended contract.
#[test]
fn runtime_staticlib_selection_is_deterministic_across_multiple_fz_runtime_artifacts() {
    let cargo_stdout = concat!(
        r#"{"reason":"compiler-artifact","package_id":"path+file:///repo/runtime#libc@0.2.0","target":{"kind":["lib"],"name":"libc"},"filenames":["/repo/target/debug/deps/liblibc-aaaa.rlib"]}"#,
        "\n",
        // First fz_runtime artifact message: the one that must win.
        r#"{"reason":"compiler-artifact","package_id":"path+file:///repo/runtime#fz-runtime@0.1.0","target":{"kind":["staticlib","rlib"],"name":"fz_runtime"},"filenames":["/repo/target/debug/deps/libfz_runtime-1111111111111111.a","/repo/target/debug/deps/libfz_runtime-1111111111111111.rlib"]}"#,
        "\n",
        // Second fz_runtime artifact message (e.g. the test-harness build of
        // the same crate): must NOT override the first match.
        r#"{"reason":"compiler-artifact","package_id":"path+file:///repo/runtime#fz-runtime@0.1.0","target":{"kind":["staticlib","rlib"],"name":"fz_runtime"},"filenames":["/repo/target/debug/deps/libfz_runtime-2222222222222222.a","/repo/target/debug/deps/libfz_runtime-2222222222222222.rlib"]}"#,
    );

    // Confirm this fixture actually exercises the multi-match corner before
    // trusting what the selector does with it.
    let fz_runtime_artifact_count = cargo_stdout
        .lines()
        .filter(|line| line.contains(r#""name":"fz_runtime""#))
        .count();
    assert_eq!(
        fz_runtime_artifact_count, 2,
        "fixture must contain at least two fz_runtime compiler-artifact messages"
    );

    let selected = runtime_staticlib_from_cargo_messages(cargo_stdout.as_bytes())
        .expect("cargo message names a staticlib artifact");

    assert_eq!(
        selected,
        PathBuf::from("/repo/target/debug/deps/libfz_runtime-1111111111111111.a"),
        "selection must deterministically take the first fz_runtime compiler-artifact message"
    );
}

/// When cargo's message stream never names an `fz_runtime` compiler-artifact
/// (e.g. only unrelated dependency artifacts and build-script messages are
/// present), the selector must return `None` so the caller can surface a loud
/// error, rather than silently returning a wrong path or panicking.
#[test]
fn runtime_staticlib_selection_returns_none_when_no_fz_runtime_artifact_is_reported() {
    let cargo_stdout = concat!(
        r#"{"reason":"compiler-artifact","package_id":"path+file:///repo/runtime#libc@0.2.0","target":{"kind":["lib"],"name":"libc"},"filenames":["/repo/target/debug/deps/liblibc-aaaa.rlib"]}"#,
        "\n",
        r#"{"reason":"build-script-executed","package_id":"path+file:///repo/runtime#fz-runtime@0.1.0"}"#,
    );

    // Confirm the fixture truly has zero fz_runtime compiler-artifact
    // messages before trusting the `None` result below.
    let fz_runtime_artifact_count = cargo_stdout
        .lines()
        .filter(|line| line.contains(r#""reason":"compiler-artifact""#) && line.contains(r#""name":"fz_runtime""#))
        .count();
    assert_eq!(
        fz_runtime_artifact_count, 0,
        "fixture must not contain any fz_runtime compiler-artifact message"
    );

    let selected = runtime_staticlib_from_cargo_messages(cargo_stdout.as_bytes());

    assert_eq!(
        selected, None,
        "absence of an fz_runtime compiler-artifact message must surface as None (the caller's ok_or_else error path), not a silent fallback"
    );
}
