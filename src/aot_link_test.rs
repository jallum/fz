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
