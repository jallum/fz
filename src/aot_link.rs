//! AOT link-time runtime archive selection.
//!
//! `fz build` links generated object code with `fz-runtime`'s staticlib. When
//! the `fz` binary itself was built by `cargo llvm-cov`, the sibling runtime
//! archive is coverage-instrumented too; linking that archive into a plain AOT
//! executable leaks unresolved LLVM profile-runtime symbols. Treat the AOT
//! executable as the product and use a clean runtime archive at this boundary.

use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::{read_dir, remove_file, write};
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

const RUNTIME_ARCHIVE_OVERRIDE_ENV: &str = "FZ_AOT_RUNTIME_STATICLIB";
const LLVM_COV_TARGET_COMPONENT: &str = "llvm-cov-target";
const ISOLATED_AOT_TARGET_DIR: &str = "fz-aot-clean-runtime";

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RuntimeArchive {
    pub(crate) path: PathBuf,
    pub(crate) source: RuntimeArchiveSource,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RuntimeArchiveSource {
    EnvOverride,
    Sibling,
    IsolatedCoverageBuild,
}

#[derive(Debug)]
pub(crate) struct RuntimeArchiveError {
    message: String,
}

impl RuntimeArchiveError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for RuntimeArchiveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for RuntimeArchiveError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CargoProfile {
    Debug,
    Release,
}

impl CargoProfile {
    fn as_str(self) -> &'static str {
        match self {
            CargoProfile::Debug => "debug",
            CargoProfile::Release => "release",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RuntimeArchivePlan {
    EnvOverride(PathBuf),
    Sibling {
        target_dir: PathBuf,
    },
    IsolatedCoverageBuild {
        target_root: PathBuf,
        profile: CargoProfile,
    },
}

pub(crate) fn resolve_runtime_archive() -> Result<RuntimeArchive, RuntimeArchiveError> {
    let override_path = env::var_os(RUNTIME_ARCHIVE_OVERRIDE_ENV)
        .filter(|value| !value.is_empty())
        .map(PathBuf::from);
    let exe = env::current_exe().map_err(|e| RuntimeArchiveError::new(format!("locating current executable: {e}")))?;
    let plan = runtime_archive_plan(&exe, override_path, coverage_env_present());
    resolve_runtime_archive_plan(plan)
}

#[derive(Debug)]
pub(crate) enum LinkAotError {
    WriteObject { path: PathBuf, error: io::Error },
    RuntimeArchive(RuntimeArchiveError),
    InvokeCc { error: io::Error },
    CcExit { status: ExitStatus },
}

impl fmt::Display for LinkAotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LinkAotError::WriteObject { path, error } => {
                write!(f, "write object {}: {error}", path.display())
            }
            LinkAotError::RuntimeArchive(error) => write!(f, "runtime archive: {error}"),
            LinkAotError::InvokeCc { error } => write!(f, "failed to invoke cc: {error}"),
            LinkAotError::CcExit { status } => write!(f, "cc exited {status}"),
        }
    }
}

impl std::error::Error for LinkAotError {}

/// Link one AOT object into a native executable next to `output_path`.
///
/// The intermediate object is left behind on failure and removed on success.
pub(crate) fn link_aot_artifact(
    artifact: &crate::ir_codegen::AotArtifact,
    output_path: &Path,
) -> Result<(), LinkAotError> {
    let obj_temp = PathBuf::from(format!("{}.o", output_path.display()));
    write(&obj_temp, &artifact.object).map_err(|error| LinkAotError::WriteObject {
        path: obj_temp.clone(),
        error,
    })?;

    let runtime_archive = resolve_runtime_archive().map_err(LinkAotError::RuntimeArchive)?;
    let mut cc = Command::new("cc");
    cc.arg("-o").arg(output_path).arg(&obj_temp).arg(&runtime_archive.path);
    if cfg!(target_os = "macos") {
        cc.arg("-Wl,-undefined,dynamic_lookup");
    }

    let status = cc.status().map_err(|error| LinkAotError::InvokeCc { error })?;
    if !status.success() {
        return Err(LinkAotError::CcExit { status });
    }

    let _ = remove_file(&obj_temp);
    Ok(())
}

fn resolve_runtime_archive_plan(plan: RuntimeArchivePlan) -> Result<RuntimeArchive, RuntimeArchiveError> {
    match plan {
        RuntimeArchivePlan::EnvOverride(path) => existing_archive(path, RuntimeArchiveSource::EnvOverride),
        RuntimeArchivePlan::Sibling { target_dir } => find_runtime_archive(&target_dir)
            .ok_or_else(|| missing_archive_error(&target_dir))
            .map(|path| RuntimeArchive {
                path,
                source: RuntimeArchiveSource::Sibling,
            }),
        RuntimeArchivePlan::IsolatedCoverageBuild { target_root, profile } => {
            ensure_isolated_clean_runtime_archive(&target_root, profile).map(|path| RuntimeArchive {
                path,
                source: RuntimeArchiveSource::IsolatedCoverageBuild,
            })
        }
    }
}

fn existing_archive(path: PathBuf, source: RuntimeArchiveSource) -> Result<RuntimeArchive, RuntimeArchiveError> {
    if path.is_file() {
        Ok(RuntimeArchive { path, source })
    } else {
        Err(RuntimeArchiveError::new(format!(
            "{} points at missing runtime archive {}",
            RUNTIME_ARCHIVE_OVERRIDE_ENV,
            path.display()
        )))
    }
}

fn runtime_archive_plan(exe: &Path, override_path: Option<PathBuf>, coverage_env_present: bool) -> RuntimeArchivePlan {
    if let Some(path) = override_path {
        return RuntimeArchivePlan::EnvOverride(path);
    }

    let target_dir = executable_target_dir(exe);
    if coverage_env_present || has_component(&target_dir, OsStr::new(LLVM_COV_TARGET_COMPONENT)) {
        return RuntimeArchivePlan::IsolatedCoverageBuild {
            target_root: workspace_target_root(&target_dir),
            profile: profile_from_target_dir(&target_dir),
        };
    }

    RuntimeArchivePlan::Sibling { target_dir }
}

fn executable_target_dir(exe: &Path) -> PathBuf {
    let dir = exe.parent().unwrap_or_else(|| Path::new("target/debug"));
    if dir.file_name() == Some(OsStr::new("deps")) {
        return dir.parent().unwrap_or(dir).to_path_buf();
    }
    dir.to_path_buf()
}

fn profile_from_target_dir(target_dir: &Path) -> CargoProfile {
    if target_dir.file_name() == Some(OsStr::new("release")) {
        CargoProfile::Release
    } else {
        CargoProfile::Debug
    }
}

fn workspace_target_root(target_dir: &Path) -> PathBuf {
    path_before_component(target_dir, OsStr::new(LLVM_COV_TARGET_COMPONENT))
        .unwrap_or_else(|| target_dir.parent().unwrap_or(target_dir).to_path_buf())
}

fn path_before_component(path: &Path, needle: &OsStr) -> Option<PathBuf> {
    let mut before = PathBuf::new();
    for component in path.components() {
        if component.as_os_str() == needle {
            return Some(before);
        }
        before.push(component.as_os_str());
    }
    None
}

fn has_component(path: &Path, needle: &OsStr) -> bool {
    path.components().any(|component| component.as_os_str() == needle)
}

fn find_runtime_archive(target_dir: &Path) -> Option<PathBuf> {
    newest_hashed_runtime_archive(&target_dir.join("deps")).or_else(|| {
        let path = target_dir.join("libfz_runtime.a");
        path.is_file().then_some(path)
    })
}

fn newest_hashed_runtime_archive(deps_dir: &Path) -> Option<PathBuf> {
    read_dir(deps_dir)
        .ok()?
        .filter_map(Result::ok)
        .filter(|entry| {
            let name = entry.file_name();
            let s = name.to_string_lossy();
            s.starts_with("libfz_runtime-") && s.ends_with(".a")
        })
        .max_by_key(|entry| entry.metadata().and_then(|m| m.modified()).ok())
        .map(|entry| entry.path())
}

fn missing_archive_error(target_dir: &Path) -> RuntimeArchiveError {
    RuntimeArchiveError::new(format!(
        "could not find libfz_runtime.a under {} or {}",
        target_dir.join("deps").display(),
        target_dir.join("libfz_runtime.a").display()
    ))
}

fn ensure_isolated_clean_runtime_archive(
    target_root: &Path,
    profile: CargoProfile,
) -> Result<PathBuf, RuntimeArchiveError> {
    let isolated_target_root = target_root.join(ISOLATED_AOT_TARGET_DIR);
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    if !manifest.is_file() {
        return Err(RuntimeArchiveError::new(format!(
            "coverage-isolated AOT runtime needs Cargo.toml at {}",
            manifest.display()
        )));
    }

    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let mut cmd = Command::new(cargo);
    cmd.arg("build")
        .arg("--manifest-path")
        .arg(&manifest)
        .arg("-p")
        .arg("fz-runtime")
        .arg("--target-dir")
        .arg(&isolated_target_root);
    if profile == CargoProfile::Release {
        cmd.arg("--release");
    }
    scrub_coverage_env(&mut cmd);

    let output = cmd.output().map_err(|e| {
        RuntimeArchiveError::new(format!(
            "building clean AOT runtime in {}: {e}",
            isolated_target_root.display()
        ))
    })?;
    if !output.status.success() {
        return Err(RuntimeArchiveError::new(format!(
            "building clean AOT runtime in {} exited {}; stdout={:?} stderr={:?}",
            isolated_target_root.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )));
    }

    let target_dir = isolated_target_root.join(profile.as_str());
    find_runtime_archive(&target_dir).ok_or_else(|| missing_archive_error(&target_dir))
}

fn scrub_coverage_env(cmd: &mut Command) {
    for (key, _) in env::vars_os() {
        if should_scrub_for_clean_runtime_build(&key) {
            cmd.env_remove(key);
        }
    }
}

fn coverage_env_present() -> bool {
    env::var_os("CARGO_LLVM_COV").is_some()
        || env::var_os("LLVM_PROFILE_FILE").is_some()
        || env_mentions_coverage("RUSTFLAGS")
        || env_mentions_coverage("CARGO_ENCODED_RUSTFLAGS")
}

fn env_mentions_coverage(name: &str) -> bool {
    env::var_os(name).is_some_and(|value| {
        let value = value.to_string_lossy();
        value.contains("instrument-coverage") || value.contains("llvm-cov")
    })
}

fn should_scrub_for_clean_runtime_build(key: &OsStr) -> bool {
    let Some(key) = key.to_str() else {
        return false;
    };
    key == "RUSTFLAGS"
        || key == "CARGO_ENCODED_RUSTFLAGS"
        || key == "RUSTDOCFLAGS"
        || key == "CARGO_ENCODED_RUSTDOCFLAGS"
        || key == "CARGO_BUILD_RUSTFLAGS"
        || key == "RUSTC"
        || key == "RUSTC_WRAPPER"
        || key == "RUSTC_WORKSPACE_WRAPPER"
        || key == "CARGO_BUILD_RUSTC"
        || key == "CARGO_BUILD_RUSTC_WRAPPER"
        || key == "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
        || key == "CARGO_TARGET_DIR"
        || key == "LLVM_PROFILE_FILE"
        || key == "LLVM_COV"
        || key == "LLVM_PROFDATA"
        || key.starts_with("CARGO_LLVM_COV")
        || (key.starts_with("CARGO_TARGET_") && key.ends_with("_RUSTFLAGS"))
}

#[cfg(test)]
#[path = "aot_link_test.rs"]
mod aot_link_test;
