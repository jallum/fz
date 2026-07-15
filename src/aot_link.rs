//! AOT link-time runtime archive selection.
//!
//! `fz2 build` links generated object code with `fz-runtime`'s staticlib. When
//! the `fz2` binary itself was built by `cargo llvm-cov`, the sibling runtime
//! archive is coverage-instrumented too; linking that archive into a plain AOT
//! executable leaks unresolved LLVM profile-runtime symbols. Treat the AOT
//! executable as the product and use a clean runtime archive at this boundary.

use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::{remove_file, write};
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

use crate::telemetry::{RawSpanStop1 as _, RawSpanTelemetry, TelemetryExt as _};

/// Escape hatch that lets an operator name the `fz-runtime` staticlib
/// directly, bypassing the build-time runtime archive.
///
/// Ordinary AOT `::build` uses the exact `fz-runtime` staticlib produced in
/// the isolated Cargo build-script target directory. It neither invokes Cargo
/// nor depends on the caller's current directory.
///
/// Set `FZ_AOT_RUNTIME_STATICLIB` to an absolute path to a prebuilt
/// `libfz_runtime*.a` to replace that path — for example, when packaging a
/// binary independently of Cargo's build directory. The path must be
/// absolute, name an existing file, and match the linking `fz2` ABI.
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
    Embedded,
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

#[derive(Clone, Debug, Eq, PartialEq)]
enum RuntimeArchivePlan {
    EnvOverride(PathBuf),
    Embedded(PathBuf),
    IsolatedCoverageBuild {
        target_root: PathBuf,
        profile: CargoProfile,
    },
}

pub(crate) fn resolve_runtime_archive<T: RawSpanTelemetry>(tel: &T) -> Result<RuntimeArchive, RuntimeArchiveError> {
    let archive_span = tel.raw_span0_1::<RuntimeArchiveSource>(&["fz", "compiler2", "aot", "resolve_runtime_archive"]);
    let override_path = env::var_os(RUNTIME_ARCHIVE_OVERRIDE_ENV)
        .filter(|value| !value.is_empty())
        .map(PathBuf::from);
    let exe = env::current_exe().map_err(|e| RuntimeArchiveError::new(format!("locating current executable: {e}")))?;
    let plan = runtime_archive_plan(&exe, override_path, coverage_env_present());
    let archive = resolve_runtime_archive_plan(plan)?;
    archive_span.stop1(&archive.source);
    Ok(archive)
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
pub(crate) fn link_aot_artifact<T: RawSpanTelemetry>(
    artifact: &crate::ir_codegen::AotArtifact,
    output_path: &Path,
    tel: &T,
) -> Result<(), LinkAotError> {
    let object_span = tel.raw_span1_0(&["fz", "compiler2", "aot", "write_object"], artifact);
    let obj_temp = PathBuf::from(format!("{}.o", output_path.display()));
    write(&obj_temp, &artifact.object).map_err(|error| LinkAotError::WriteObject {
        path: obj_temp.clone(),
        error,
    })?;
    drop(object_span);

    let runtime_archive = resolve_runtime_archive(tel).map_err(LinkAotError::RuntimeArchive)?;
    let mut cc = Command::new("cc");
    cc.arg("-o").arg(output_path).arg(&obj_temp).arg(&runtime_archive.path);
    if cfg!(target_os = "macos") {
        cc.arg("-Wl,-undefined,dynamic_lookup");
    }

    let _link_span = tel.raw_span1_0(&["fz", "compiler2", "aot", "link"], artifact);
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
        RuntimeArchivePlan::Embedded(path) => existing_archive(path, RuntimeArchiveSource::Embedded),
        RuntimeArchivePlan::IsolatedCoverageBuild { target_root, profile } => {
            let isolated_target_root = target_root.join(ISOLATED_AOT_TARGET_DIR);
            locate_runtime_staticlib(&isolated_target_root, profile, true).map(|path| RuntimeArchive {
                path,
                source: RuntimeArchiveSource::IsolatedCoverageBuild,
            })
        }
    }
}

fn existing_archive(path: PathBuf, source: RuntimeArchiveSource) -> Result<RuntimeArchive, RuntimeArchiveError> {
    if source == RuntimeArchiveSource::EnvOverride && !path.is_absolute() {
        return Err(RuntimeArchiveError::new(format!(
            "{} must be an absolute runtime archive path: {}",
            RUNTIME_ARCHIVE_OVERRIDE_ENV,
            path.display()
        )));
    }
    if path.is_file() {
        Ok(RuntimeArchive { path, source })
    } else {
        Err(RuntimeArchiveError::new(format!(
            "runtime archive is missing: {}",
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

    RuntimeArchivePlan::Embedded(PathBuf::from(env!("FZ_AOT_EMBEDDED_RUNTIME_STATICLIB")))
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

/// Ask Cargo for the exact staticlib path it produced for `fz-runtime` under
/// `target_root`/`profile`, instead of globbing `libfz_runtime-*.a` and
/// picking the newest by mtime.
///
/// Cargo's hashed dependency filenames (`libfz_runtime-<hash>.a`) are stable
/// for a given (rustc, features, profile, target) tuple, but stale archives
/// from earlier builds linger alongside the current one, and under parallel
/// `::build` test execution a *different* concurrent build can refresh one
/// of those files' mtimes mid-run. "Newest mtime" then names whichever build
/// last touched the filesystem, not necessarily the archive that matches
/// *this* invocation — a race, not a selection. Cargo's own
/// `--message-format=json` artifact report names the file it actually
/// produced for this exact invocation; asking it directly removes the
/// ambiguity at the source rather than guessing among candidates. Cargo also
/// serializes concurrent builds of the same target directory itself, so this
/// call is safe under contention where a directory scan was not.
fn locate_runtime_staticlib(
    target_root: &Path,
    profile: CargoProfile,
    scrub_env: bool,
) -> Result<PathBuf, RuntimeArchiveError> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    if !manifest.is_file() {
        return Err(RuntimeArchiveError::new(format!(
            "locating the fz-runtime staticlib needs Cargo.toml at {}",
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
        .arg(target_root)
        .arg("--message-format=json")
        .arg("-q");
    if profile == CargoProfile::Release {
        cmd.arg("--release");
    }
    if scrub_env {
        scrub_coverage_env(&mut cmd);
    }

    let output = cmd.output().map_err(|e| {
        RuntimeArchiveError::new(format!(
            "invoking `cargo build -p fz-runtime --target-dir {}`: {e}",
            target_root.display()
        ))
    })?;
    if !output.status.success() {
        return Err(RuntimeArchiveError::new(format!(
            "`cargo build -p fz-runtime --target-dir {}` exited {}; stderr={}",
            target_root.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        )));
    }

    runtime_staticlib_from_cargo_messages(&output.stdout).ok_or_else(|| {
        RuntimeArchiveError::new(format!(
            "`cargo build -p fz-runtime --target-dir {}` did not report a staticlib artifact",
            target_root.display()
        ))
    })
}

/// Parse Cargo's `--message-format=json` stream for the `fz-runtime`
/// `compiler-artifact` message and return the staticlib (`.a`) filename it
/// names. This is the deterministic, Cargo-authoritative counterpart to
/// globbing `libfz_runtime-*.a` and picking the newest by mtime.
fn runtime_staticlib_from_cargo_messages(stdout: &[u8]) -> Option<PathBuf> {
    String::from_utf8_lossy(stdout).lines().find_map(|line| {
        let message: serde_json::Value = serde_json::from_str(line).ok()?;
        if message.get("reason")?.as_str()? != "compiler-artifact" {
            return None;
        }
        if message.get("target")?.get("name")?.as_str()? != "fz_runtime" {
            return None;
        }
        message
            .get("filenames")?
            .as_array()?
            .iter()
            .filter_map(|name| name.as_str())
            .find(|name| name.ends_with(".a"))
            .map(PathBuf::from)
    })
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
