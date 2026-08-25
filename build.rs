use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=runtime/Cargo.toml");
    println!("cargo:rerun-if-changed=runtime/src");
    println!("cargo:rerun-if-env-changed=CARGO");
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));
    let target = out.join("runtime-artifact");
    let profile = env::var("PROFILE").expect("PROFILE");
    let target_triple = env::var("TARGET").expect("TARGET");
    let mut command = Command::new(env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
    command
        .args([
            "rustc",
            "-p",
            "fz-runtime",
            "--crate-type",
            "staticlib",
            "--target",
            &target_triple,
            "--target-dir",
        ])
        .arg(&target);
    if profile == "release" {
        command.arg("--release");
    }
    let status = command.status().expect("run runtime staticlib cargo build");
    assert!(status.success(), "runtime staticlib cargo build failed");
    let archive = target.join(&target_triple).join(&profile).join("libfz_runtime.a");
    assert!(archive.is_file(), "runtime staticlib archive was not produced");
    println!(
        "cargo:rustc-env=FZ_AOT_EMBEDDED_RUNTIME_STATICLIB={}",
        archive.display()
    );
}
