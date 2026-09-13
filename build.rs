use std::env;
use std::path::PathBuf;
use std::process::Command;

/// Keep every runtime export in the linked image, and visible to `dlsym`.
///
/// An executable exports nothing by default, so the linker drops a
/// `#[unsafe(no_mangle)]` function in the runtime rlib that no Rust code calls
/// -- and then `fz_extern_symbol_addr` cannot find it, because it is not in the
/// process at all. Compiled fz code names those functions by symbol, not by
/// Rust path, so the only reference is the one the fz program makes at run
/// time. Exporting dynamically is what makes them reachable.
///
/// AOT binaries get the same treatment on their own link line (`aot_link.rs`).
/// Windows needs none: the resolver there answers 0 for every symbol.
fn export_dynamically() -> Option<&'static str> {
    let vendor = env::var("CARGO_CFG_TARGET_VENDOR").unwrap_or_default();
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    match (vendor.as_str(), os.as_str()) {
        ("apple", _) => Some("-Wl,-export_dynamic"),
        (_, "linux") => Some("-rdynamic"),
        _ => None,
    }
}

fn main() {
    if let Some(flag) = export_dynamically() {
        println!("cargo:rustc-link-arg={flag}");
    }
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
