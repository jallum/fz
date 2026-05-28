use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");

#[test]
fn fz_dump_emits_interfaces() {
    let src = r#"
defmodule Math do
  @type Id :: opaque integer
  @spec add(Id, Id) :: Id
  fn add(x, y), do: x + y
end

defmodule User do
  @moduledoc "Uses math."
  import Math, only: [add: 2]
  fn calc(x, y), do: add(x, y)
end
"#;
    let path = std::env::temp_dir().join(format!(
        "fz-interface-dump-{}-{}.fz",
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    fs::write(&path, src).unwrap_or_else(|e| panic!("write {}: {}", path.display(), e));
    let out = Command::new(FZ_BIN)
        .args(["dump", "--emit", "interfaces"])
        .arg(&path)
        .output()
        .expect("spawn fz dump --emit interfaces");
    let _ = fs::remove_file(&path);
    assert!(
        out.status.success(),
        "fz dump --emit interfaces exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let expected = r#"interface Math abi=1
  types
    Id Opaque = Ident("opaque") Ident("integer")
  exports
    add/2 :: (Upper("Id"), Upper("Id")) -> Upper("Id")
  fingerprint-digest 97353785e9a2097f
  fingerprint-inputs
    abi=1
    module=Math
    type=Id:Opaque:Ident("opaque") Ident("integer")
    fn=add/2:(Upper("Id"),Upper("Id"))->Upper("Id")

interface User abi=1
  moduledoc "Uses math."
  imports
    Math only [add/2]
  exports
    calc/2
  fingerprint-digest 27e57c07ebacf97a
  fingerprint-inputs
    abi=1
    module=User
    moduledoc=Uses math.
    import=Math:only=[add/2]:except=[]
    fn=calc/2:<unspecified>

"#;
    assert_eq!(stdout, expected);
    assert!(
        !stdout.contains("x + y"),
        "interface dump leaked implementation body:\n{}",
        stdout
    );
}

#[test]
fn fz_build_emits_fzi() {
    let src = r#"
defmodule Math do
  @spec id(integer) :: integer
  fn id(x), do: x
end

fn main(), do: Math.id(1)
"#;
    let root = std::env::temp_dir().join(format!("fz-build-fzi-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let input = root.join("input.fz");
    let out_path = root.join("app");
    let artifact_root = root.join("artifacts");
    fs::write(&input, src).unwrap_or_else(|e| panic!("write {}: {}", input.display(), e));

    let out = Command::new(FZ_BIN)
        .args(["build", "--emit-fzi", "--artifact-root"])
        .arg(&artifact_root)
        .arg(&input)
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("spawn fz build --emit-fzi");
    assert!(
        out.status.success(),
        "fz build --emit-fzi exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    let fzi_path = artifact_root.join("interfaces/Math.fzi");
    let fzi = fs::read_to_string(&fzi_path)
        .unwrap_or_else(|e| panic!("read {}: {}", fzi_path.display(), e));
    assert!(fzi.starts_with("fzi\n"), "{fzi}");
    assert!(fzi.contains("\"Math\""), "{fzi}");
    assert!(fzi.contains("\"interface_fingerprint_digest\""), "{fzi}");
    assert!(
        fzi.contains("\"id\"") && fzi.contains("\"arity\": 1"),
        "{fzi}"
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn fz_build_emits_fzo() {
    let src = r#"
defmodule Math do
  @spec id(integer) :: integer
  fn id(x), do: x
end

fn main(), do: Math.id(1)
"#;
    let root = std::env::temp_dir().join(format!("fz-build-fzo-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let input = root.join("input.fz");
    let out_path = root.join("app");
    let artifact_root = root.join("artifacts");
    fs::write(&input, src).unwrap_or_else(|e| panic!("write {}: {}", input.display(), e));

    let out = Command::new(FZ_BIN)
        .args(["build", "--emit-fzi", "--emit-fzo", "--artifact-root"])
        .arg(&artifact_root)
        .arg(&input)
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("spawn fz build --emit-fzo");
    assert!(
        out.status.success(),
        "fz build --emit-fzo exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    let fzo_path = artifact_root.join("objects/Math.fzo");
    let fzo = fs::read_to_string(&fzo_path)
        .unwrap_or_else(|e| panic!("read {}: {}", fzo_path.display(), e));
    assert!(fzo.starts_with("fzo\n"), "{fzo}");
    assert!(fzo.contains("\"Math\""), "{fzo}");
    assert!(fzo.contains("\"format\": \"fz-source-unit-v1\""), "{fzo}");
    assert!(fzo.contains("defmodule Math"), "{fzo}");
    assert!(fzo.contains("\"interface_fingerprint_digest\""), "{fzo}");

    let _ = fs::remove_dir_all(&root);
}

fn write_provider_consumer(root: &Path) -> (PathBuf, PathBuf, PathBuf) {
    let provider = r#"
defmodule Math do
  @spec add(integer, integer) :: integer
  fn add(x, y), do: x + y
end

fn main(), do: Math.add(1, 2)
"#;
    let consumer = r#"
defmodule User do
  import Math, only: [add: 2]
  fn run(), do: add(20, 22)
end

fn main(), do: dbg(User.run())
"#;
    let provider_path = root.join("provider.fz");
    let consumer_path = root.join("consumer.fz");
    let artifact_root = root.join("artifacts");
    fs::write(&provider_path, provider)
        .unwrap_or_else(|e| panic!("write {}: {}", provider_path.display(), e));
    fs::write(&consumer_path, consumer)
        .unwrap_or_else(|e| panic!("write {}: {}", consumer_path.display(), e));
    (provider_path, consumer_path, artifact_root)
}

fn build_provider_artifacts(provider_path: &Path, artifact_root: &Path, out_path: &Path) {
    let out = Command::new(FZ_BIN)
        .args(["build", "--emit-fzi", "--emit-fzo", "--artifact-root"])
        .arg(artifact_root)
        .arg(provider_path)
        .arg("-o")
        .arg(out_path)
        .output()
        .expect("spawn provider artifact build");
    assert!(
        out.status.success(),
        "provider artifact build exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn fz_run_loads_reachable_fzo_after_provider_source_removed() {
    let root = std::env::temp_dir().join(format!("fz-run-load-fzo-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let (provider_path, consumer_path, artifact_root) = write_provider_consumer(&root);
    build_provider_artifacts(&provider_path, &artifact_root, &root.join("provider-app"));
    fs::remove_file(&provider_path)
        .unwrap_or_else(|e| panic!("remove {}: {}", provider_path.display(), e));

    let out = Command::new(FZ_BIN)
        .args(["run", "--interface", "Math", "--artifact-root"])
        .arg(&artifact_root)
        .arg(&consumer_path)
        .output()
        .expect("spawn consumer run");
    assert!(
        out.status.success(),
        "consumer run exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "42");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn fz_build_loads_reachable_fzo_after_provider_source_removed() {
    let root = std::env::temp_dir().join(format!("fz-build-load-fzo-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let (provider_path, consumer_path, artifact_root) = write_provider_consumer(&root);
    build_provider_artifacts(&provider_path, &artifact_root, &root.join("provider-app"));
    fs::remove_file(&provider_path)
        .unwrap_or_else(|e| panic!("remove {}: {}", provider_path.display(), e));

    let app = root.join("consumer-app");
    let build = Command::new(FZ_BIN)
        .args(["build", "--interface", "Math", "--artifact-root"])
        .arg(&artifact_root)
        .arg(&consumer_path)
        .arg("-o")
        .arg(&app)
        .output()
        .expect("spawn consumer build");
    assert!(
        build.status.success(),
        "consumer build exited {}: {}",
        build.status,
        String::from_utf8_lossy(&build.stderr)
    );
    let run = Command::new(&app).output().expect("run built consumer");
    assert!(
        run.status.success(),
        "built consumer exited {}: {}",
        run.status,
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "42");

    let fzo = artifact_root.join("objects/Math.fzo");
    fs::remove_file(&fzo).unwrap_or_else(|e| panic!("remove {}: {}", fzo.display(), e));
    let missing = Command::new(FZ_BIN)
        .args(["run", "--interface", "Math", "--artifact-root"])
        .arg(&artifact_root)
        .arg(&consumer_path)
        .output()
        .expect("spawn missing-fzo consumer run");
    assert!(
        !missing.status.success(),
        "missing fzo run unexpectedly succeeded"
    );
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("Math.fzo"),
        "{}",
        String::from_utf8_lossy(&missing.stderr)
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn fz_build_emits_fzo_for_module_with_artifact_imports() {
    let provider = r#"
defmodule Math do
  @spec add(integer, integer) :: integer
  fn add(x, y), do: x + y
end

fn main(), do: Math.add(1, 2)
"#;
    let consumer = r#"
defmodule User do
  import Math, only: [add: 2]

  @spec run() :: integer
  fn run(), do: add(20, 22)
end

fn main(), do: dbg(User.run())
"#;
    let root = std::env::temp_dir().join(format!("fz-build-imported-fzo-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let provider_path = root.join("provider.fz");
    let consumer_path = root.join("consumer.fz");
    let artifact_root = root.join("artifacts");
    fs::write(&provider_path, provider)
        .unwrap_or_else(|e| panic!("write {}: {}", provider_path.display(), e));
    fs::write(&consumer_path, consumer)
        .unwrap_or_else(|e| panic!("write {}: {}", consumer_path.display(), e));
    build_provider_artifacts(&provider_path, &artifact_root, &root.join("provider-app"));

    let out = Command::new(FZ_BIN)
        .args([
            "build",
            "--emit-fzi",
            "--emit-fzo",
            "--interface",
            "Math",
            "--artifact-root",
        ])
        .arg(&artifact_root)
        .arg(&consumer_path)
        .arg("-o")
        .arg(root.join("consumer-app"))
        .output()
        .expect("spawn consumer artifact build");
    assert!(
        out.status.success(),
        "consumer artifact build exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    let fzo_path = artifact_root.join("objects/User.fzo");
    let fzo = fs::read_to_string(&fzo_path)
        .unwrap_or_else(|e| panic!("read {}: {}", fzo_path.display(), e));
    assert!(fzo.contains("\"User\""), "{fzo}");
    assert!(fzo.contains("\"format\": \"fz-source-unit-v1\""), "{fzo}");
    assert!(
        fzo.contains("\"add\"") && fzo.contains("\"arity\": 2"),
        "{fzo}"
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn fz_repl_script_keeps_module_artifacts_out_of_session() {
    let root = std::env::temp_dir().join(format!("fz-repl-no-artifacts-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let (provider_path, consumer_path, artifact_root) = write_provider_consumer(&root);
    build_provider_artifacts(&provider_path, &artifact_root, &root.join("provider-app"));
    fs::remove_file(&provider_path)
        .unwrap_or_else(|e| panic!("remove {}: {}", provider_path.display(), e));

    let out = Command::new(FZ_BIN)
        .args(["repl", "--script"])
        .arg(&consumer_path)
        .output()
        .expect("spawn repl script");
    assert!(
        !out.status.success(),
        "repl script unexpectedly loaded module artifacts"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("resolve/unknown-module")
            && stderr.contains("module `Math` is not defined"),
        "unexpected repl script stderr: {stderr}"
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn fz_build_emit_fzi_requires_public_specs() {
    let src = r#"
defmodule Public do
  fn missing(x), do: x
end

fn main(), do: Public.missing(1)
"#;
    let root = std::env::temp_dir().join(format!("fz-build-fzi-strict-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let input = root.join("input.fz");
    let out_path = root.join("app");
    let artifact_root = root.join("artifacts");
    fs::write(&input, src).unwrap_or_else(|e| panic!("write {}: {}", input.display(), e));

    let out = Command::new(FZ_BIN)
        .args(["build", "--emit-fzi", "--artifact-root"])
        .arg(&artifact_root)
        .arg(&input)
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("spawn fz build --emit-fzi missing specs");
    assert!(
        !out.status.success(),
        "fz build --emit-fzi should reject missing public specs"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("interface/missing-spec"), "{stderr}");
    assert!(!artifact_root.join("interfaces/Public.fzi").exists());

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn fz_dump_loads_fzi_for_imports() {
    let provider = r#"
defmodule Math do
  @spec add(integer, integer) :: integer
  fn add(x, y), do: x + y
end

fn main(), do: Math.add(1, 2)
"#;
    let consumer = r#"
defmodule User do
  import Math, only: [add: 2]
  @spec run(integer, integer) :: integer
  fn run(x, y), do: x + y
end
"#;
    let root = std::env::temp_dir().join(format!("fz-dump-load-fzi-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap_or_else(|e| panic!("mkdir {}: {}", root.display(), e));
    let provider_path = root.join("provider.fz");
    let consumer_path = root.join("consumer.fz");
    let out_path = root.join("provider-app");
    let artifact_root = root.join("artifacts");
    fs::write(&provider_path, provider)
        .unwrap_or_else(|e| panic!("write {}: {}", provider_path.display(), e));
    fs::write(&consumer_path, consumer)
        .unwrap_or_else(|e| panic!("write {}: {}", consumer_path.display(), e));

    let build = Command::new(FZ_BIN)
        .args(["build", "--emit-fzi", "--artifact-root"])
        .arg(&artifact_root)
        .arg(&provider_path)
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("spawn provider fzi build");
    assert!(
        build.status.success(),
        "provider fzi build exited {}: {}",
        build.status,
        String::from_utf8_lossy(&build.stderr)
    );
    fs::remove_file(&provider_path)
        .unwrap_or_else(|e| panic!("remove {}: {}", provider_path.display(), e));

    let dump = Command::new(FZ_BIN)
        .args([
            "dump",
            "--emit",
            "interfaces",
            "--interface",
            "Math",
            "--artifact-root",
        ])
        .arg(&artifact_root)
        .arg(&consumer_path)
        .output()
        .expect("spawn consumer interface dump");
    assert!(
        dump.status.success(),
        "consumer interface dump exited {}: {}",
        dump.status,
        String::from_utf8_lossy(&dump.stderr)
    );
    let stdout = String::from_utf8_lossy(&dump.stdout);
    assert!(stdout.contains("interface User abi=1"), "{stdout}");
    assert!(stdout.contains("Math only [add/2]"), "{stdout}");
    assert!(
        !stdout.contains("interface Math abi=1"),
        "consumer dump should not need provider source/interface as local output:\n{stdout}"
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn fz_dump_strict_interfaces_requires_public_specs() {
    let missing = r#"
fn helper(x), do: x

defmodule Public do
  fn missing(x), do: helper(x)
end
"#;
    let out = dump_interfaces_for_source(missing, true);
    assert!(
        !out.status.success(),
        "strict interface dump should reject missing public @spec"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("interface/missing-spec"), "{stderr}");
    assert!(stderr.contains("Public`.`missing/1"), "{stderr}");

    let specified = r#"
fn helper(x), do: x

defmodule Public do
  @spec f(integer) :: integer
  fn f(x), do: helper(x)
end
"#;
    let out = dump_interfaces_for_source(specified, true);
    assert!(
        out.status.success(),
        "strict interface dump should allow specified public exports: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn fz_dump_lto_erases_cross_module_boundary() {
    let missing_spec = r#"
defmodule Math do
  fn add(x, y), do: x + y
end

fn main(), do: Math.add(20, 22)
"#;
    let missing = write_temp_fz("fz-lto-missing-spec", missing_spec);
    let missing_out = Command::new(FZ_BIN)
        .args(["dump", "--lto", "--emit", "bodies"])
        .arg(&missing)
        .output()
        .expect("spawn fz dump --lto --emit bodies missing spec");
    let _ = fs::remove_file(&missing);
    assert!(
        !missing_out.status.success(),
        "LTO should validate public interfaces before optimization"
    );
    assert!(
        String::from_utf8_lossy(&missing_out.stderr).contains("interface/missing-spec"),
        "{}",
        String::from_utf8_lossy(&missing_out.stderr)
    );

    let src = r#"
defmodule Math do
  @spec add(integer, integer) :: integer
  fn add(x, y), do: x + y
end

fn main(), do: Math.add(20, 22)
"#;
    let path = write_temp_fz("fz-lto-dump", src);
    let out = Command::new(FZ_BIN)
        .args(["dump", "--lto", "--emit", "bodies"])
        .arg(&path)
        .output()
        .expect("spawn fz dump --lto --emit bodies");
    let _ = fs::remove_file(&path);
    assert!(
        out.status.success(),
        "fz dump --lto --emit bodies exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("bodies emitted: 0 user functions"),
        "LTO should let reducer erase the cross-module call:\n{}",
        stdout
    );
}

fn write_temp_fz(prefix: &str, src: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "{}-{}-{}.fz",
        prefix,
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    fs::write(&path, src).unwrap_or_else(|e| panic!("write {}: {}", path.display(), e));
    path
}

fn dump_interfaces_for_source(src: &str, strict: bool) -> std::process::Output {
    let path = std::env::temp_dir().join(format!(
        "fz-interface-dump-{}-{}.fz",
        std::process::id(),
        strict
    ));
    fs::write(&path, src).unwrap_or_else(|e| panic!("write {}: {}", path.display(), e));
    let mut cmd = Command::new(FZ_BIN);
    cmd.args(["dump", "--emit", "interfaces"]);
    if strict {
        cmd.arg("--strict-interfaces");
    }
    let out = cmd.arg(&path).output().expect("spawn fz dump interfaces");
    let _ = fs::remove_file(&path);
    out
}
