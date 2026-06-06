use std::env::temp_dir;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output, id};
use std::thread::current;

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
    let path = temp_dir().join(format!(
        "fz-interface-dump-{}-{}.fz",
        id(),
        current().name().unwrap_or("test")
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
  fingerprint-digest 801a8be1a8eac35a
  fingerprint-inputs
    abi=1
    module=Math
    type=Id:Opaque:Ident("opaque") Ident("integer")
    fn=add/2:specs=[(Upper("Id"),Upper("Id"))->Upper("Id")]

interface User abi=1
  moduledoc "Uses math."
  imports
    Math only [add/2]
  exports
    calc/2
  fingerprint-digest c1b427894f4a0a21
  fingerprint-inputs
    abi=1
    module=User
    moduledoc=Uses math.
    import=Math:only=[add/2]:except=[]
    fn=calc/2:specs=[<unspecified>]

"#;
    assert_eq!(stdout, expected);
    assert!(
        !stdout.contains("x + y"),
        "interface dump leaked implementation body:\n{}",
        stdout
    );
}

#[test]
fn fz_repl_script_keeps_unknown_modules_out_of_session() {
    let src = r#"
defmodule User do
  import Math, only: [add: 2]
  fn run(), do: add(20, 22)
end

fn main(), do: dbg(User.run())
"#;
    let path = write_temp_fz("fz-repl-no-providers", src);
    let out = Command::new(FZ_BIN)
        .args(["repl", "--script"])
        .arg(&path)
        .output()
        .expect("spawn repl script");
    let _ = fs::remove_file(&path);
    assert!(
        !out.status.success(),
        "repl script unexpectedly resolved missing module"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("resolve/unknown-module") && stderr.contains("module `Math` is not defined"),
        "unexpected repl script stderr: {stderr}"
    );
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
    let path = temp_dir().join(format!("{}-{}-{}.fz", prefix, id(), current().name().unwrap_or("test")));
    fs::write(&path, src).unwrap_or_else(|e| panic!("write {}: {}", path.display(), e));
    path
}

fn dump_interfaces_for_source(src: &str, strict: bool) -> Output {
    let path = temp_dir().join(format!("fz-interface-dump-{}-{}.fz", id(), strict));
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
