//! End-to-end tests for the `hax-lib` compatibility check: fixture
//! workspaces depend on a local fake `hax-lib` package whose version is
//! chosen per test, and the real binary is run against them.
//!
//! The test binary shares `CARGO_PKG_VERSION` with `cargo-hax`, so the
//! binary's own version (the upper bound of the accepted range) is
//! available as `env!("CARGO_PKG_VERSION")`.

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;

const OWN_VERSION: &str = env!("CARGO_PKG_VERSION");

fn write(path: &Path, contents: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, contents).unwrap();
}

/// A workspace with an `app` crate and a fake local `hax-lib` at the
/// given version. `direct` controls whether `app` depends on it directly
/// or through an intermediate `shim` crate.
fn fixture(hax_lib_version: &str, direct: bool) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let members = if direct {
        r#"["app", "hax-lib"]"#
    } else {
        r#"["app", "shim", "hax-lib"]"#
    };
    write(
        &root.join("Cargo.toml"),
        &format!("[workspace]\nmembers = {members}\nresolver = \"2\"\n"),
    );
    write(
        &root.join("hax-lib/Cargo.toml"),
        &format!(
            "[package]\nname = \"hax-lib\"\nversion = \"{hax_lib_version}\"\nedition = \"2021\"\n"
        ),
    );
    write(&root.join("hax-lib/src/lib.rs"), "");
    let app_dep = if direct {
        "hax-lib = { path = \"../hax-lib\" }"
    } else {
        "shim = { path = \"../shim\" }"
    };
    write(
        &root.join("app/Cargo.toml"),
        &format!(
            "[package]\nname = \"app\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
             [dependencies]\n{app_dep}\n"
        ),
    );
    write(&root.join("app/src/lib.rs"), "");
    if !direct {
        write(
            &root.join("shim/Cargo.toml"),
            "[package]\nname = \"shim\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
             [dependencies]\nhax-lib = { path = \"../hax-lib\" }\n",
        );
        write(&root.join("shim/src/lib.rs"), "");
    }
    dir
}

fn run(args: &[&str], current_dir: &Path, envs: &[(&str, &str)]) -> (String, bool) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-hax"));
    cmd.args(args).current_dir(current_dir);
    for var in [
        "HAX_AENEAS_BINARY",
        "HAX_CHARON_BINARY",
        "HAX_TOOLS_MANIFEST",
    ] {
        cmd.env_remove(var);
    }
    for (var, value) in envs {
        cmd.env(var, value);
    }
    let output = cmd.output().unwrap();
    (
        format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
        output.status.success(),
    )
}

/// Stub charon/aeneas binaries, to let an `into lean` run finish
/// without real tools.
fn stub_tools(dir: &Path) -> [(&'static str, String); 2] {
    for name in ["charon", "charon-driver", "aeneas"] {
        let path = dir.join(name);
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(&path, "#!/bin/sh\nexit 0\n").unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
    [
        (
            "HAX_CHARON_BINARY",
            dir.join("charon").display().to_string(),
        ),
        (
            "HAX_AENEAS_BINARY",
            dir.join("aeneas").display().to_string(),
        ),
    ]
}

#[test]
fn too_old_hax_lib_aborts_before_processing() {
    let project = fixture("0.2.0", true);
    let (output, success) = run(&["json"], project.path(), &[]);
    assert!(!success);
    assert!(
        output.contains("incompatible `hax-lib` version"),
        "{output}"
    );
    assert!(output.contains("found hax-lib 0.2.0"), "{output}");
    assert!(output.contains("crate `app`"), "{output}");
    assert!(
        output.contains("update the `hax-lib` dependency"),
        "{output}"
    );
}

#[test]
fn newer_hax_lib_suggests_updating_cargo_hax() {
    let own = semver_parts(OWN_VERSION);
    let newer = format!("{}.{}.{}", own.0, own.1, own.2 + 1);
    let project = fixture(&newer, true);
    let (output, success) = run(&["json"], project.path(), &[]);
    assert!(!success);
    assert!(
        output.contains(&format!("found hax-lib {newer}")),
        "{output}"
    );
    assert!(output.contains("update cargo-hax"), "{output}");
}

#[test]
fn transitive_only_hax_lib_is_ignored() {
    let project = fixture("0.2.0", false);
    let stubs_dir: PathBuf = project.path().join("stubs");
    let envs = stub_tools(&stubs_dir);
    let envs: Vec<(&str, &str)> = envs.iter().map(|(k, v)| (*k, v.as_str())).collect();
    // The incompatible hax-lib is only a transitive dependency: the
    // check is skipped and the pipeline runs.
    let (output, success) = run(&["into", "lean"], &project.path().join("app"), &envs);
    assert!(success, "{output}");
    assert!(!output.contains("incompatible"), "{output}");
}

#[test]
fn compatible_hax_lib_passes_and_is_reported_by_show() {
    let project = fixture(OWN_VERSION, true);
    let stubs_dir: PathBuf = project.path().join("stubs");
    let envs = stub_tools(&stubs_dir);
    let envs: Vec<(&str, &str)> = envs.iter().map(|(k, v)| (*k, v.as_str())).collect();
    let (output, success) = run(&["into", "lean"], &project.path().join("app"), &envs);
    assert!(success, "{output}");

    let (output, success) = run(&["tools", "show"], project.path(), &[]);
    assert!(success, "{output}");
    assert!(output.contains("libraries:"), "{output}");
    // The `hax-lib` row reports the resolved version and its status.
    assert!(output.contains("hax-lib"), "{output}");
    assert!(output.contains(OWN_VERSION), "{output}");
    assert!(output.contains("(compatible)"), "{output}");
}

#[test]
fn tools_subcommands_never_gate_on_incompatibility() {
    let project = fixture("0.2.0", true);
    // `tools show` reports the incompatibility instead of failing.
    let (output, success) = run(&["tools", "show"], project.path(), &[]);
    assert!(success, "{output}");
    assert!(output.contains("INCOMPATIBLE"), "{output}");
    // `tools list` is unaffected.
    let (_, success) = run(&["tools", "list"], project.path(), &[]);
    assert!(success);
}

#[test]
fn no_hax_lib_dependency_skips_the_check() {
    let project = fixture("0.2.0", true);
    // Remove the dependency: no processed crate depends on hax-lib.
    write(
        &project.path().join("app/Cargo.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    );
    let stubs_dir: PathBuf = project.path().join("stubs");
    let envs = stub_tools(&stubs_dir);
    let envs: Vec<(&str, &str)> = envs.iter().map(|(k, v)| (*k, v.as_str())).collect();
    let (output, success) = run(&["into", "lean"], &project.path().join("app"), &envs);
    assert!(success, "{output}");
}

#[test]
fn dev_dependency_hax_lib_is_ignored() {
    // `app` depends on an incompatible `hax-lib`, but only as a
    // dev-dependency: it is not what `app`'s annotations compile against,
    // so the check must not gate on it.
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(
        &root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"app\", \"hax-lib\"]\nresolver = \"2\"\n",
    );
    write(
        &root.join("hax-lib/Cargo.toml"),
        "[package]\nname = \"hax-lib\"\nversion = \"0.2.0\"\nedition = \"2021\"\n",
    );
    write(&root.join("hax-lib/src/lib.rs"), "");
    write(
        &root.join("app/Cargo.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
         [dev-dependencies]\nhax-lib = { path = \"../hax-lib\" }\n",
    );
    write(&root.join("app/src/lib.rs"), "");

    let stubs_dir: PathBuf = root.join("stubs");
    let envs = stub_tools(&stubs_dir);
    let envs: Vec<(&str, &str)> = envs.iter().map(|(k, v)| (*k, v.as_str())).collect();
    let (output, success) = run(&["into", "lean"], &root.join("app"), &envs);
    assert!(success, "{output}");
    assert!(!output.contains("incompatible"), "{output}");
}

fn semver_parts(version: &str) -> (u64, u64, u64) {
    let mut parts = version.splitn(3, '.');
    let mut next = || {
        parts
            .next()
            .unwrap()
            .split(['-', '+'])
            .next()
            .unwrap()
            .parse()
            .unwrap()
    };
    (next(), next(), next())
}
