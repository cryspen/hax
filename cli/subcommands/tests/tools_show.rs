//! End-to-end tests for `cargo hax tools show`: project discovery, the
//! resolution order, and the associated warnings, exercised through the
//! real binary on a temporary Cargo workspace.

use std::fs;
use std::path::Path;
use std::process::Command;

fn write(path: &Path, contents: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, contents).unwrap();
}

/// A workspace with two members: `a` (no overrides) and `b` (overrides
/// charon), a workspace-root `hax.toml` pinning aeneas, and a stray
/// `hax.toml` in a non-crate subdirectory.
fn fixture_workspace() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(
        &root.join("Cargo.toml"),
        r#"[workspace]
members = ["a", "b"]
resolver = "2"
"#,
    );
    for member in ["a", "b"] {
        write(
            &root.join(member).join("Cargo.toml"),
            &format!(
                r#"[package]
name = "{member}"
version = "0.1.0"
edition = "2021"
"#
            ),
        );
        write(&root.join(member).join("src/lib.rs"), "");
    }
    write(
        &root.join("hax.toml"),
        r#"[tools]
aeneas = "nightly-9999.01.01"
"#,
    );
    write(
        &root.join("b/hax.toml"),
        r#"[tools]
charon = "nightly-8888.01.01"
"#,
    );
    write(&root.join("sub/hax.toml"), "");
    fs::create_dir_all(root.join("sub/deeper")).unwrap();
    dir
}

fn run_tools_show(current_dir: &Path, envs: &[(&str, &str)]) -> (String, String, bool) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-hax"));
    cmd.args(["tools", "show"]).current_dir(current_dir);
    for (var, value) in envs {
        cmd.env(var, value);
    }
    for var in ["HAX_AENEAS_BINARY", "HAX_CHARON_BINARY"] {
        if !envs.iter().any(|(v, _)| v == &var) {
            cmd.env_remove(var);
        }
    }
    let output = cmd.output().expect("could not run cargo-hax");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        output.status.success(),
    )
}

#[test]
fn show_reports_pins_defaults_and_member_overrides() {
    let dir = fixture_workspace();
    let (stdout, _stderr, success) = run_tools_show(dir.path(), &[]);
    assert!(success, "tools show failed: {stdout}");

    // Workspace pin, with its source.
    assert!(stdout.contains("nightly-9999.01.01"), "{stdout}");
    assert!(stdout.contains("pinned in"), "{stdout}");
    // Charon has no workspace pin: built-in default.
    assert!(stdout.contains("(default)"), "{stdout}");
    // Declared-only versions are reported.
    assert!(stdout.contains("lean"), "{stdout}");
    // Member `b` diverges, and only its differing tool is reported.
    assert!(stdout.contains("crate `b` (overrides)"), "{stdout}");
    assert!(stdout.contains("nightly-8888.01.01"), "{stdout}");
    // The member-override warning names the crate.
    assert!(
        stdout.contains("`b` overrides the workspace tool configuration"),
        "{stdout}"
    );
}

#[test]
fn env_override_wins() {
    let dir = fixture_workspace();
    let (stdout, _, success) = run_tools_show(
        dir.path(),
        &[("HAX_AENEAS_BINARY", "/opt/aeneas/bin/aeneas")],
    );
    assert!(success);
    assert!(stdout.contains("/opt/aeneas/bin/aeneas"), "{stdout}");
    assert!(stdout.contains("env HAX_AENEAS_BINARY"), "{stdout}");
}

#[test]
fn stray_hax_toml_is_warned_about() {
    let dir = fixture_workspace();
    let (stdout, _, success) = run_tools_show(&dir.path().join("sub/deeper"), &[]);
    assert!(success, "{stdout}");
    assert!(stdout.contains("has no effect and is ignored"), "{stdout}");
    // Invoking from the workspace root itself does not warn.
    let (stdout, _, _) = run_tools_show(dir.path(), &[]);
    assert!(!stdout.contains("has no effect"), "{stdout}");
}

#[test]
fn json_message_format_emits_structured_output() {
    let dir = fixture_workspace();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-hax"));
    cmd.args(["--message-format", "json", "tools", "show"])
        .current_dir(dir.path());
    for var in ["HAX_AENEAS_BINARY", "HAX_CHARON_BINARY"] {
        cmd.env_remove(var);
    }
    let output = cmd.output().unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // The last line is the `show` payload; earlier lines are JSON messages.
    let payload = stdout.lines().last().unwrap();
    let json: serde_json::Value = serde_json::from_str(payload).expect("invalid JSON payload");
    assert_eq!(json["member_overrides"][0]["crate"], serde_json::json!("b"));
    assert_eq!(
        json["member_overrides"][0]["tools"][0]["version"],
        serde_json::json!("nightly-8888.01.01")
    );
}

#[test]
fn malformed_hax_toml_is_a_hard_error() {
    let dir = fixture_workspace();
    write(
        &dir.path().join("hax.toml"),
        r#"[tools]
charon = { version = "x", path = "y" }
"#,
    );
    let (stdout, _, success) = run_tools_show(dir.path(), &[]);
    assert!(!success);
    assert!(stdout.contains("both `version` and `path`"), "{stdout}");
}

#[test]
fn outside_a_cargo_project_fails_with_a_clear_error() {
    let dir = tempfile::tempdir().unwrap();
    let (stdout, _, success) = run_tools_show(dir.path(), &[]);
    assert!(!success);
    assert!(
        stdout.contains("must be run inside a") || stdout.contains("cargo metadata"),
        "{stdout}"
    );
}
