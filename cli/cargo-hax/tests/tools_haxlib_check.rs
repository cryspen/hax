//! End-to-end tests for the `hax-lib` compatibility check: fixture
//! workspaces depend on a local fake `hax-lib` package whose version is
//! chosen per test, and the real binary is run against them.
//!
//! The test binary shares `CARGO_PKG_VERSION` with `cargo-hax`, so the
//! binary's own version (the one `hax-lib` version it accepts) is
//! available as `env!("CARGO_PKG_VERSION")`.

mod common;

use std::path::Path;

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

fn run(args: &[&str], current_dir: &Path) -> (String, bool) {
    common::run_hax(args, current_dir, &[])
}

/// Stub charon/aeneas binaries under `<root>/stubs`, pointed at by a
/// workspace-root `hax.toml`, to let an `into lean` run finish without real
/// tools.
fn stub_tools(root: &Path) {
    let dir = root.join("stubs");
    common::stub_pipeline_tools(&dir, &common::stub("aeneas-invoked"));
    write(&root.join("hax.toml"), &common::path_entries(&dir));
}

#[test]
fn too_old_hax_lib_aborts_before_processing() {
    let project = fixture("0.2.0", true);
    let (output, success) = run(&["json"], project.path());
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
fn older_same_series_hax_lib_is_rejected() {
    let own = semver_parts(OWN_VERSION);
    let older = if own.2 > 0 {
        format!("{}.{}.{}", own.0, own.1, own.2 - 1)
    } else if own.1 > 0 {
        format!("{}.{}.0", own.0, own.1 - 1)
    } else {
        format!("{}.0.0", own.0 - 1)
    };
    let project = fixture(&older, true);
    let (output, success) = run(&["json"], project.path());
    assert!(!success);
    assert!(
        output.contains(&format!("found hax-lib {older}")),
        "{output}"
    );
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
    let (output, success) = run(&["json"], project.path());
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
    stub_tools(project.path());
    // The incompatible hax-lib is only a transitive dependency: the
    // check is skipped and the pipeline runs.
    let (output, success) = run(&["into", "lean"], &project.path().join("app"));
    assert!(success, "{output}");
    assert!(!output.contains("incompatible"), "{output}");
}

#[test]
fn compatible_hax_lib_passes_and_is_reported_by_show() {
    let project = fixture(OWN_VERSION, true);
    stub_tools(project.path());
    let (output, success) = run(&["into", "lean"], &project.path().join("app"));
    assert!(success, "{output}");

    let (output, success) = run(&["tools", "show"], project.path());
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
    let (output, success) = run(&["tools", "show"], project.path());
    assert!(success, "{output}");
    assert!(output.contains("INCOMPATIBLE"), "{output}");
    // `tools list` is unaffected.
    let (_, success) = run(&["tools", "list"], project.path());
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
    stub_tools(project.path());
    let (output, success) = run(&["into", "lean"], &project.path().join("app"));
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

    stub_tools(root);
    let (output, success) = run(&["into", "lean"], &root.join("app"));
    assert!(success, "{output}");
    assert!(!output.contains("incompatible"), "{output}");
}

/// A virtual workspace at `<root>/ws` with a compatible `app` and a
/// `legacy` member still on `hax-lib` 0.2.0. `legacy`'s `hax-lib` sits
/// outside the workspace directory, so that both versions can coexist.
fn mixed_workspace() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(
        &root.join("ws/Cargo.toml"),
        "[workspace]\nmembers = [\"app\", \"legacy\", \"hax-lib\"]\nresolver = \"2\"\n",
    );
    write(
        &root.join("ws/hax-lib/Cargo.toml"),
        &format!(
            "[package]\nname = \"hax-lib\"\nversion = \"{OWN_VERSION}\"\nedition = \"2021\"\n"
        ),
    );
    write(&root.join("ws/hax-lib/src/lib.rs"), "");
    write(
        &root.join("old/hax-lib/Cargo.toml"),
        "[package]\nname = \"hax-lib\"\nversion = \"0.2.0\"\nedition = \"2021\"\n",
    );
    write(&root.join("old/hax-lib/src/lib.rs"), "");
    for (member, hax_lib) in [("app", "../hax-lib"), ("legacy", "../../old/hax-lib")] {
        write(
            &root.join(format!("ws/{member}/Cargo.toml")),
            &format!(
                "[package]\nname = \"{member}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
                 [dependencies]\nhax-lib = {{ path = \"{hax_lib}\" }}\n"
            ),
        );
        write(&root.join(format!("ws/{member}/src/lib.rs")), "");
    }
    stub_tools(&root.join("ws"));
    dir
}

#[test]
fn a_package_selection_is_not_second_guessed() {
    let project = mixed_workspace();
    let ws = project.path().join("ws");

    // No selection: every member of the virtual workspace is processed, so
    // `legacy`'s incompatible `hax-lib` aborts the run.
    let (output, success) = run(&["json"], &ws);
    assert!(!success, "{output}");
    assert!(output.contains("crate `legacy`"), "{output}");

    // With a selection, hax does not guess which members Cargo compiles:
    // `app` is on a compatible `hax-lib`, so no selection is known to hit
    // the incompatible one and the gate lets the run proceed. (It then
    // stops at the Lean package-name derivation, which needs a root
    // package the virtual workspace does not have.)
    for flags in [
        vec!["-C", "-p", "app", ";"],
        vec!["-C", "--package=legacy", ";"],
        vec!["-C", "--workspace", "--exclude", "legacy", ";"],
    ] {
        let args = [flags.as_slice(), &["into", "lean"]].concat();
        let (output, _) = run(&args, &ws);
        assert!(!output.contains("incompatible"), "{flags:?}: {output}");
        assert!(output.contains("no root package"), "{flags:?}: {output}");
    }
}

#[test]
fn a_selection_no_crate_can_dodge_still_aborts() {
    // Every member of this workspace is on the incompatible `hax-lib`, so
    // whichever ones `-p` selects, the run cannot proceed.
    let project = fixture("0.2.0", true);
    let (output, success) = run(&["-C", "-p", "app", ";", "json"], project.path());
    assert!(!success, "{output}");
    assert!(output.contains("crate `app`"), "{output}");
}

#[test]
fn manifest_path_selects_the_project_from_outside_it() {
    let project = mixed_workspace();
    let ws = project.path().join("ws");
    // Run from a directory that is no Cargo project at all: the manifest
    // given with `-C` is what discovery must use.
    let elsewhere = tempfile::tempdir().unwrap();
    let manifest = ws.join("app/Cargo.toml");
    let (output, success) = run(
        &[
            "-C",
            "--manifest-path",
            manifest.to_str().unwrap(),
            ";",
            "into",
            "lean",
        ],
        elsewhere.path(),
    );
    assert!(success, "{output}");
    // The workspace-root `hax.toml` was found (its stub tools were used)
    // and the output went to the crate the manifest names.
    assert!(ws.join("app/proofs/lean").is_dir(), "{output}");
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
