//! End-to-end tests for a `cargo-hax` installed on its own, without the
//! frontend driver and the engine next to it, as `cargo install cargo-hax`
//! and tools built on it (e.g. `cargo-run-bin`) produce. The binary under
//! test is copied to a directory of its own, since the driver sits next to
//! it in this repository's build directory.
//!
//! Such an installation supports the `lean` backend, which runs charon and
//! aeneas, and the `tools` subcommands. Everything else needs the driver.

mod common;

use std::path::{Path, PathBuf};

use common::{cargo_hax, command, output_of, write_crate, write_path_entries, write_tool_stubs};

/// A crate to process, with charon and aeneas stubbed out and pinned by a
/// `hax.toml`, so that a `lean` run finishes without the real tools.
fn project() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write_crate(root, "app");
    let stubs = root.join("stubs");
    write_tool_stubs(&stubs);
    write_path_entries(root, &stubs);
    dir
}

/// The binary under test, copied into a directory holding nothing else.
fn standalone_binary(dir: &Path) -> PathBuf {
    let path = dir.join("bin/cargo-hax");
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::copy(cargo_hax(), &path).unwrap();
    path
}

fn run(binary: &Path, args: &[&str], current_dir: &Path) -> (String, bool) {
    output_of(&mut command(binary, args, current_dir))
}

#[test]
fn lean_backend_runs_without_the_driver() {
    let project = project();
    let binary = standalone_binary(project.path());
    let (output, success) = run(&binary, &["into", "lean"], project.path());
    assert!(success, "{output}");
    // The stubs ran: the pipeline went through, rather than exiting early.
    assert!(project.path().join("charon-invoked").is_file(), "{output}");
    assert!(project.path().join("aeneas-invoked").is_file(), "{output}");
}

#[test]
fn other_backends_report_the_missing_driver() {
    let project = project();
    let binary = standalone_binary(project.path());
    let (output, success) = run(&binary, &["into", "fstar"], project.path());
    assert!(!success, "{output}");
    assert!(output.contains("standalone"), "{output}");
    assert!(output.contains("cargo hax into lean"), "{output}");
}
