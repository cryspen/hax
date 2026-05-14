//! Snapshot tests for the ProVerif backend.
//!
//! Each test runs `cargo hax into proverif` on one of the
//! `tests/proverif-*` crates and compares the produced `lib.pvl` against a
//! committed `expected.pvl` baseline. Run with `INSTA_UPDATE=auto` after
//! intentional changes — wait, we don't use insta, just plain string
//! equality. Diff a failing run to update the baseline.
//!
//! These tests are gated on the env var `HAX_PROVERIF_SNAPSHOT_RUN` so they
//! don't fire by default (they require the full hax toolchain in `PATH`).
//! Run them with:
//!
//! ```bash
//! HAX_PROVERIF_SNAPSHOT_RUN=1 cargo test -p hax-rust-engine --test proverif_snapshot
//! ```

use std::path::PathBuf;
use std::process::Command;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf()
}

/// `proverif-noise` extracts with diagnostics today (unsupported
/// `.concat()` / closures in `map_err`). The file is still produced and
/// is the regression baseline — we just don't require a clean exit.
const ALLOWED_TO_FAIL: &[&str] = &["proverif-noise"];

fn run_one(crate_name: &str) {
    if std::env::var("HAX_PROVERIF_SNAPSHOT_RUN").is_err() {
        eprintln!(
            "Skipping {crate_name}: set HAX_PROVERIF_SNAPSHOT_RUN=1 to run snapshot tests."
        );
        return;
    }
    let crate_dir = workspace_root().join("tests").join(crate_name);
    let proofs = crate_dir.join("proofs");
    let _ = std::fs::remove_dir_all(&proofs);

    let cargo_hax = std::env::var("CARGO_HAX_BIN")
        .unwrap_or_else(|_| "cargo-hax".to_string());
    let mut cmd = Command::new(cargo_hax);
    cmd.current_dir(&crate_dir).args(["into", "proverif"]);
    let output = cmd.output().expect("running cargo-hax");
    if !output.status.success() && !ALLOWED_TO_FAIL.contains(&crate_name) {
        panic!(
            "cargo-hax failed for {crate_name}:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let actual = std::fs::read_to_string(proofs.join("proverif/extraction/lib.pvl"))
        .expect("reading generated lib.pvl");
    let expected_path = crate_dir.join("expected.pvl");
    let expected = std::fs::read_to_string(&expected_path)
        .expect("reading expected.pvl baseline");

    if actual != expected {
        let diff_path = crate_dir.join("actual.pvl");
        std::fs::write(&diff_path, &actual).ok();
        panic!(
            "Snapshot mismatch for {crate_name}.\n  Expected: {}\n  Actual:   {}\n\n\
             Run `diff {} {}` to see the difference.\n\
             If the new output is correct, run `cp {} {}` to update the baseline.",
            expected_path.display(),
            diff_path.display(),
            expected_path.display(),
            diff_path.display(),
            diff_path.display(),
            expected_path.display(),
        );
    }
}

#[test]
fn proverif_minimal() {
    run_one("proverif-minimal");
}

#[test]
fn proverif_basic_structs() {
    run_one("proverif-basic-structs");
}

#[test]
fn proverif_fn_to_letfun() {
    run_one("proverif-fn-to-letfun");
}

#[test]
fn proverif_ping_pong() {
    run_one("proverif-ping-pong");
}

#[test]
fn proverif_noise() {
    run_one("proverif-noise");
}

#[test]
fn proverif_generics() {
    run_one("proverif-generics");
}

#[test]
fn proverif_inline() {
    run_one("proverif-inline");
}
