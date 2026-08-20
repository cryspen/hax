//! End-to-end tests for `cargo hax extract`: scope resolution, dry-run
//! output, the compiled charon flags, per-scenario environments, and the
//! failure summary, exercised through the real binary with stub
//! charon/aeneas executables.

mod common;

use std::path::Path;

/// A charon stub that records its invocation and fails when the
/// environment says so, to exercise per-scenario `env` and the failure
/// summary.
const CHARON_STUB: &str = "#!/bin/sh\n\
    if [ -n \"$SCENARIO_FAIL\" ]; then exit 1; fi\n\
    echo \"$@\" > charon-invoked\n\
    exit 0\n";

/// The stub pipeline, with a charon that honors `$SCENARIO_FAIL`.
fn stub_tools(bin: &Path) {
    common::stub_pipeline_tools(bin, &common::stub("aeneas-invoked"));
    common::write_executable(&bin.join("charon"), CHARON_STUB);
}

/// A crate with stub tools and the given extra `hax.toml` contents.
fn write_project(dir: &Path, extra_hax_toml: &str) -> std::path::PathBuf {
    let crate_dir = dir.join("crate");
    common::write_crate(&crate_dir, "fixture");
    let bin = dir.join("bin");
    stub_tools(&bin);
    std::fs::write(
        crate_dir.join("hax.toml"),
        format!("{}{extra_hax_toml}", common::path_entries(&bin)),
    )
    .unwrap();
    crate_dir
}

fn extract(args: &[&str], dir: &Path) -> (String, bool) {
    let mut full = vec!["extract"];
    full.extend(args);
    common::run_hax(&full, dir, &[])
}

#[test]
fn a_lean_scenario_extracts_into_its_own_directory() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(
        dir.path(),
        "[scenario.demo]\n\
         backend = \"lean\"\n\
         include = [\"fixture::main\"]\n\
         opaque = [\"{impl tls_codec::Size for _}\"]\n",
    );

    let (output, success) = extract(&[], &crate_dir);
    assert!(success, "{output}");
    assert!(output.contains("scenario `demo`"), "{output}");
    // The charon invocation carries the compiled selection flags and the
    // inherited default opaque set before the scenario's own patterns.
    let invocation = std::fs::read_to_string(crate_dir.join("charon-invoked")).unwrap();
    assert!(
        invocation.contains("--start-from=fixture::main"),
        "{invocation}"
    );
    assert!(
        invocation.contains("--opaque={impl serde::ser::Serialize for _}"),
        "{invocation}"
    );
    assert!(
        invocation.contains("--opaque={impl tls_codec::Size for _}"),
        "{invocation}"
    );
    // The Lean package is scaffolded under `proofs/<scenario>/lean` and
    // named after the scenario.
    let lean_dir = crate_dir.join("proofs/demo/lean");
    assert!(lean_dir.join("lakefile.toml").is_file(), "{output}");
    assert!(
        lean_dir
            .join("Demo/Verification/ProofObligations.lean")
            .is_file()
    );
    assert!(
        std::fs::read_to_string(lean_dir.join("lakefile.toml"))
            .unwrap()
            .contains("name = \"Demo\"")
    );
    assert!(output.contains("1 scenario extracted"), "{output}");
}

#[test]
fn dry_run_prints_the_resolved_invocations_and_runs_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(
        dir.path(),
        "[scenario.demo]\n\
         backend = \"lean\"\n\
         default-opaques = false\n\
         charon-args = [\"--rare flag\"]\n\
         env = { HAX_TEST_VAR = \"1\" }\n\
         \n\
         [scenario.book]\n\
         backend = \"fstar\"\n\
         select-clauses = [\"-**\", \"+**::process\"]\n\
         z3rlimit = 100\n",
    );

    let (output, success) = extract(&["--dry-run"], &crate_dir);
    assert!(success, "{output}");
    assert!(
        output.contains("scenario `demo` (package `fixture`):"),
        "{output}"
    );
    assert!(output.contains("backend: lean"), "{output}");
    assert!(output.contains("lean package: Demo"), "{output}");
    // Verbatim arguments are quoted for display, and the opt-out drops the
    // default opaque set.
    assert!(output.contains("charon args: '--rare flag'"), "{output}");
    assert!(!output.contains("--opaque"), "{output}");
    assert!(output.contains("env: HAX_TEST_VAR=1"), "{output}");
    assert!(
        output.contains("scenario `book` (package `fixture`):"),
        "{output}"
    );
    assert!(output.contains("--z3rlimit=100"), "{output}");
    assert!(output.contains("-i '-**' '+**::process'"), "{output}");
    // The engine backends write below an `extraction/` subdirectory, and
    // the printed output-dir is where the files actually land.
    assert!(
        output.contains(&format!(
            "output-dir: {}",
            crate_dir.join("proofs/book/fstar/extraction").display()
        )),
        "{output}"
    );
    // Nothing ran.
    assert!(!crate_dir.join("charon-invoked").exists());
    assert!(!crate_dir.join("proofs").exists());
}

#[test]
fn an_empty_scope_and_an_unknown_name_fail_loudly() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(dir.path(), "");

    let (output, success) = extract(&[], &crate_dir);
    assert!(!success);
    assert!(output.contains("no scenarios in scope"), "{output}");
    assert!(output.contains("[scenario.<name>]"), "{output}");

    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(dir.path(), "[scenario.demo]\nbackend = \"lean\"\n");
    let (output, success) = extract(&["demol"], &crate_dir);
    assert!(!success);
    assert!(output.contains("no scenario named `demol`"), "{output}");
    assert!(output.contains("demo"), "{output}");
    assert!(!crate_dir.join("charon-invoked").exists());
}

#[test]
fn a_repeated_name_runs_the_scenario_once() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(dir.path(), "[scenario.demo]\nbackend = \"lean\"\n");

    let (output, success) = extract(&["demo", "demo"], &crate_dir);
    assert!(success, "{output}");
    assert!(output.contains("1 scenario extracted"), "{output}");
}

#[test]
fn failures_are_collected_and_summarized() {
    let dir = tempfile::tempdir().unwrap();
    // `bad` fails through its scenario environment, which doubles as the
    // check that `env` entries reach the spawned tools.
    let crate_dir = write_project(
        dir.path(),
        "[scenario.good]\n\
         backend = \"lean\"\n\
         \n\
         [scenario.bad]\n\
         backend = \"lean\"\n\
         env = { SCENARIO_FAIL = \"1\" }\n",
    );

    let (output, success) = extract(&[], &crate_dir);
    assert!(!success, "{output}");
    // The failing scenario did not abort the run: the good one extracted.
    assert!(
        crate_dir.join("proofs/good/lean/lakefile.toml").is_file(),
        "{output}"
    );
    assert!(output.contains("1 of 2 scenarios failed"), "{output}");
    assert!(output.contains("bad (package `fixture`)"), "{output}");
}

#[test]
fn workspace_scenarios_resolve_packages_and_members_shadow() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().join("ws");
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"a\", \"b\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    common::write_crate(&root.join("a"), "a");
    common::write_crate(&root.join("b"), "b");
    let bin = dir.path().join("bin");
    stub_tools(&bin);

    // A workspace-level scenario in a multi-member workspace needs a
    // `package`.
    std::fs::write(
        root.join("hax.toml"),
        format!(
            "{}[scenario.demo]\nbackend = \"lean\"\n",
            common::path_entries(&bin)
        ),
    )
    .unwrap();
    let (output, success) = extract(&["--dry-run"], &root);
    assert!(!success);
    assert!(output.contains("needs a `package` key"), "{output}");

    // With packages resolved, `-p` narrows the scope, and a member-level
    // scenario shadows the same-named workspace-level one.
    std::fs::write(
        root.join("hax.toml"),
        format!(
            "{}[scenario.demo]\nbackend = \"lean\"\npackage = \"a\"\n",
            common::path_entries(&bin)
        ),
    )
    .unwrap();
    std::fs::write(
        root.join("b/hax.toml"),
        "[scenario.demo]\nbackend = \"lean\"\n",
    )
    .unwrap();
    let (output, success) = extract(&["--dry-run"], &root);
    assert!(success, "{output}");
    assert!(output.contains("is shadowed by"), "{output}");
    assert!(output.contains("(package `b`)"), "{output}");
    assert!(!output.contains("(package `a`)"), "{output}");

    let (output, success) = extract(&["--dry-run", "-p", "a"], &root);
    assert!(!success, "{output}");
    assert!(output.contains("no scenarios in scope"), "{output}");

    // From inside a member, only that member's scope is visible.
    let (output, success) = extract(&["--dry-run"], &root.join("b"));
    assert!(success, "{output}");
    assert!(output.contains("(package `b`)"), "{output}");
}

#[test]
fn colliding_output_directories_abort_before_anything_runs() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(
        dir.path(),
        "[scenario.one]\n\
         backend = \"lean\"\n\
         output-dir = \"proofs/shared\"\n\
         \n\
         [scenario.two]\n\
         backend = \"lean\"\n\
         output-dir = \"proofs/shared/nested\"\n",
    );

    let (output, success) = extract(&[], &crate_dir);
    assert!(!success);
    assert!(output.contains("lies inside"), "{output}");
    assert!(!crate_dir.join("charon-invoked").exists());
}

#[test]
fn narrowed_runs_still_detect_collisions_across_packages() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().join("ws");
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"a\", \"b\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    common::write_crate(&root.join("a"), "a");
    common::write_crate(&root.join("b"), "b");
    for member in ["a", "b"] {
        std::fs::write(
            root.join(member).join("hax.toml"),
            format!("[scenario.{member}1]\nbackend = \"lean\"\noutput-dir = \"../shared\"\n"),
        )
        .unwrap();
    }

    // `-p` narrows what runs, not what is checked: the collision with the
    // filtered-out scenario of the other package still aborts.
    let (output, success) = extract(&["--dry-run", "-p", "a"], &root);
    assert!(!success);
    assert!(output.contains("same output directory"), "{output}");

    // The invocation directory narrows the scope the same way `-p` does,
    // and the collision is still detected.
    let (output, success) = extract(&["--dry-run"], &root.join("a"));
    assert!(!success);
    assert!(output.contains("same output directory"), "{output}");
}

#[test]
fn hermeticity_flags_reach_every_cargo_invocation() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(dir.path(), "[scenario.demo]\nbackend = \"lean\"\n");

    // Without a lockfile, `--frozen` fails the initial discovery: the
    // flags apply from the very first cargo invocation.
    let (output, success) = extract(&["--frozen"], &crate_dir);
    assert!(!success, "{output}");
    assert!(!crate_dir.join("charon-invoked").exists());

    std::fs::write(
        crate_dir.join("Cargo.lock"),
        "version = 3\n\n[[package]]\nname = \"fixture\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let (output, success) = extract(&["--dry-run", "--locked", "--offline"], &crate_dir);
    assert!(success, "{output}");
    assert!(
        output.contains("cargo args: -p fixture --locked --offline"),
        "{output}"
    );
    assert!(
        output.contains("charon cargo args: --locked --offline"),
        "{output}"
    );

    // The cargo invocation charon drives receives the flags too.
    let (output, success) = extract(&["--locked", "--offline"], &crate_dir);
    assert!(success, "{output}");
    let invocation = std::fs::read_to_string(crate_dir.join("charon-invoked")).unwrap();
    assert!(invocation.contains("--locked --offline"), "{invocation}");
}

#[test]
fn cargo_flags_do_not_apply_to_extract() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(dir.path(), "[scenario.demo]\nbackend = \"lean\"\n");

    let (output, success) = common::run_hax(&["-C", "--offline", ";", "extract"], &crate_dir, &[]);
    assert!(!success);
    assert!(output.contains("does not apply to `extract`"), "{output}");
    assert!(!crate_dir.join("charon-invoked").exists());
}

#[test]
fn a_scenario_layout_override_is_blamed_on_the_scenario() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(
        dir.path(),
        "[scenario.demo]\n\
         backend = \"lean\"\n\
         aeneas-args = [\"-dest\", \"elsewhere\"]\n",
    );

    let (output, success) = extract(&[], &crate_dir);
    assert!(success, "{output}");
    assert!(
        output.contains("the scenario's `aeneas-args` overrides -dest"),
        "{output}"
    );
    assert!(!output.contains("--aeneas-args overrides"), "{output}");
}

#[test]
fn full_scope_runs_warn_about_orphaned_scenario_directories() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = write_project(dir.path(), "[scenario.demo]\nbackend = \"lean\"\n");
    // A leftover of a renamed scenario, and the scenario-less layout,
    // which is legitimate.
    std::fs::create_dir_all(crate_dir.join("proofs/old-name/lean")).unwrap();
    std::fs::create_dir_all(crate_dir.join("proofs/fstar/extraction")).unwrap();

    let (output, success) = extract(&[], &crate_dir);
    assert!(success, "{output}");
    assert!(output.contains("old-name"), "{output}");
    assert!(
        output.contains("lies under no output directory"),
        "{output}"
    );
    assert!(!output.contains("proofs/fstar"), "{output}");

    // A narrowed run proves nothing about other directories: no warning.
    let (output, success) = extract(&["demo"], &crate_dir);
    assert!(success, "{output}");
    assert!(!output.contains("old-name"), "{output}");
}
