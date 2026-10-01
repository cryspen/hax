//! End-to-end tests for `cargo hax tools pin`: which `hax.toml` is edited,
//! what the two forms write, and what they leave untouched, exercised
//! through the real binary on a temporary Cargo workspace.

mod common;

use std::path::Path;
use std::process::Command;

use common::write_crate;

/// A workspace with two members, no `hax.toml` anywhere.
fn workspace() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"a\", \"b\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    write_crate(&dir.path().join("a"), "a");
    write_crate(&dir.path().join("b"), "b");
    dir
}

fn run(args: &[&str], current_dir: &Path) -> (String, bool) {
    let output = Command::new(env!("CARGO_BIN_EXE_cargo-hax"))
        .args(args)
        .current_dir(current_dir)
        .output()
        .expect("could not run cargo-hax");
    (
        format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
        output.status.success(),
    )
}

/// The versions the binary under test defaults to, read from `tools show`.
fn defaults(dir: &Path) -> serde_json::Value {
    let output = Command::new(env!("CARGO_BIN_EXE_cargo-hax"))
        .args(["--message-format", "json", "tools", "show"])
        .current_dir(dir)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    serde_json::from_str(stdout.lines().last().unwrap()).unwrap()
}

fn default_of(show: &serde_json::Value, section: &str, name: &str) -> String {
    show["ToolsShow"][section]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["name"] == name)
        .unwrap()["version"]
        .as_str()
        .unwrap()
        .to_string()
}

#[test]
fn bare_pin_writes_the_defaults_and_is_idempotent() {
    let dir = workspace();
    let show = defaults(dir.path());

    let (output, success) = run(&["tools", "pin"], dir.path());
    assert!(success, "{output}");
    assert!(output.contains("Pinned aeneas"), "{output}");
    assert!(output.contains("Pinned lean"), "{output}");
    // The hint replaces installing, which `pin` deliberately does not do.
    assert!(
        output.contains("run `cargo hax tools install` to pre-fetch"),
        "{output}"
    );

    // Every managed tool and declared key is pinned at its default.
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    for (section, name) in [
        ("tools", "aeneas"),
        ("tools", "charon"),
        ("versions", "lean"),
        ("versions", "hax-lean-lib"),
    ] {
        let version = default_of(&show, section, name);
        assert!(
            written.contains(&format!("{name} = \"{version}\"")),
            "{written}"
        );
    }
    assert!(
        written.contains("[tools]") && written.contains("[versions]"),
        "{written}"
    );
    // Pinning the defaults means nothing deviates from them, so no
    // non-default-version notice is produced afterwards.
    let (output, _) = run(&["tools", "show"], dir.path());
    assert!(!output.contains("tested with"), "{output}");

    // Running again changes nothing and says so.
    let (output, success) = run(&["tools", "pin"], dir.path());
    assert!(success, "{output}");
    assert!(output.contains("already pins these versions"), "{output}");
    assert_eq!(
        std::fs::read_to_string(dir.path().join("hax.toml")).unwrap(),
        written
    );
}

#[test]
fn bare_pin_rewrites_outdated_entries_and_reports_the_previous_version() {
    let dir = workspace();
    let show = defaults(dir.path());
    let charon = default_of(&show, "tools", "charon");
    std::fs::write(
        dir.path().join("hax.toml"),
        "# our pins\n[tools]\naeneas = \"nightly-1111.01.01\"  # old\n",
    )
    .unwrap();

    let (output, success) = run(&["tools", "pin"], dir.path());
    assert!(success, "{output}");
    assert!(output.contains("(was nightly-1111.01.01)"), "{output}");

    // The outdated entry is rewritten in place, the missing ones added,
    // and comments and formatting survive.
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    assert!(written.starts_with("# our pins\n"), "{written}");
    assert!(written.contains("  # old"), "{written}");
    assert!(!written.contains("nightly-1111.01.01"), "{written}");
    assert!(
        written.contains(&format!("charon = \"{charon}\"")),
        "{written}"
    );
}

#[test]
fn pin_sets_one_entry_in_the_table_the_name_belongs_to() {
    let dir = workspace();

    let (output, success) = run(&["tools", "pin", "charon@nightly-2026.07.16"], dir.path());
    assert!(success, "{output}");
    assert!(
        output.contains("Pinned charon nightly-2026.07.16"),
        "{output}"
    );

    // A declared-only key goes to `[versions]`, not `[tools]`.
    let (output, success) = run(
        &["tools", "pin", "lean@leanprover/lean4:v4.31.0"],
        dir.path(),
    );
    assert!(success, "{output}");
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    let tools = written.find("[tools]").unwrap();
    let versions = written.find("[versions]").unwrap();
    assert!(written.find("charon =").unwrap() > tools, "{written}");
    assert!(written.find("lean =").unwrap() > versions, "{written}");
    // Only the named entry is written: the argument form does not pin the
    // remaining defaults.
    assert!(!written.contains("aeneas"), "{written}");
    assert!(!written.contains("hax-lean-lib"), "{written}");
}

#[test]
fn pinning_a_version_outside_the_manifest_warns_but_writes_it() {
    let dir = workspace();
    let (output, success) = run(&["tools", "pin", "charon@nightly-9999.01.01"], dir.path());
    assert!(success, "{output}");
    assert!(
        output.contains("not in this release's manifest"),
        "{output}"
    );
    assert!(output.contains("unverified fallback"), "{output}");
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    assert!(written.contains("nightly-9999.01.01"), "{written}");
}

#[test]
fn a_path_entry_is_left_untouched() {
    let dir = workspace();
    let contents = "[tools]\ncharon = { path = \"/opt/charon\" }\n";
    std::fs::write(dir.path().join("hax.toml"), contents).unwrap();

    // The named entry is the whole request, so not writing it fails.
    let (output, success) = run(&["tools", "pin", "charon@nightly-2026.07.16"], dir.path());
    assert!(!success, "{output}");
    assert!(output.contains("pinned to a path"), "{output}");
    assert!(output.contains("nothing was written"), "{output}");
    assert!(!output.contains("already pins these versions"), "{output}");
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    assert!(written.contains("/opt/charon"), "{written}");
    assert!(!written.contains("nightly-2026.07.16"), "{written}");

    // The bare form pins everything else and keeps the path entry.
    let (output, success) = run(&["tools", "pin"], dir.path());
    assert!(success, "{output}");
    assert!(output.contains("pinned to a path"), "{output}");
    assert!(output.contains("Pinned aeneas"), "{output}");
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    assert!(written.contains("/opt/charon"), "{written}");
}

#[test]
fn only_path_entries_left_reports_a_skip_not_an_unchanged_file() {
    let dir = workspace();
    let show = defaults(dir.path());
    // A file that leaves `pin` nothing to write: both tools are path
    // pinned, both declared versions already hold their default.
    let contents = format!(
        "[tools]\naeneas = {{ path = \"/opt/aeneas\" }}\ncharon = {{ path = \"/opt/charon\" }}\n\
         [versions]\nlean = \"{}\"\nhax-lean-lib = \"{}\"\n",
        default_of(&show, "versions", "lean"),
        default_of(&show, "versions", "hax-lean-lib"),
    );
    std::fs::write(dir.path().join("hax.toml"), &contents).unwrap();

    // The bare form wrote nothing, and does not claim the file pins what
    // was asked for.
    let (output, success) = run(&["tools", "pin"], dir.path());
    assert!(success, "{output}");
    assert!(
        output.contains("Skipped aeneas (pinned to a path)"),
        "{output}"
    );
    assert!(
        output.contains("Skipped charon (pinned to a path)"),
        "{output}"
    );
    assert!(output.contains("Unchanged ./hax.toml"), "{output}");
    assert!(!output.contains("already pins these versions"), "{output}");

    let (output, success) = run(&["tools", "pin", "charon@nightly-2026.07.16"], dir.path());
    assert!(!success, "{output}");
    assert_eq!(
        std::fs::read_to_string(dir.path().join("hax.toml")).unwrap(),
        contents
    );
}

#[test]
fn pin_repairs_a_hax_toml_the_project_rejects() {
    let dir = workspace();
    std::fs::write(
        dir.path().join("hax.toml"),
        "[tools]\ncharon = \"nightly 2026\"\n",
    )
    .unwrap();
    // The file is rejected by everything that loads the configuration.
    let (output, success) = run(&["tools", "show"], dir.path());
    assert!(!success, "{output}");

    let (output, success) = run(&["tools", "pin", "charon@nightly-2026.07.16"], dir.path());
    assert!(success, "{output}");
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    assert!(written.contains("nightly-2026.07.16"), "{written}");
    let (output, success) = run(&["tools", "show"], dir.path());
    assert!(success, "{output}");
}

#[test]
fn a_rejected_member_file_does_not_block_pinning_at_the_root() {
    let dir = workspace();
    std::fs::write(
        dir.path().join("b").join("hax.toml"),
        "[tools]\ncharon = \"nightly 2026\"\n",
    )
    .unwrap();

    let (output, success) = run(&["tools", "pin", "charon@nightly-2026.07.16"], dir.path());
    assert!(success, "{output}");
    let written = std::fs::read_to_string(dir.path().join("hax.toml")).unwrap();
    assert!(written.contains("nightly-2026.07.16"), "{written}");
}

#[test]
fn inside_a_member_crate_pin_edits_that_crate() {
    let dir = workspace();
    let member = dir.path().join("b");

    let (output, success) = run(&["tools", "pin", "charon@nightly-2026.07.16"], &member);
    assert!(success, "{output}");
    // Creating an override is worth saying at write time: the override
    // warning of the other subcommands cannot see a file that does not
    // exist yet.
    assert!(output.contains("per-crate override"), "{output}");
    // The member's own file is written; the workspace root is untouched.
    let written = std::fs::read_to_string(member.join("hax.toml")).unwrap();
    assert!(written.contains("nightly-2026.07.16"), "{written}");
    assert!(!dir.path().join("hax.toml").exists());

    // The override warning applies to the file just created.
    let (output, _) = run(&["tools", "show"], dir.path());
    assert!(
        output.contains("overrides the workspace tool configuration"),
        "{output}"
    );
}

#[test]
fn a_member_run_writing_nothing_does_not_announce_an_override() {
    let dir = workspace();
    let member = dir.path().join("b");

    let (output, success) = run(&["tools", "pin"], &member);
    assert!(success, "{output}");
    assert!(output.contains("per-crate override"), "{output}");

    // Nothing is written the second time, so there is no override to
    // announce.
    let (output, success) = run(&["tools", "pin"], &member);
    assert!(success, "{output}");
    assert!(!output.contains("per-crate override"), "{output}");
}

#[test]
fn a_project_whose_dependencies_do_not_resolve_can_still_be_pinned() {
    let dir = workspace();
    // Pinning needs the project's directories, not its dependency graph:
    // an unresolvable dependency (or a cold registry cache offline) must
    // not stand between a project and its pins.
    std::fs::write(
        dir.path().join("a").join("Cargo.toml"),
        "[package]\nname = \"a\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n\
         [dependencies]\nno-such-package-hax-test = \"1\"\n",
    )
    .unwrap();

    let (output, success) = run(&["tools", "pin"], dir.path());
    assert!(success, "{output}");
    assert!(dir.path().join("hax.toml").exists());
}

#[test]
fn outside_a_cargo_project_pin_fails_clearly() {
    let dir = tempfile::tempdir().unwrap();
    let (output, success) = run(&["tools", "pin"], dir.path());
    assert!(!success);
    assert!(
        output.contains("must be run inside a Cargo project"),
        "{output}"
    );
    assert!(!dir.path().join("hax.toml").exists());
}

#[test]
fn json_message_format_emits_structured_output() {
    let dir = workspace();
    std::fs::write(
        dir.path().join("hax.toml"),
        "[tools]\naeneas = { path = \"/opt/aeneas\" }\ncharon = \"nightly-2026.07.01\"\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_cargo-hax"))
        .args([
            "--message-format",
            "json",
            "tools",
            "pin",
            "charon@nightly-2026.07.16",
        ])
        .current_dir(dir.path())
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let pinned = stdout
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .find_map(|message| message.get("ToolsPinned").cloned())
        .expect("no `ToolsPinned` message");
    assert_eq!(
        pinned["changes"],
        serde_json::json!([{
            "name": "charon",
            "version": "nightly-2026.07.16",
            "previous": "nightly-2026.07.01",
        }])
    );
    assert_eq!(pinned["skipped"], serde_json::json!([] as [&str; 0]));
    assert!(
        pinned["path"].as_str().unwrap().ends_with("hax.toml"),
        "{pinned}"
    );
}

#[test]
fn malformed_pin_specs_are_rejected() {
    let dir = workspace();
    for (spec, expected) in [
        ("charon", "<name>@<version>"),
        ("unknown@v1", "not a pinnable name"),
        ("charon@../escape", "not a valid version identifier"),
        ("lean@../escape", "not a valid value"),
    ] {
        let (output, success) = run(&["tools", "pin", spec], dir.path());
        assert!(!success, "{spec}: {output}");
        assert!(output.contains(expected), "{spec}: {output}");
    }
    assert!(!dir.path().join("hax.toml").exists());
}
