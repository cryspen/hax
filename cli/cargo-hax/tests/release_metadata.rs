//! Checks that the binstall metadata of this crate and the release workflow
//! describe the same archives.
//!
//! `cargo binstall` fetches what `package.metadata.binstall` renders to, and
//! builds from source when it is not there: an archive the release workflow
//! names or compresses otherwise leaves a release that is silently not
//! binstallable, or one that every user's `cargo binstall` fails to unpack.
//! Since both sides of that agreement are files in this repository, it is
//! checked here rather than at release time, where the first version to
//! disagree is already published.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `package.metadata.binstall` of this crate.
fn binstall_metadata() -> toml::Value {
    let manifest =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"))
            .unwrap()
            .parse::<toml::Value>()
            .unwrap();
    manifest["package"]["metadata"]["binstall"].clone()
}

/// A workflow of this repository, or `None` outside a checkout: the published
/// crate carries this test, but not the workflows it reads. Whether this is a
/// checkout is decided by the directory, so that a workflow that moved or was
/// renamed fails these tests instead of skipping them.
fn workflow(name: &str) -> Option<String> {
    let dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.github/workflows");
    dir.is_dir()
        .then(|| std::fs::read_to_string(dir.join(name)).expect(name))
}

/// The `ARCHIVE` the release workflow packages, as a `pkg-url` template: the
/// name is per target there, and per `{ target }` in the metadata.
fn archive_template(workflow: &str) -> String {
    let archive = workflow
        .lines()
        .find_map(|line| line.trim().strip_prefix("ARCHIVE:"))
        .expect("the release workflow names an ARCHIVE")
        .trim();
    archive.replace("${{ matrix.target }}", "{ target }")
}

/// The script of the release workflow step that packages the archive.
fn packaging_script(workflow: &str) -> String {
    let lines: Vec<&str> = workflow.lines().collect();
    let indent = |line: &str| line.len() - line.trim_start().len();
    let step = lines
        .iter()
        .position(|line| line.trim() == "- name: Package the binary at the archive root")
        .expect("the release workflow has a packaging step");
    let run = (step..lines.len())
        .find(|&i| lines[i].trim() == "run: |")
        .expect("the packaging step has a run block");
    lines[run + 1..]
        .iter()
        .take_while(|line| line.trim().is_empty() || indent(line) > indent(lines[run]))
        .map(|line| line.trim_start())
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn the_release_workflow_names_the_archive_binstall_fetches() {
    let Some(release) = workflow("release.yml") else {
        return;
    };
    let pkg_url = binstall_metadata()["pkg-url"].as_str().unwrap().to_string();
    let (_, file) = pkg_url.rsplit_once('/').unwrap();
    assert_eq!(file, archive_template(&release));
}

#[test]
fn the_archive_is_published_under_the_tag_a_release_makes() {
    let pkg_url = binstall_metadata()["pkg-url"].as_str().unwrap().to_string();
    // `cargo release --workspace` tags this crate as `cargo-hax-v<version>`,
    // and the release workflow publishes the archives under that tag.
    assert!(
        pkg_url.contains("/releases/download/cargo-hax-v{ version }/"),
        "{pkg_url}"
    );
    let Some(release) = workflow("release.yml") else {
        return;
    };
    assert!(
        release.contains("\"cargo-hax-v$version\""),
        "the release workflow publishes under another tag"
    );
}

#[test]
fn the_declared_format_matches_the_archive_name() {
    let metadata = binstall_metadata();
    let pkg_url = metadata["pkg-url"].as_str().unwrap();
    let pkg_fmt = metadata["pkg-fmt"].as_str().unwrap();
    // `cargo binstall` unpacks by `pkg-fmt`, whatever the name says.
    assert_eq!(pkg_fmt, "tzstd", "{pkg_url}");
    assert!(pkg_url.ends_with(".tar.zst"), "{pkg_url}");
}

/// Runs the workflow's packaging step on a stand-in binary and unpacks the
/// archive the way `cargo binstall` unpacks `tzstd`: the binary has to sit at
/// the path `bin-dir` renders to, or every install fails to find it.
#[test]
fn the_binary_sits_in_the_archive_where_the_metadata_says() {
    let Some(release) = workflow("release.yml") else {
        return;
    };
    // The packaging step pipes through the `zstd` command.
    if Command::new("zstd").arg("--version").output().is_err() {
        eprintln!("skipped: `zstd` is not on PATH");
        return;
    }

    let target = "x86_64-unknown-linux-gnu";
    let archive = archive_template(&release).replace("{ target }", target);
    let script = packaging_script(&release).replace("${{ matrix.target }}", target);

    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("release-archive");
    let _ = std::fs::remove_dir_all(&dir);
    let release_dir = dir.join("target").join(target).join("release");
    std::fs::create_dir_all(&release_dir).unwrap();
    std::fs::write(release_dir.join("cargo-hax"), "the binary").unwrap();

    let packaging = Command::new("bash")
        .args(["-ec", &script])
        .env("ARCHIVE", &archive)
        .current_dir(&dir)
        .output()
        .unwrap();
    assert!(
        packaging.status.success(),
        "{}",
        String::from_utf8_lossy(&packaging.stderr)
    );

    let entries = Command::new("bash")
        .args([
            "-eo",
            "pipefail",
            "-c",
            r#"zstd -dc -- "$ARCHIVE" | tar -tf -"#,
        ])
        .env("ARCHIVE", &archive)
        .current_dir(&dir)
        .output()
        .unwrap();
    assert!(
        entries.status.success(),
        "{}",
        String::from_utf8_lossy(&entries.stderr)
    );
    let bin = binstall_metadata()["bin-dir"]
        .as_str()
        .unwrap()
        .replace("{ bin }", "cargo-hax")
        .replace("{ binary-ext }", "");
    assert_eq!(String::from_utf8_lossy(&entries.stdout).trim(), bin);
}
