//! Lakefile generation for lean projects.

use hax_types::cli_options::*;
use hax_types::diagnostics::message::HaxMessage;
use std::fs;
use std::path::Path;

/// The source repository of the aeneas Lean proof library: the repository
/// the managed aeneas binaries are built from, so a resolved aeneas
/// version doubles as the library's rev.
const AENEAS_REPO: &str = "https://github.com/cryspen/aeneas";

/// The source repository of the `Hax` Lean proof library.
const HAX_LEAN_LIB_REPO: &str = "https://github.com/cryspen/hax-lean";

/// The resolved versions a generated Lean project pins: the aeneas rev
/// (matching the aeneas binary, so the proof library matches the
/// extraction), the Lean toolchain, and the `Hax` library rev. All come
/// from the project's resolution ([versions] entries and the aeneas
/// resolution, or the built-in defaults).
pub struct LakefilePins {
    pub aeneas_rev: String,
    pub lean_toolchain: String,
    pub hax_lean_lib_rev: String,
}

/// Render a value as a TOML string, escaping what would otherwise
/// end it. The pinned revisions are validated before they reach here (a
/// `[versions]` entry when parsed, a tool version before it is installed);
/// this makes the generated file well-formed regardless, so a value that
/// ever slips through cannot restructure it into, say, a `[[require]]` on
/// a repository of its choosing.
fn toml_string(value: &str) -> String {
    toml::Value::String(value.to_string()).to_string()
}

/// Generate the contents of a `lakefile.toml` for a lean project.
fn lakefile_contents(crate_name: &str, pins: &LakefilePins) -> String {
    let pkg_name = super::to_camel_case(crate_name);
    let aeneas_git = AENEAS_REPO;
    let aeneas_rev = toml_string(&pins.aeneas_rev);
    let hax_lean_git = HAX_LEAN_LIB_REPO;
    let hax_lean_rev = toml_string(&pins.hax_lean_lib_rev);

    format!(
        r#"name = "{pkg_name}"
version = "0.1.0"
defaultTargets = ["{pkg_name}"]

[[lean_lib]]
name = "{pkg_name}"

[[require]]
name = "aeneas"
git = "{aeneas_git}"
rev = {aeneas_rev}
subDir = "backends/lean"

[[require]]
name = "Hax"
git = {{ url = "{hax_lean_git}" }}
rev = {hax_lean_rev}
"#
    )
}

/// Generate the contents of the root `<PkgName>.lean` file: a single
/// `import` line that pulls in the extracted module.
fn root_lean_contents(crate_name: &str) -> String {
    let pkg_name = super::to_camel_case(crate_name);
    format!("import {pkg_name}.Extraction.Funs\n")
}

/// Write `contents` to `path` if the file doesn't already exist.
/// Reports the file as produced (wrote or unchanged) via `HaxMessage`.
fn write_if_absent(path: &Path, contents: &str, message_format: MessageFormat) {
    if path.exists() {
        HaxMessage::ProducedFile {
            path: path.to_path_buf(),
            wrote: false,
        }
        .report(message_format, None);
    } else {
        fs::write(path, contents).unwrap_or_else(|e| {
            HaxMessage::GenericError {
                message: format!("failed to write {}: {}", path.display(), e),
            }
            .report(message_format, None);
        });
        HaxMessage::ProducedFile {
            path: path.to_path_buf(),
            wrote: true,
        }
        .report(message_format, None);
    }
}

/// The pins in an existing lakefile that differ from the current
/// resolution, as (require name, found rev, expected rev). Only the two
/// requires hax manages are compared; a lakefile that does not parse is
/// left alone (lake itself will complain). `aeneas_rev` is `None` when
/// aeneas resolves to a local binary, which no rev can be compared to.
fn lakefile_drifts(
    contents: &str,
    aeneas_rev: Option<&str>,
    hax_lean_lib_rev: &str,
) -> Vec<(String, String, String)> {
    let Ok(table) = contents.parse::<toml::Table>() else {
        return Vec::new();
    };
    let Some(requires) = table.get("require").and_then(toml::Value::as_array) else {
        return Vec::new();
    };
    requires
        .iter()
        .filter_map(|require| {
            let name = require.get("name")?.as_str()?;
            let found = require.get("rev")?.as_str()?;
            let expected = match name {
                "aeneas" => aeneas_rev?,
                "Hax" => hax_lean_lib_rev,
                _ => return None,
            };
            (found != expected).then(|| (name.to_string(), found.to_string(), expected.to_string()))
        })
        .collect()
}

/// Check an existing Lean project's pinned versions against the current
/// resolution, warning about each pin that differs. Generation never
/// overwrites these files, so without this check a project would keep
/// building against a stale library after a version update.
pub fn check_existing(
    lean_dir: &Path,
    aeneas_rev: Option<&str>,
    lean_toolchain: &str,
    hax_lean_lib_rev: &str,
    message_format: MessageFormat,
) {
    let lakefile_path = lean_dir.join("lakefile.toml");
    if let Ok(contents) = fs::read_to_string(&lakefile_path) {
        for (name, found, expected) in lakefile_drifts(&contents, aeneas_rev, hax_lean_lib_rev) {
            HaxMessage::LakefilePinDrift {
                path: lakefile_path.clone(),
                name,
                found,
                expected,
            }
            .report(message_format, None);
        }
    }
    let toolchain_path = lean_dir.join("lean-toolchain");
    if let Ok(contents) = fs::read_to_string(&toolchain_path) {
        let found = contents.trim();
        if !found.is_empty() && found != lean_toolchain.trim() {
            HaxMessage::LakefilePinDrift {
                path: toolchain_path,
                name: "lean".to_string(),
                found: found.to_string(),
                expected: lean_toolchain.trim().to_string(),
            }
            .report(message_format, None);
        }
    }
}

/// Generates a `lakefile.toml`, `lean-toolchain`, and root `<PkgName>.lean`
/// in `lean_dir`. Existing files are not overwritten.
pub fn generate(
    lean_dir: &Path,
    crate_name: &str,
    pins: &LakefilePins,
    message_format: MessageFormat,
) {
    let pkg_name = super::to_camel_case(crate_name);
    write_if_absent(
        &lean_dir.join("lakefile.toml"),
        &lakefile_contents(crate_name, pins),
        message_format,
    );
    write_if_absent(
        &lean_dir.join("lean-toolchain"),
        &pins.lean_toolchain,
        message_format,
    );
    write_if_absent(
        &lean_dir.join(format!("{pkg_name}.lean")),
        &root_lean_contents(crate_name),
        message_format,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `[[require]]` entries of a generated lakefile, as
    /// (name, git url, rev). Panics if it is not valid TOML.
    fn requires(contents: &str) -> Vec<(String, String, String)> {
        let table: toml::Table = contents
            .parse()
            .unwrap_or_else(|e| panic!("generated lakefile is not valid TOML: {e}\n{contents}"));
        table["require"]
            .as_array()
            .unwrap()
            .iter()
            .map(|require| {
                let git = match &require["git"] {
                    toml::Value::String(url) => url.clone(),
                    table => table["url"].as_str().unwrap().to_string(),
                };
                (
                    require["name"].as_str().unwrap().to_string(),
                    git,
                    require["rev"].as_str().unwrap().to_string(),
                )
            })
            .collect()
    }

    #[test]
    fn pins_appear_as_the_revisions_of_the_two_requires() {
        let contents = lakefile_contents(
            "my_crate",
            &LakefilePins {
                aeneas_rev: "nightly-1".into(),
                lean_toolchain: "leanprover/lean4:v4.31.0".into(),
                hax_lean_lib_rev: "v0.2.0".into(),
            },
        );
        assert_eq!(
            requires(&contents),
            vec![
                (
                    "aeneas".to_string(),
                    AENEAS_REPO.to_string(),
                    "nightly-1".to_string()
                ),
                (
                    "Hax".to_string(),
                    HAX_LEAN_LIB_REPO.to_string(),
                    "v0.2.0".to_string()
                ),
            ]
        );
    }

    #[test]
    fn matching_pins_are_no_drift() {
        let contents = lakefile_contents(
            "my_crate",
            &LakefilePins {
                aeneas_rev: "nightly-1".into(),
                lean_toolchain: "leanprover/lean4:v4.31.0".into(),
                hax_lean_lib_rev: "v0.2.0".into(),
            },
        );
        assert_eq!(lakefile_drifts(&contents, Some("nightly-1"), "v0.2.0"), []);
    }

    #[test]
    fn each_drifted_require_is_reported_with_both_revisions() {
        let contents = lakefile_contents(
            "my_crate",
            &LakefilePins {
                aeneas_rev: "nightly-1".into(),
                lean_toolchain: "leanprover/lean4:v4.31.0".into(),
                hax_lean_lib_rev: "v0.1.0".into(),
            },
        );
        assert_eq!(
            lakefile_drifts(&contents, Some("nightly-2"), "v0.2.0"),
            vec![
                (
                    "aeneas".to_string(),
                    "nightly-1".to_string(),
                    "nightly-2".to_string()
                ),
                (
                    "Hax".to_string(),
                    "v0.1.0".to_string(),
                    "v0.2.0".to_string()
                ),
            ]
        );
    }

    /// A path-resolved aeneas has no rev to compare, so only the `Hax`
    /// require is checked.
    #[test]
    fn without_an_aeneas_rev_only_the_hax_require_is_checked() {
        let contents = lakefile_contents(
            "my_crate",
            &LakefilePins {
                aeneas_rev: "nightly-1".into(),
                lean_toolchain: "leanprover/lean4:v4.31.0".into(),
                hax_lean_lib_rev: "v0.1.0".into(),
            },
        );
        assert_eq!(
            lakefile_drifts(&contents, None, "v0.2.0"),
            vec![(
                "Hax".to_string(),
                "v0.1.0".to_string(),
                "v0.2.0".to_string()
            )]
        );
    }

    /// Requires the user added and files that are not valid TOML are
    /// left alone.
    #[test]
    fn foreign_requires_and_invalid_toml_are_ignored() {
        let contents = "[[require]]\nname = \"mathlib\"\nrev = \"v4.31.0\"\n";
        assert_eq!(lakefile_drifts(contents, Some("nightly-1"), "v0.2.0"), []);
        assert_eq!(
            lakefile_drifts("not toml [", Some("nightly-1"), "v0.2.0"),
            []
        );
    }

    /// A revision is written as one TOML string, whatever it contains: it
    /// cannot close that string to add a `[[require]]` of its own.
    #[test]
    fn a_revision_cannot_add_a_require() {
        let injection = "v1\"\n\n[[require]]\nname = \"X\"\n\
                         git = \"https://evil.example/x\"\nrev = \"main";
        let contents = lakefile_contents(
            "my_crate",
            &LakefilePins {
                aeneas_rev: "nightly-1".into(),
                lean_toolchain: "leanprover/lean4:v4.31.0".into(),
                hax_lean_lib_rev: injection.into(),
            },
        );
        assert_eq!(
            requires(&contents),
            vec![
                (
                    "aeneas".to_string(),
                    AENEAS_REPO.to_string(),
                    "nightly-1".to_string()
                ),
                (
                    "Hax".to_string(),
                    HAX_LEAN_LIB_REPO.to_string(),
                    injection.to_string()
                ),
            ]
        );
    }
}
