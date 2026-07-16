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

/// Render a value as a TOML basic string, escaping what would otherwise
/// end it. The pinned revisions are validated before they reach here (a
/// `[versions]` entry when parsed, a tool version before it is installed);
/// this makes the generated file well-formed regardless, so a value that
/// ever slips through cannot restructure it into, say, a `[[require]]` on
/// a repository of its choosing.
fn toml_string(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len() + 2);
    escaped.push('"');
    for c in value.chars() {
        match c {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            c if c.is_control() => escaped.push_str(&format!("\\u{:04X}", c as u32)),
            c => escaped.push(c),
        }
    }
    escaped.push('"');
    escaped
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
