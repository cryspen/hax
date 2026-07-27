//! Lakefile generation for lean projects.

use hax_types::cli_options::*;
use hax_types::diagnostics::message::HaxMessage;
use std::fs;
use std::path::Path;

/// Generate the contents of a `lakefile.toml` for an lean project.
///
/// The `aeneas` Lean proof library is pinned to the same source repo + commit as
/// the `aeneas` binary hax expects (baked from `pins.toml`'s `[aeneas]`, see
/// build.rs), so the proof library matches the extraction. The `Hax` Lean proof
/// library is pinned from `[hax-lean-lib]`. All pins are required — `generate`
/// rejects empty ones before we get here, so there are no fallbacks.
fn lakefile_contents(crate_name: &str) -> String {
    let pkg_name = super::to_camel_case(crate_name);
    let aeneas_git = super::AENEAS_PIN_REPO;
    let aeneas_rev = super::AENEAS_PIN_VERSION;
    let hax_lean_git = super::LEAN_LIB_PIN_REPO;
    let hax_lean_rev = super::LEAN_LIB_PIN_VERSION;

    format!(
        r#"name = "{pkg_name}"
version = "0.1.0"
defaultTargets = ["{pkg_name}"]

[[lean_lib]]
name = "{pkg_name}"

[[require]]
name = "aeneas"
git = "{aeneas_git}"
rev = "{aeneas_rev}"
subDir = "backends/lean"

[[require]]
name = "Hax"
git = {{ url = "{hax_lean_git}" }}
rev = "{hax_lean_rev}"
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
pub fn generate(lean_dir: &Path, crate_name: &str, message_format: MessageFormat) {
    let pkg_name = super::to_camel_case(crate_name);
    write_if_absent(
        &lean_dir.join("lakefile.toml"),
        &lakefile_contents(crate_name),
        message_format,
    );
    write_if_absent(
        &lean_dir.join("lean-toolchain"),
        super::LEAN_PIN_TOOLCHAIN,
        message_format,
    );
    write_if_absent(
        &lean_dir.join(format!("{pkg_name}.lean")),
        &root_lean_contents(crate_name),
        message_format,
    );
}
