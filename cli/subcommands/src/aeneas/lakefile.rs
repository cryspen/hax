//! Lakefile generation for aeneas-lean projects.

use hax_types::cli_options::*;
use hax_types::diagnostics::message::HaxMessage;
use std::fs;
use std::path::Path;

/// Generate the contents of a `lakefile.toml` for an aeneas-lean project.
fn lakefile_contents(crate_name: &str) -> String {
    let pkg_name = super::to_camel_case(crate_name);

    format!(
        r#"name = "{pkg_name}"
version = "0.1.0"
defaultTargets = ["{pkg_name}"]

[[lean_lib]]
name = "{pkg_name}"

[[require]]
name = "aeneas"
git = "https://github.com/AeneasVerif/aeneas"
rev = "main"
subDir = "backends/lean"
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
        "leanprover/lean4:v4.28.0-rc1",
        message_format,
    );
    write_if_absent(
        &lean_dir.join(format!("{pkg_name}.lean")),
        &root_lean_contents(crate_name),
        message_format,
    );
}
