//! Lakefile generation for aeneas-lean projects.

use hax_types::cli_options::*;
use hax_types::diagnostics::message::HaxMessage;
use std::path::Path;
use std::{fs};


/// Generate the contents of a `lakefile.toml` for an aeneas-lean project.
fn lakefile_contents(crate_name: &str) -> String {
    // Convert crate name to PascalCase for the Lean module name
    let pkg_name: String = crate_name
        .split('_')
        .map(|s| {
            let mut c = s.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().to_string() + c.as_str(),
            }
        })
        .collect();

    format!(
        r#"name = "{pkg_name}"
version = "0.1.0"
defaultTargets = ["{pkg_name}"]

[[lean_lib]]
name = "{pkg_name}"
roots = ["extraction.{pkg_name}"]

[[require]]
name = "aeneas"
git = {{ url = "https://github.com/AeneasVerif/aeneas", subDir = "backends/lean" }}
"#
    )
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

/// Generates a `lakefile.toml` and `lean-toolchain` in `lean_dir`.
/// Existing files are not overwritten.
pub fn generate(lean_dir: &Path, crate_name: &str, message_format: MessageFormat) {
    write_if_absent(
        &lean_dir.join("lakefile.toml"),
        &lakefile_contents(crate_name),
        message_format,
    );
    write_if_absent(
        &lean_dir.join("lean-toolchain"),
        "leanprover/lean4:stable",
        message_format,
    );
}
