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

/// Generate the contents of a `lakefile.toml` for a lean project.
fn lakefile_contents(crate_name: &str, pins: &LakefilePins) -> String {
    let pkg_name = super::to_camel_case(crate_name);
    let aeneas_git = AENEAS_REPO;
    let aeneas_rev = &pins.aeneas_rev;
    let hax_lean_git = HAX_LEAN_LIB_REPO;
    let hax_lean_rev = &pins.hax_lean_lib_rev;

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
