//! Scaffolding of the Lean package around an extraction: the project files
//! (`lakefile.toml`, `lean-toolchain`, `.gitignore`), the root module, the
//! `Verification/` stub for handwritten proofs, the `Assumptions/` files
//! holding the user's models of external definitions, and the checks that
//! keep an existing package consistent with the current extraction and
//! version resolution.
//!
//! Everything outside `Extraction/` is created only when missing, so
//! re-extraction never overwrites handwritten proofs or manual edits. The
//! single opt-out against recreation and the root-module warnings is a
//! commented-out import line (`-- import ...`) in the root module.

use hax_types::cli_options::*;
use hax_types::diagnostics::message::HaxMessage;
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

/// The source repository of the aeneas Lean proof library: the repository
/// the managed aeneas binaries are built from, so a resolved aeneas
/// version doubles as the library's rev.
const AENEAS_REPO: &str = "https://github.com/cryspen/aeneas";

/// The source repository of the `Hax` Lean proof library.
const HAX_LEAN_LIB_REPO: &str = "https://github.com/cryspen/hax-lean";

/// Module roots the required libraries provide: Lean itself, and every
/// `lean_lib` of the `Hax` package (`CoreModels` among them, which the
/// extracted assumption modules import). A package named like one of them
/// fails inside `lake` in a confusing way, so the collision is caught up
/// front.
pub(crate) const RESERVED_MODULE_ROOTS: &[&str] = &[
    "Lean",
    "Init",
    "Std",
    "Lake",
    "Aeneas",
    "Hax",
    "CoreModels",
    "Tests",
];

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

/// Check that `pkg_name` can name a Lean package: a legal Lean identifier
/// (which a crate name starting with a digit does not yield) that does not
/// collide with a module root present in every package. `origin` names
/// where the candidate came from, for the error message.
pub fn validate_package_name(pkg_name: &str, origin: &str) -> Result<(), String> {
    let mut chars = pkg_name.chars();
    let legal = chars.next().is_some_and(|c| c.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_');
    if !legal {
        return Err(format!(
            "`{pkg_name}` ({origin}) is not a legal Lean identifier, so it cannot \
             name the Lean package; extract through a proof scenario, whose name \
             determines the package name"
        ));
    }
    if RESERVED_MODULE_ROOTS.contains(&pkg_name) {
        return Err(format!(
            "`{pkg_name}` ({origin}) collides with a module root present in every \
             generated Lean package, so it cannot name the Lean package; extract \
             through a proof scenario, whose name determines the package name"
        ));
    }
    Ok(())
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
fn lakefile_contents(pkg_name: &str, pins: &LakefilePins) -> String {
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

/// The generated artifacts that should not be committed. The extracted
/// `.lean` files stay tracked.
const GITIGNORE_CONTENTS: &str = "/llbc/\n/.lake/\n/aeneas-error.log\n";

/// The stub for handwritten proofs. Comments only, so the package builds
/// before any extraction module it could import exists.
fn verification_stub(pkg_name: &str) -> String {
    format!(
        "/- Handwritten proofs about the extracted definitions.\n\
         \n\
         hax creates this file once and never modifies anything under\n\
         `Verification/`. Import the extraction modules to prove properties\n\
         about, e.g. `import {pkg_name}.Extraction.Funs`. -/\n"
    )
}

/// The stems of the extraction files that hold models of external
/// definitions in the aeneas workflow. The models are user content: they
/// live in `Assumptions/`, seeded from the `<stem>_Template.lean` files
/// aeneas generates, and the extraction reaches them through a hax-owned
/// shim at `Extraction/<stem>.lean` (which is where the generated imports
/// point).
const EXTERNAL_STEMS: &[&str] = &["FunsExternal", "TypesExternal"];

/// Whether an `Extraction/` module holds external definitions (a shim or
/// an aeneas template). These are not imported by the root module: the
/// extraction files that need them import them themselves.
fn is_external(stem: &str) -> bool {
    let stem = stem.strip_suffix("_Template").unwrap_or(stem);
    EXTERNAL_STEMS.contains(&stem)
}

/// The shim redirecting a generated `import <Pkg>.Extraction.<stem>` to
/// the user's models in `Assumptions/`.
fn external_shim(pkg_name: &str, stem: &str) -> String {
    format!("import {pkg_name}.Assumptions.{stem}\n")
}

fn extraction_dir(lean_dir: &Path, pkg_name: &str) -> PathBuf {
    lean_dir.join(pkg_name).join("Extraction")
}

fn assumptions_path(lean_dir: &Path, pkg_name: &str, stem: &str) -> PathBuf {
    lean_dir
        .join(pkg_name)
        .join("Assumptions")
        .join(format!("{stem}.lean"))
}

/// Move user-maintained external-definition files out of `Extraction/`
/// into `Assumptions/`. Must run before `Extraction/` is cleared: before
/// `Assumptions/` existed, the filled-in templates lived in `Extraction/`
/// directly, and clearing would silently destroy them. A file that is
/// hax's own shim, or whose `Assumptions/` counterpart already exists, is
/// left for the clearing. Returns whether a move failed, in which case the
/// caller must not clear `Extraction/`.
pub fn rescue_external_files(
    lean_dir: &Path,
    pkg_name: &str,
    message_format: MessageFormat,
) -> bool {
    let mut error = false;
    for stem in EXTERNAL_STEMS {
        let old = extraction_dir(lean_dir, pkg_name).join(format!("{stem}.lean"));
        // An unreadable file must fail the rescue: the clearing would
        // delete it, and only a missing one is legitimately skipped.
        let contents = match fs::read_to_string(&old) {
            Ok(contents) => contents,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => {
                HaxMessage::GenericError {
                    message: format!("failed to read {}: {}", old.display(), e),
                }
                .report(message_format, None);
                error = true;
                continue;
            }
        };
        // The shim is recognized by its import, not by exact bytes: a
        // formatting variant (say, written by another hax version) must
        // not land in `Assumptions/`, where it would import itself.
        let assumptions_import = format!("{pkg_name}.Assumptions.{stem}");
        if parse_root_imports(&contents)
            .active
            .contains(&assumptions_import)
        {
            if contents.trim() != format!("import {assumptions_import}") {
                HaxMessage::GenericWarning {
                    message: format!(
                        "{} imports {} and is removed with the rest of the \
                         extraction; models of external definitions live in \
                         `Assumptions/`, which hax never modifies",
                        old.display(),
                        assumptions_import
                    ),
                }
                .report(message_format, None);
            }
            continue;
        }
        let new = assumptions_path(lean_dir, pkg_name, stem);
        if new.exists() {
            // The file is left for the clearing; losing edits that diverge
            // from the `Assumptions/` copy deserves a warning.
            if fs::read_to_string(&new).ok().as_deref() != Some(&contents) {
                HaxMessage::GenericWarning {
                    message: format!(
                        "{} differs from {} and is removed with the rest of \
                         the extraction; models of external definitions live \
                         in `Assumptions/`, which hax never modifies",
                        old.display(),
                        new.display()
                    ),
                }
                .report(message_format, None);
            }
            continue;
        }
        let moved = fs::create_dir_all(new.parent().expect("the path has a parent"))
            .and_then(|()| fs::rename(&old, &new));
        match moved {
            Ok(()) => HaxMessage::GenericWarning {
                message: format!(
                    "moved {} to {}: models of external definitions live in \
                     `Assumptions/`, which hax never modifies",
                    old.display(),
                    new.display()
                ),
            }
            .report(message_format, None),
            Err(e) => {
                HaxMessage::GenericError {
                    message: format!(
                        "failed to move {} to {}: {}",
                        old.display(),
                        new.display(),
                        e
                    ),
                }
                .report(message_format, None);
                error = true;
            }
        }
    }
    error
}

/// Wire the extraction's external definitions to `Assumptions/`, after
/// aeneas ran: seed each missing `Assumptions/<stem>.lean` from the
/// `<stem>_Template.lean` aeneas generated, and write the shim the
/// extraction's imports resolve to. The templates signal which external
/// files this extraction needs; the seeded files are the user's from then
/// on. Returns whether an error occurred.
pub fn process_external_templates(
    lean_dir: &Path,
    pkg_name: &str,
    message_format: MessageFormat,
) -> bool {
    let mut error = false;
    for stem in EXTERNAL_STEMS {
        let extraction_dir = extraction_dir(lean_dir, pkg_name);
        let template = extraction_dir.join(format!("{stem}_Template.lean"));
        let Ok(template_contents) = fs::read_to_string(&template) else {
            continue;
        };
        let assumption = assumptions_path(lean_dir, pkg_name, stem);
        if let Err(e) = fs::create_dir_all(assumption.parent().expect("the path has a parent")) {
            HaxMessage::GenericError {
                message: format!("failed to create the `Assumptions/` directory: {e}"),
            }
            .report(message_format, None);
            error = true;
        }
        error |= write_if_absent(&assumption, &template_contents, message_format);
        let shim = extraction_dir.join(format!("{stem}.lean"));
        if let Err(e) = fs::write(&shim, external_shim(pkg_name, stem)) {
            HaxMessage::GenericError {
                message: format!("failed to write {}: {}", shim.display(), e),
            }
            .report(message_format, None);
            error = true;
        }
    }
    error
}

/// The extraction files the generated root module imports, in build order,
/// as (subdirectory, module stem). `Verification/ProofObligations.lean` is
/// the stub for the handwritten proofs of the obligations the extraction
/// states.
///
/// Deliberately a fixed list, while [`check_root_module`] scans the files
/// on disk: the root module is written once and never updated (regenerating
/// it would overwrite user edits), so a file appearing after the scaffolding
/// is surfaced by the check's warning rather than by regeneration.
const ROOT_IMPORTS: &[(&str, &str)] = &[
    ("Extraction", "Types"),
    ("Extraction", "Funs"),
    ("Extraction", "Specs"),
    ("Extraction", "ProofObligations"),
    ("Verification", "ProofObligations"),
];

/// Generate the contents of the root `<PkgName>.lean` file: an import for
/// each known module whose file exists. Called after the extraction, so
/// files produced by the same run are covered.
fn root_module_contents(lean_dir: &Path, pkg_name: &str) -> String {
    ROOT_IMPORTS
        .iter()
        .filter(|(dir, stem)| {
            lean_dir
                .join(pkg_name)
                .join(dir)
                .join(format!("{stem}.lean"))
                .exists()
        })
        .map(|(dir, stem)| format!("import {pkg_name}.{dir}.{stem}\n"))
        .collect()
}

/// The import lines of a root module: the modules it imports, and those it
/// deliberately opts out of with a `--` line comment (optionally indented).
/// Imports inside block comments are not recognized as commented.
#[derive(Debug, Default, PartialEq, Eq)]
struct RootImports {
    active: BTreeSet<String>,
    commented: BTreeSet<String>,
}

fn parse_root_imports(contents: &str) -> RootImports {
    let mut imports = RootImports::default();
    for line in contents.lines() {
        let line = line.trim_start();
        let (line, commented) = match line.strip_prefix("--") {
            Some(rest) => (rest.trim_start(), true),
            None => (line, false),
        };
        let Some(rest) = line.strip_prefix("import") else {
            continue;
        };
        // `import` must be its own word: `imports` is not an import line.
        if !rest.starts_with(char::is_whitespace) {
            continue;
        }
        let Some(module) = rest.split_whitespace().next() else {
            continue;
        };
        let set = if commented {
            &mut imports.commented
        } else {
            &mut imports.active
        };
        set.insert(module.to_string());
    }
    imports
}

/// Whether generation treats `path` as absent and would write it. An empty
/// file counts as absent: it holds no content worth preserving (typically
/// the leftover of an interrupted write) and would otherwise never be
/// repaired, since existing files are not touched.
fn absent_or_empty(path: &Path) -> bool {
    !fs::metadata(path).is_ok_and(|metadata| !metadata.is_file() || metadata.len() > 0)
}

/// Write `contents` to `path` if [`absent_or_empty`] holds for it.
/// Reports the file as produced (wrote or unchanged) via `HaxMessage`.
/// Returns whether writing failed.
fn write_if_absent(path: &Path, contents: &str, message_format: MessageFormat) -> bool {
    if !absent_or_empty(path) {
        HaxMessage::ProducedFile {
            path: path.to_path_buf(),
            wrote: false,
        }
        .report(message_format, None);
        false
    } else {
        match fs::write(path, contents) {
            Ok(()) => {
                HaxMessage::ProducedFile {
                    path: path.to_path_buf(),
                    wrote: true,
                }
                .report(message_format, None);
                false
            }
            Err(e) => {
                HaxMessage::GenericError {
                    message: format!("failed to write {}: {}", path.display(), e),
                }
                .report(message_format, None);
                true
            }
        }
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

/// The path of the root module of the package in `lean_dir`.
fn root_module_path(lean_dir: &Path, pkg_name: &str) -> PathBuf {
    lean_dir.join(format!("{pkg_name}.lean"))
}

/// The commented-out imports of the root module, which opt files out of
/// recreation and of the root-module warnings. Empty if there is no root
/// module.
fn root_module_opt_outs(lean_dir: &Path, pkg_name: &str) -> BTreeSet<String> {
    fs::read_to_string(root_module_path(lean_dir, pkg_name))
        .map(|contents| parse_root_imports(&contents).commented)
        .unwrap_or_default()
}

/// Generate every missing package file in `lean_dir`. Existing files are
/// never overwritten. The root module is written only after a successful
/// extraction (`extraction_ok`), so that its imports cover the files that
/// run produced; a failed run leaves the scaffolding without a root module,
/// which the next successful run completes.
///
/// `aeneas_local_path` is set when aeneas resolves to a local binary, whose
/// pin in `pins` is the substituted default: a lakefile that is actually
/// written then carries a warning naming the substitution.
///
/// Returns whether an error occurred.
pub fn generate(
    lean_dir: &Path,
    pkg_name: &str,
    pins: &LakefilePins,
    extraction_ok: bool,
    aeneas_local_path: Option<&Path>,
    message_format: MessageFormat,
) -> bool {
    let mut error = false;
    let opt_outs = root_module_opt_outs(lean_dir, pkg_name);

    // A handwritten `lakefile.lean` fills the same role: lake rejects a
    // package with both configuration files, so it suppresses the
    // generation.
    if !lean_dir.join("lakefile.lean").exists() {
        let lakefile = lean_dir.join("lakefile.toml");
        if absent_or_empty(&lakefile) {
            if let Some(path) = aeneas_local_path {
                HaxMessage::GenericWarning {
                    message: format!(
                        "aeneas resolves to the local binary {}; pinning the aeneas Lean \
                         library to the default {} in the generated lakefile",
                        path.display(),
                        pins.aeneas_rev
                    ),
                }
                .report(message_format, None);
            }
        }
        error |= write_if_absent(
            &lakefile,
            &lakefile_contents(pkg_name, pins),
            message_format,
        );
    }
    error |= write_if_absent(
        &lean_dir.join("lean-toolchain"),
        &pins.lean_toolchain,
        message_format,
    );
    error |= write_if_absent(
        &lean_dir.join(".gitignore"),
        GITIGNORE_CONTENTS,
        message_format,
    );

    if !opt_outs.contains(&format!("{pkg_name}.Verification.ProofObligations")) {
        let verification_dir = lean_dir.join(pkg_name).join("Verification");
        if let Err(e) = fs::create_dir_all(&verification_dir) {
            HaxMessage::GenericError {
                message: format!("failed to create {}: {}", verification_dir.display(), e),
            }
            .report(message_format, None);
            error = true;
        }
        error |= write_if_absent(
            &verification_dir.join("ProofObligations.lean"),
            &verification_stub(pkg_name),
            message_format,
        );
    }

    if extraction_ok {
        error |= write_if_absent(
            &root_module_path(lean_dir, pkg_name),
            &root_module_contents(lean_dir, pkg_name),
            message_format,
        );
    }
    error
}

/// Check the root module against the files on disk, in both directions: an
/// extraction file (or the `Verification/` stub) it does not import will
/// silently stay out of the build, and an import of a file the extraction
/// no longer produces fails the build less legibly than a warning here. A
/// commented-out import silences both directions for that file. Imports of
/// missing files below `Verification/` are the user's business and are not
/// reported.
pub fn check_root_module(lean_dir: &Path, pkg_name: &str, message_format: MessageFormat) {
    let root_path = root_module_path(lean_dir, pkg_name);
    let Ok(contents) = fs::read_to_string(&root_path) else {
        return;
    };
    let imports = parse_root_imports(&contents);
    let extraction_dir = extraction_dir(lean_dir, pkg_name);

    let mut expected: BTreeSet<String> = fs::read_dir(&extraction_dir)
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.ok())
        .filter_map(|entry| {
            let path = entry.path();
            let stem = (path.extension()? == "lean")
                .then(|| path.file_stem())??
                .to_str()?;
            (!is_external(stem)).then(|| format!("{pkg_name}.Extraction.{stem}"))
        })
        .collect();
    if lean_dir
        .join(pkg_name)
        .join("Verification")
        .join("ProofObligations.lean")
        .exists()
    {
        expected.insert(format!("{pkg_name}.Verification.ProofObligations"));
    }

    for import in &expected {
        if !imports.active.contains(import) && !imports.commented.contains(import) {
            HaxMessage::RootModuleMissingImport {
                path: root_path.clone(),
                import: import.clone(),
            }
            .report(message_format, None);
        }
    }

    let extraction_prefix = format!("{pkg_name}.Extraction.");
    for import in &imports.active {
        let Some(module) = import.strip_prefix(&extraction_prefix) else {
            continue;
        };
        if module.is_empty() {
            continue;
        }
        let mut file = extraction_dir.clone();
        file.extend(module.split('.'));
        file.set_extension("lean");
        if !file.exists() {
            HaxMessage::RootModuleStaleImport {
                path: root_path.clone(),
                import: import.clone(),
            }
            .report(message_format, None);
        }
    }
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
            "MyCrate",
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
            "MyCrate",
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
            "MyCrate",
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
            "MyCrate",
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
            "MyCrate",
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

    #[test]
    fn package_names_are_validated() {
        validate_package_name("MyCrate", "derived from `my-crate`").unwrap();
        validate_package_name("A2b_c", "derived from `a2b_c`").unwrap();
        for name in ["2fast", "", "My.Crate", "My Crate", "_Under"] {
            let err = validate_package_name(name, "derived").unwrap_err();
            assert!(err.contains("not a legal Lean identifier"), "{name}: {err}");
        }
        for name in RESERVED_MODULE_ROOTS {
            let err = validate_package_name(name, "derived").unwrap_err();
            assert!(err.contains("module root"), "{name}: {err}");
        }
    }

    #[test]
    fn exactly_the_external_stems_and_their_templates_are_external() {
        for stem in EXTERNAL_STEMS {
            assert!(is_external(stem));
            assert!(is_external(&format!("{stem}_Template")));
        }
        assert!(!is_external("Funs"));
        assert!(!is_external("SomethingExternal"));
    }

    #[test]
    fn import_lines_are_split_into_active_and_commented() {
        let imports = parse_root_imports(
            "import A.Extraction.Funs\n\
             -- import A.Extraction.Specs\n\
             \t--   import A.Verification.ProofObligations\n\
             import A.Extraction.Types -- trailing comment\n\
             -- some other comment\n\
             importFoo\n\
             /- import A.Blocked -/\n",
        );
        assert_eq!(
            imports.active,
            BTreeSet::from(["A.Extraction.Funs".into(), "A.Extraction.Types".into()])
        );
        assert_eq!(
            imports.commented,
            BTreeSet::from([
                "A.Extraction.Specs".into(),
                "A.Verification.ProofObligations".into()
            ])
        );
    }

    #[test]
    fn the_root_module_imports_exactly_the_existing_files_in_order() {
        let dir = tempfile::tempdir().unwrap();
        let extraction = dir.path().join("MyCrate/Extraction");
        std::fs::create_dir_all(&extraction).unwrap();
        for stem in ["Funs", "Types"] {
            std::fs::write(extraction.join(format!("{stem}.lean")), "").unwrap();
        }
        let verification = dir.path().join("MyCrate/Verification");
        std::fs::create_dir_all(&verification).unwrap();
        std::fs::write(verification.join("ProofObligations.lean"), "").unwrap();
        assert_eq!(
            root_module_contents(dir.path(), "MyCrate"),
            "import MyCrate.Extraction.Types\n\
             import MyCrate.Extraction.Funs\n\
             import MyCrate.Verification.ProofObligations\n"
        );
    }
}
