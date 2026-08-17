//! Parsing of `hax.toml` files.
//!
//! A `hax.toml` carries a `[tools]` table (managed tools, pinned by version
//! or pointed at a local binary by path), a `[versions]` table
//! (declared-only versions), and a top-level `project-files` key
//! (proof-project file generation). Unknown top-level keys, unknown tools, and
//! unknown keys inside an entry are warned about and skipped, so files
//! written for a newer hax remain readable by an older one. Malformed
//! entries are hard errors.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use super::{DECLARED_VERSION_KEYS, MANAGED_TOOLS};

/// A `[tools]` entry, mirroring Cargo's dependency syntax: a plain version
/// string, or a table with exactly one of `version` and `path`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToolEntry {
    Version(String),
    /// Path to an existing executable, used as-is. Resolved against the
    /// directory of the defining `hax.toml` if relative.
    Path(PathBuf),
}

/// The parsed contents of one `hax.toml`.
#[derive(Debug, Clone, Default)]
pub struct HaxToml {
    /// The file this was parsed from.
    pub path: PathBuf,
    pub tools: BTreeMap<String, ToolEntry>,
    pub versions: BTreeMap<String, String>,
    /// The top-level `project-files` key: whether hax generates and checks
    /// the proof-project files around an extraction. Backend-neutral; a
    /// member-level value overrides a workspace-level one.
    pub project_files: Option<bool>,
}

impl HaxToml {
    /// Whether this file carries any entry that affects resolution.
    pub fn has_entries(&self) -> bool {
        !self.tools.is_empty() || !self.versions.is_empty()
    }

    /// The names of all entries, for the member-override warning.
    pub fn entry_names(&self) -> Vec<String> {
        self.tools
            .keys()
            .chain(self.versions.keys())
            .cloned()
            .collect()
    }
}

/// Parse a `hax.toml`. Returns the parsed file and a list of non-fatal
/// warnings; a malformed entry is a hard error.
pub fn parse(path: &Path, contents: &str) -> Result<(HaxToml, Vec<String>), String> {
    let table: toml::Table = contents.parse().map_err(|e| format!("invalid TOML: {e}"))?;
    let dir = path.parent().unwrap_or(Path::new("."));
    let mut warnings = Vec::new();
    let mut result = HaxToml {
        path: path.to_path_buf(),
        ..HaxToml::default()
    };

    for (key, value) in table {
        match key.as_str() {
            "tools" => {
                let Some(tools) = value.as_table() else {
                    return Err("`[tools]` must be a table".into());
                };
                for (tool, entry) in tools {
                    if !MANAGED_TOOLS.contains(&tool.as_str()) {
                        warnings.push(format!(
                            "tool `{tool}` is not managed by this version of hax; \
                             its entry is ignored"
                        ));
                        continue;
                    }
                    let entry = parse_tool_entry(tool, entry, dir, &mut warnings)?;
                    result.tools.insert(tool.clone(), entry);
                }
            }
            "versions" => {
                let Some(versions) = value.as_table() else {
                    return Err("`[versions]` must be a table".into());
                };
                for (name, value) in versions {
                    if !DECLARED_VERSION_KEYS.contains(&name.as_str()) {
                        warnings.push(format!(
                            "`[versions]` key `{name}` is not known to this version of hax; \
                             it is ignored"
                        ));
                        continue;
                    }
                    let Some(version) = value.as_str() else {
                        return Err(format!(
                            "`[versions]` entry `{name}` must be a version string"
                        ));
                    };
                    validate_declared_version(name, version)?;
                    result.versions.insert(name.clone(), version.to_string());
                }
            }
            "project-files" => {
                let Some(enabled) = value.as_bool() else {
                    return Err("`project-files` must be a boolean".into());
                };
                result.project_files = Some(enabled);
            }
            other => {
                warnings.push(format!(
                    "unknown top-level key `{other}` is ignored by this version of hax"
                ));
            }
        }
    }

    Ok((result, warnings))
}

fn parse_tool_entry(
    tool: &str,
    entry: &toml::Value,
    dir: &Path,
    warnings: &mut Vec<String>,
) -> Result<ToolEntry, String> {
    // A pinned version is checked here rather than only where it is
    // installed, so an unusable pin is reported as the configuration error
    // it is, by every command that reads the file.
    let version_entry = |version: &str| {
        super::manifest::validate_version_id(version)
            .map_err(|e| format!("the entry for tool `{tool}` is invalid: {e}"))?;
        Ok(ToolEntry::Version(version.to_string()))
    };
    match entry {
        toml::Value::String(version) => version_entry(version),
        toml::Value::Table(table) => {
            for key in table.keys() {
                if key != "version" && key != "path" {
                    warnings.push(format!(
                        "unknown key `{key}` in the entry for tool `{tool}` is ignored"
                    ));
                }
            }
            let version = table.get("version");
            let path = table.get("path");
            match (version, path) {
                (Some(_), Some(_)) => Err(format!(
                    "the entry for tool `{tool}` declares both `version` and `path`; \
                     declare exactly one"
                )),
                (Some(version), None) => {
                    let Some(version) = version.as_str() else {
                        return Err(format!("`version` of tool `{tool}` must be a string"));
                    };
                    version_entry(version)
                }
                (None, Some(path)) => {
                    let Some(path) = path.as_str() else {
                        return Err(format!("`path` of tool `{tool}` must be a string"));
                    };
                    let path = Path::new(path);
                    let resolved = if path.is_absolute() {
                        path.to_path_buf()
                    } else {
                        dir.join(path)
                    };
                    Ok(ToolEntry::Path(resolved))
                }
                (None, None) => Err(format!(
                    "the entry for tool `{tool}` must declare exactly one of \
                     `version` and `path`"
                )),
            }
        }
        _ => Err(format!(
            "the entry for tool `{tool}` must be a version string or a table \
             with exactly one of `version` and `path`"
        )),
    }
}

/// Validate a `[versions]` value. These versions are not installed by hax,
/// but they are written into the files it generates: a `lean-toolchain`
/// holds one verbatim, and a `lakefile.toml` names one as a `rev`. A value
/// must therefore not be able to restructure those files, which the
/// accepted character set rules out (no quotes, whitespace, comment
/// markers, or control characters), and must not traverse a path.
pub fn validate_declared_version(key: &str, value: &str) -> Result<(), String> {
    let allowed =
        |c: char| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_' | '+' | ':' | '/');
    let valid = !value.is_empty()
        && value.len() <= 128
        && value.chars().all(allowed)
        && !value.contains("..")
        && !value.starts_with(['.', '-', '/'])
        && !value.ends_with('/');
    if valid {
        Ok(())
    } else {
        Err(format!(
            "`{value}` is not a valid value for the `[versions]` entry `{key}`: expected a \
             version, tag, or toolchain name of ASCII alphanumerics and `.-_+:/`"
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_str(contents: &str) -> Result<(HaxToml, Vec<String>), String> {
        parse(Path::new("/project/hax.toml"), contents)
    }

    #[test]
    fn string_and_table_forms_are_equivalent() {
        let (a, w) = parse_str(
            r#"[tools]
aeneas = "nightly-2026.07.01""#,
        )
        .unwrap();
        let (b, _) = parse_str(
            r#"[tools]
aeneas = { version = "nightly-2026.07.01" }"#,
        )
        .unwrap();
        assert!(w.is_empty());
        assert_eq!(a.tools, b.tools);
        assert_eq!(
            a.tools["aeneas"],
            ToolEntry::Version("nightly-2026.07.01".into())
        );
    }

    #[test]
    fn relative_path_resolves_against_defining_dir() {
        let (parsed, _) = parse_str(
            r#"[tools]
charon = { path = "vendor/bin/charon" }"#,
        )
        .unwrap();
        assert_eq!(
            parsed.tools["charon"],
            ToolEntry::Path(PathBuf::from("/project/vendor/bin/charon"))
        );
    }

    #[test]
    fn absolute_path_is_kept() {
        let (parsed, _) = parse_str(
            r#"[tools]
charon = { path = "/usr/bin/charon" }"#,
        )
        .unwrap();
        assert_eq!(
            parsed.tools["charon"],
            ToolEntry::Path(PathBuf::from("/usr/bin/charon"))
        );
    }

    #[test]
    fn version_and_path_together_is_an_error() {
        let err = parse_str(
            r#"[tools]
charon = { version = "x", path = "y" }"#,
        )
        .unwrap_err();
        assert!(err.contains("both `version` and `path`"), "{err}");
    }

    #[test]
    fn neither_version_nor_path_is_an_error() {
        let err = parse_str("[tools]\ncharon = {}").unwrap_err();
        assert!(err.contains("exactly one"), "{err}");
    }

    #[test]
    fn unknown_tool_is_warned_and_skipped() {
        let (parsed, warnings) = parse_str(
            r#"[tools]
lean = "4.31.0""#,
        )
        .unwrap();
        assert!(parsed.tools.is_empty());
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].contains("`lean`"), "{}", warnings[0]);
    }

    #[test]
    fn unknown_entry_key_is_warned() {
        let (parsed, warnings) = parse_str(
            r#"[tools]
charon = { version = "x", features = ["y"] }"#,
        )
        .unwrap();
        assert_eq!(parsed.tools["charon"], ToolEntry::Version("x".into()));
        assert!(warnings.iter().any(|w| w.contains("`features`")));
    }

    #[test]
    fn unknown_top_level_key_is_warned() {
        let (parsed, warnings) = parse_str(r#"hax = "0.3.7""#).unwrap();
        assert!(!parsed.has_entries());
        assert!(warnings.iter().any(|w| w.contains("`hax`")));
    }

    #[test]
    fn versions_table_parses_known_keys() {
        let (parsed, warnings) = parse_str(
            r#"[versions]
lean = "leanprover/lean4:v4.30.0-rc2"
hax-lean-lib = "v0.1.0"
unknown-thing = "1""#,
        )
        .unwrap();
        assert_eq!(parsed.versions.len(), 2);
        assert_eq!(parsed.versions["lean"], "leanprover/lean4:v4.30.0-rc2");
        assert!(warnings.iter().any(|w| w.contains("`unknown-thing`")));
    }

    #[test]
    fn non_string_version_is_an_error() {
        assert!(parse_str("[versions]\nlean = 4").is_err());
    }

    #[test]
    fn tool_versions_are_validated() {
        for entry in [
            r#"charon = "../escape""#,
            r#"charon = "nightly 1""#,
            r#"charon = { version = "a/b" }"#,
            r#"charon = """#,
        ] {
            let err = parse_str(&format!("[tools]\n{entry}")).unwrap_err();
            assert!(err.contains("`charon`"), "{entry}: {err}");
        }
    }

    #[test]
    fn declared_versions_are_validated() {
        let valid = [
            "leanprover/lean4:v4.31.0",
            "v0.2.0",
            "refs/tags/v1",
            "4.31.0-rc2+build_1",
        ];
        for value in valid {
            validate_declared_version("lean", value).unwrap();
        }
        let invalid = [
            // Closing a TOML string and appending to the generated file.
            "v1\"\n[[require]]\nname = \"X\"\ngit = \"https://evil.example/x\"\nrev = \"main",
            "v1 # comment",
            "v1\nsecond-line",
            "../escape",
            "a/../../escape",
            "-leading-dash",
            ".hidden",
            "trailing/",
            "",
        ];
        for value in invalid {
            assert!(
                validate_declared_version("lean", value).is_err(),
                "accepted `{value}`"
            );
        }
        assert!(validate_declared_version("lean", &"v".repeat(129)).is_err());
    }

    /// A `[versions]` value that could restructure a generated file is
    /// rejected where it enters, so no consumer has to defend against it.
    #[test]
    fn injecting_declared_version_is_an_error() {
        let err = parse_str(
            r#"[versions]
hax-lean-lib = "v1\"\ngit = \"https://evil.example/x\"\nrev = \"main""#,
        )
        .unwrap_err();
        assert!(err.contains("`hax-lean-lib`"), "{err}");
    }

    #[test]
    fn project_files_parses_both_values_and_defaults_to_none() {
        let (parsed, warnings) = parse_str("project-files = false").unwrap();
        assert_eq!(parsed.project_files, Some(false));
        assert!(warnings.is_empty());
        let (parsed, _) = parse_str("project-files = true").unwrap();
        assert_eq!(parsed.project_files, Some(true));
        let (parsed, _) = parse_str("").unwrap();
        assert_eq!(parsed.project_files, None);
    }

    #[test]
    fn non_boolean_project_files_is_an_error() {
        let err = parse_str(r#"project-files = "no""#).unwrap_err();
        assert!(err.contains("`project-files`"), "{err}");
    }

    #[test]
    fn empty_file_is_valid() {
        let (parsed, warnings) = parse_str("").unwrap();
        assert!(!parsed.has_entries());
        assert!(warnings.is_empty());
    }
}
