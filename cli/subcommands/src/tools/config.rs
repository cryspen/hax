//! Parsing of `hax.toml` files.
//!
//! A `hax.toml` carries a `[tools]` table (managed tools, pinned by version
//! or pointed at a local binary by path) and a `[versions]` table
//! (declared-only versions). Unknown top-level keys, unknown tools, and
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
                    result.versions.insert(name.clone(), version.to_string());
                }
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
    match entry {
        toml::Value::String(version) => Ok(ToolEntry::Version(version.clone())),
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
                    Ok(ToolEntry::Version(version.to_string()))
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
    fn empty_file_is_valid() {
        let (parsed, warnings) = parse_str("").unwrap();
        assert!(!parsed.has_entries());
        assert!(warnings.is_empty());
    }
}
