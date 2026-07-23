//! The version manifest embedded at build time.
//!
//! The manifest maps tool name, version, and platform to a download URL,
//! SHA-256 checksum, and optional `entry_points`. Versions it does not
//! list are reachable through per-tool fallback templates: the same shape
//! with a `{version}` placeholder and no checksum. Because the manifest
//! ships inside the binary, resolving a version never requires network
//! access, and manifest and parser are always in step.

use std::collections::BTreeMap;
use std::path::{Component, Path, PathBuf};
use std::sync::OnceLock;

const MANIFEST_TOML: &str = include_str!("../../tools-manifest.toml");

/// Internal override for tests: a path to a manifest file used instead of
/// the embedded one. Not part of the user-facing interface.
pub const MANIFEST_OVERRIDE_ENV: &str = "HAX_TOOLS_MANIFEST";

/// A verified artifact: one tool version on one platform.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct ArtifactEntry {
    pub url: String,
    pub sha256: String,
    /// Executable name to path (relative to the installed version
    /// directory), for archives not following the `bin/<name>` convention.
    #[serde(default)]
    pub entry_points: Option<BTreeMap<String, String>>,
}

/// A fallback template: an [`ArtifactEntry`] shape with `{version}`
/// placeholders and no checksum.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct FallbackTemplate {
    pub url: String,
    #[serde(default)]
    pub entry_points: Option<BTreeMap<String, String>>,
}

#[derive(Debug, Clone, Default, serde::Deserialize)]
pub struct Manifest {
    /// tool name -> version -> platform key -> artifact.
    #[serde(default)]
    pub tools: BTreeMap<String, BTreeMap<String, BTreeMap<String, ArtifactEntry>>>,
    /// tool name -> platform key -> template.
    #[serde(default)]
    pub fallback: BTreeMap<String, BTreeMap<String, FallbackTemplate>>,
}

/// The manifest in effect: the embedded one, unless overridden for tests.
pub fn manifest() -> &'static Manifest {
    static MANIFEST: OnceLock<Manifest> = OnceLock::new();
    MANIFEST.get_or_init(|| {
        let contents = match std::env::var(MANIFEST_OVERRIDE_ENV) {
            Ok(path) => std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("could not read {MANIFEST_OVERRIDE_ENV}={path}: {e}")),
            Err(_) => MANIFEST_TOML.to_string(),
        };
        parse(&contents).unwrap_or_else(|e| panic!("invalid tools manifest: {e}"))
    })
}

pub fn parse(contents: &str) -> Result<Manifest, String> {
    toml::from_str(contents).map_err(|e| e.to_string())
}

/// The platform key of the running binary, derived from its compile-time
/// target: `<os>-<arch>` with `os` in `linux`/`macos` and `arch` in
/// `x86_64`/`aarch64`. Deliberately unrelated to Rust target triples.
pub fn platform_key() -> String {
    format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH)
}

impl Manifest {
    /// The verified artifact for a tool version on a platform, if listed.
    pub fn lookup(&self, tool: &str, version: &str, platform: &str) -> Option<&ArtifactEntry> {
        self.tools.get(tool)?.get(version)?.get(platform)
    }

    /// The versions of a tool listed for verified installation, in the
    /// manifest's (lexicographic, hence chronological for nightly tags)
    /// order.
    pub fn versions_of(&self, tool: &str) -> Vec<&str> {
        self.tools
            .get(tool)
            .map(|versions| versions.keys().map(String::as_str).collect())
            .unwrap_or_default()
    }

    /// Whether a version of a tool is listed for any platform.
    pub fn knows_version(&self, tool: &str, version: &str) -> bool {
        self.tools
            .get(tool)
            .is_some_and(|versions| versions.contains_key(version))
    }

    /// Instantiate the fallback template for a tool version on a platform:
    /// the URL and entry points with `{version}` substituted.
    pub fn fallback_for(
        &self,
        tool: &str,
        version: &str,
        platform: &str,
    ) -> Option<(String, Option<BTreeMap<String, String>>)> {
        let template = self.fallback.get(tool)?.get(platform)?;
        let substitute = |s: &str| s.replace("{version}", version);
        let entry_points = template.entry_points.as_ref().map(|entry_points| {
            entry_points
                .iter()
                .map(|(name, path)| (name.clone(), substitute(path)))
                .collect()
        });
        Some((substitute(&template.url), entry_points))
    }
}

/// Validate an entry-point path from the manifest or an installation's
/// metadata: it must stay inside the version directory it is relative to.
pub fn validate_entry_point(path: &str) -> Result<PathBuf, String> {
    let parsed = Path::new(path);
    if parsed.as_os_str().is_empty()
        || !parsed
            .components()
            .all(|c| matches!(c, Component::Normal(_)))
    {
        return Err(format!(
            "entry point `{path}` must be a relative path inside the version directory"
        ));
    }
    Ok(parsed.to_path_buf())
}

/// Validate a version identifier before it is used as a cache directory
/// name: opaque, but not allowed to traverse the filesystem.
pub fn validate_version_id(version: &str) -> Result<(), String> {
    let valid = !version.is_empty()
        && !version.starts_with('.')
        && version
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_' | '+' | ':'));
    if valid {
        Ok(())
    } else {
        Err(format!("`{version}` is not a valid version identifier"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn embedded_manifest_parses_and_covers_the_defaults() {
        let manifest = parse(MANIFEST_TOML).expect("embedded manifest must parse");
        let defaults = super::super::defaults::defaults();
        for platform in ["linux-x86_64", "macos-x86_64", "macos-aarch64"] {
            for (tool, version) in &defaults.tools {
                let entry = manifest
                    .lookup(tool, version, platform)
                    .unwrap_or_else(|| panic!("manifest lacks {tool} {version} on {platform}"));
                assert_eq!(entry.sha256.len(), 64, "{tool} {platform}: bad sha256");
                assert!(
                    entry.sha256.chars().all(|c| c.is_ascii_hexdigit()),
                    "{tool} {platform}: bad sha256"
                );
                assert!(entry.url.starts_with("https://"), "{tool} {platform}");
                // Entry points, when present, must be valid relative paths
                // and cover every executable of the tool.
                if let Some(entry_points) = &entry.entry_points {
                    for path in entry_points.values() {
                        validate_entry_point(path).unwrap();
                    }
                    for executable in super::super::tool_executables(tool) {
                        assert!(
                            entry_points.contains_key(*executable),
                            "{tool} {platform}: no entry point for `{executable}`"
                        );
                    }
                }
                // The fallback template must exist and substitute cleanly.
                let (url, _) = manifest.fallback_for(tool, version, platform).unwrap();
                assert!(!url.contains("{version}"));
                assert!(url.contains(version));
            }
        }
    }

    #[test]
    fn platform_key_is_os_dash_arch() {
        let key = platform_key();
        let (os, arch) = key.split_once('-').unwrap();
        assert!(
            ["linux", "macos"].contains(&os)
                || !cfg!(any(target_os = "linux", target_os = "macos"))
        );
        assert!(!arch.is_empty());
    }

    #[test]
    fn fallback_substitutes_version_in_url_and_entry_points() {
        let manifest = parse(
            r#"[fallback.charon.linux-x86_64]
url = "https://example.com/{version}/charon-{version}.tar.gz"
entry_points = { charon = "charon-{version}/bin/charon" }
"#,
        )
        .unwrap();
        let (url, entry_points) = manifest
            .fallback_for("charon", "nightly-1", "linux-x86_64")
            .unwrap();
        assert_eq!(url, "https://example.com/nightly-1/charon-nightly-1.tar.gz");
        assert_eq!(
            entry_points.unwrap()["charon"],
            "charon-nightly-1/bin/charon"
        );
        assert!(
            manifest
                .fallback_for("aeneas", "x", "linux-x86_64")
                .is_none()
        );
    }

    #[test]
    fn entry_point_escapes_are_rejected() {
        assert!(validate_entry_point("bin/charon").is_ok());
        assert!(validate_entry_point("charon").is_ok());
        assert!(validate_entry_point("../outside").is_err());
        assert!(validate_entry_point("a/../../outside").is_err());
        assert!(validate_entry_point("/absolute").is_err());
        assert!(validate_entry_point("").is_err());
        assert!(validate_entry_point("./x").is_err());
    }

    #[test]
    fn version_ids_are_validated() {
        assert!(validate_version_id("nightly-2026.07.01").is_ok());
        assert!(validate_version_id("v1.2.3+build_4").is_ok());
        assert!(validate_version_id("leanprover/lean4:v4.30.0-rc2").is_err());
        assert!(validate_version_id("../escape").is_err());
        assert!(validate_version_id("a/b").is_err());
        assert!(validate_version_id(".hidden").is_err());
        assert!(validate_version_id("").is_err());
    }

    #[test]
    fn unknown_manifest_fields_are_ignored() {
        let manifest = parse(
            r#"future_top_level = 1
[tools.charon."v1".linux-x86_64]
url = "https://example.com/a.tar.gz"
sha256 = "00"
future_field = "x"
"#,
        )
        .unwrap();
        assert!(manifest.knows_version("charon", "v1"));
    }
}
