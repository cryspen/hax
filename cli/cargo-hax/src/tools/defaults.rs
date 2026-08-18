//! The built-in default tool versions, embedded at build time.
//!
//! `defaults.toml` follows the schema of a project's `hax.toml`; it names
//! the version of each managed tool and each declared-only entry that this
//! release of hax was built and tested against.

use std::collections::BTreeMap;
use std::sync::OnceLock;

const DEFAULTS_TOML: &str = include_str!("../../defaults.toml");

/// The default versions shipped with this release.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct Defaults {
    pub tools: BTreeMap<String, String>,
    pub versions: BTreeMap<String, String>,
    /// The built-in default opaque set of each backend, applied to proof
    /// scenarios (`[scenario-defaults.<backend>]`).
    #[serde(default, rename = "scenario-defaults")]
    pub scenario_defaults: BTreeMap<super::config::ScenarioBackend, ScenarioDefaults>,
}

/// One built-in `[scenario-defaults.<backend>]` table.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct ScenarioDefaults {
    #[serde(default)]
    pub opaque: Vec<String>,
}

/// The parsed embedded defaults. Panics only if the embedded file is
/// malformed, which is a build defect caught by the tests below.
pub fn defaults() -> &'static Defaults {
    static DEFAULTS: OnceLock<Defaults> = OnceLock::new();
    DEFAULTS
        .get_or_init(|| toml::from_str(DEFAULTS_TOML).expect("embedded defaults.toml is malformed"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn embedded_defaults_parse_and_cover_all_tools() {
        let defaults = defaults();
        for tool in super::super::MANAGED_TOOLS {
            assert!(
                defaults.tools.contains_key(*tool),
                "defaults.toml lacks a default version for managed tool `{tool}`"
            );
        }
        for key in super::super::DECLARED_VERSION_KEYS {
            assert!(
                defaults.versions.contains_key(*key),
                "defaults.toml lacks a default for `[versions]` key `{key}`"
            );
        }
        // `defaults.toml` is deserialized directly rather than through
        // `config::parse`, so its `[versions]` values are checked here.
        for (key, value) in &defaults.versions {
            super::super::config::validate_declared_version(key, value).unwrap();
        }
        // No entries beyond the known sets: defaults must be resolvable.
        for tool in defaults.tools.keys() {
            assert!(super::super::MANAGED_TOOLS.contains(&tool.as_str()));
        }
        for key in defaults.versions.keys() {
            assert!(super::super::DECLARED_VERSION_KEYS.contains(&key.as_str()));
        }
    }

    /// The version of `hax-lean-lib` in `defaults.toml` must be the same as the version
    /// declared in `hax-lib/proof-libs/lean/lakefile.toml`.
    #[test]
    fn hax_lean_lib_pin_matches_declared_version() {
        let lean_lib =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../hax-lib/proof-libs/lean");
        // Nix builds this crate from a filtered source tree that drops
        // `proof-libs`. In such a situation, we need to skip this test:
        if !lean_lib.is_dir() {
            return;
        }
        let path = lean_lib.join("lakefile.toml");
        let contents = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        let lakefile: toml::Value = toml::from_str(&contents)
            .unwrap_or_else(|e| panic!("{} is malformed: {e}", path.display()));
        let declared = lakefile
            .get("version")
            .and_then(toml::Value::as_str)
            .unwrap_or_else(|| panic!("{} declares no `version`", path.display()));

        let pinned = &defaults().versions["hax-lean-lib"];
        assert_eq!(
            pinned,
            &format!("v{declared}"),
            "`hax-lean-lib` in defaults.toml must pin the version declared in {}",
            path.display()
        );
    }
}
