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
        // No entries beyond the known sets: defaults must be resolvable.
        for tool in defaults.tools.keys() {
            assert!(super::super::MANAGED_TOOLS.contains(&tool.as_str()));
        }
        for key in defaults.versions.keys() {
            assert!(super::super::DECLARED_VERSION_KEYS.contains(&key.as_str()));
        }
    }

    /// Until `pins.toml` is retired, the embedded defaults must agree with
    /// it: both are consumed (by `hax_types::pins` and by this module
    /// respectively) and silently diverging pins would be confusing.
    #[test]
    fn defaults_agree_with_pins_toml() {
        let pins_path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../pins.toml");
        let pins: toml::Table = std::fs::read_to_string(pins_path)
            .expect("pins.toml not found next to the workspace root")
            .parse()
            .expect("pins.toml is not valid TOML");
        let pin = |table: &str, key: &str| -> String {
            pins[table][key]
                .as_str()
                .unwrap_or_else(|| panic!("pins.toml [{table}].{key} is not a string"))
                .to_string()
        };
        let defaults = defaults();
        assert_eq!(defaults.tools["aeneas"], pin("aeneas", "tag"));
        assert_eq!(defaults.tools["charon"], pin("charon", "tag"));
        assert_eq!(defaults.versions["lean"], pin("lean", "toolchain"));
        assert_eq!(
            defaults.versions["hax-lean-lib"],
            pin("hax-lean-lib", "version")
        );
    }
}
