//! Version resolution: which version (or local path) of a tool applies to a
//! given crate.
//!
//! Precedence, highest to lowest:
//! 1. the `HAX_<TOOL>_BINARY` environment variable,
//! 2. the entry in the member crate's `hax.toml`,
//! 3. the entry in the workspace-root `hax.toml`,
//! 4. the built-in default shipped with this release.
//!
//! Declared-only `[versions]` entries resolve through levels 2 to 4 of the
//! same order; no environment override exists for them.

use std::path::PathBuf;

use super::config::{HaxToml, ToolEntry};
use super::defaults::Defaults;

/// Where a resolution came from, for `tools show` and notices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    /// A `HAX_<TOOL>_BINARY` override.
    EnvOverride { var: String },
    /// An entry in the member crate's own `hax.toml`.
    MemberPin { file: PathBuf },
    /// An entry in the workspace-root `hax.toml`.
    WorkspacePin { file: PathBuf },
    /// The built-in default shipped with this release.
    Default,
}

/// What a tool resolved to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolved {
    Version(String),
    Path(PathBuf),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Resolution {
    pub kind: Resolved,
    pub source: Source,
}

/// The override variable for a tool: `HAX_<TOOL>_BINARY`.
pub fn env_var_for(tool: &str) -> String {
    format!("HAX_{}_BINARY", tool.to_uppercase().replace('-', "_"))
}

/// Check the override environment variable for a tool.
fn env_override(tool: &str) -> Option<Resolution> {
    let var = env_var_for(tool);
    let path = std::env::var(&var).ok()?;
    Some(Resolution {
        kind: Resolved::Path(PathBuf::from(path)),
        source: Source::EnvOverride { var },
    })
}

/// Resolve a managed tool for one crate. `member` is the crate's own
/// `hax.toml` (if any), `workspace` the workspace-root one.
pub fn resolve_tool(
    tool: &str,
    member: Option<&HaxToml>,
    workspace: Option<&HaxToml>,
    defaults: &Defaults,
) -> Resolution {
    if let Some(resolution) = env_override(tool) {
        return resolution;
    }
    for (config, source) in [
        (member, Source::member as fn(&HaxToml) -> Source),
        (workspace, Source::workspace as fn(&HaxToml) -> Source),
    ] {
        if let Some(config) = config
            && let Some(entry) = config.tools.get(tool)
        {
            let kind = match entry {
                ToolEntry::Version(version) => Resolved::Version(version.clone()),
                ToolEntry::Path(path) => Resolved::Path(path.clone()),
            };
            return Resolution {
                kind,
                source: source(config),
            };
        }
    }
    let version = defaults
        .tools
        .get(tool)
        .unwrap_or_else(|| panic!("no built-in default version for tool `{tool}`"))
        .clone();
    Resolution {
        kind: Resolved::Version(version),
        source: Source::Default,
    }
}

/// Resolve a declared-only `[versions]` entry for one crate.
pub fn resolve_version(
    key: &str,
    member: Option<&HaxToml>,
    workspace: Option<&HaxToml>,
    defaults: &Defaults,
) -> Resolution {
    for (config, source) in [
        (member, Source::member as fn(&HaxToml) -> Source),
        (workspace, Source::workspace as fn(&HaxToml) -> Source),
    ] {
        if let Some(config) = config
            && let Some(version) = config.versions.get(key)
        {
            return Resolution {
                kind: Resolved::Version(version.clone()),
                source: source(config),
            };
        }
    }
    let version = defaults
        .versions
        .get(key)
        .unwrap_or_else(|| panic!("no built-in default for `[versions]` key `{key}`"))
        .clone();
    Resolution {
        kind: Resolved::Version(version),
        source: Source::Default,
    }
}

impl Source {
    fn member(config: &HaxToml) -> Self {
        Source::MemberPin {
            file: config.path.clone(),
        }
    }
    fn workspace(config: &HaxToml) -> Self {
        Source::WorkspacePin {
            file: config.path.clone(),
        }
    }

    /// A short human-readable description, used by `tools show`.
    pub fn describe(&self) -> String {
        match self {
            Source::EnvOverride { var } => format!("env {var}"),
            Source::MemberPin { file } | Source::WorkspacePin { file } => {
                format!("pinned in {}", file.display())
            }
            Source::Default => "default".into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use std::path::Path;

    fn defaults() -> Defaults {
        Defaults {
            tools: BTreeMap::from([
                ("aeneas".to_string(), "default-aeneas".to_string()),
                ("charon".to_string(), "default-charon".to_string()),
            ]),
            versions: BTreeMap::from([("lean".to_string(), "default-lean".to_string())]),
        }
    }

    fn config(path: &str, contents: &str) -> HaxToml {
        super::super::config::parse(Path::new(path), contents)
            .unwrap()
            .0
    }

    #[test]
    fn precedence_member_over_workspace_over_default() {
        let workspace = config(
            "/ws/hax.toml",
            "[tools]\ncharon = \"ws-charon\"\naeneas = \"ws-aeneas\"",
        );
        let member = config("/ws/crate/hax.toml", "[tools]\ncharon = \"member-charon\"");
        let defaults = defaults();

        // Member wins for the tool it mentions.
        let r = resolve_tool("charon", Some(&member), Some(&workspace), &defaults);
        assert_eq!(r.kind, Resolved::Version("member-charon".into()));
        assert!(matches!(r.source, Source::MemberPin { .. }));

        // A tool the member file does not mention keeps resolving through
        // the workspace root.
        let r = resolve_tool("aeneas", Some(&member), Some(&workspace), &defaults);
        assert_eq!(r.kind, Resolved::Version("ws-aeneas".into()));
        assert!(matches!(r.source, Source::WorkspacePin { .. }));

        // No entry anywhere: built-in default.
        let r = resolve_tool("aeneas", None, None, &defaults);
        assert_eq!(r.kind, Resolved::Version("default-aeneas".into()));
        assert_eq!(r.source, Source::Default);
    }

    #[test]
    fn path_entries_resolve_as_paths() {
        let workspace = config(
            "/ws/hax.toml",
            "[tools]\ncharon = { path = \"bin/charon\" }",
        );
        let r = resolve_tool("charon", None, Some(&workspace), &defaults());
        assert_eq!(r.kind, Resolved::Path("/ws/bin/charon".into()));
    }

    #[test]
    fn versions_resolve_without_env_level() {
        let workspace = config("/ws/hax.toml", "[versions]\nlean = \"ws-lean\"");
        let r = resolve_version("lean", None, Some(&workspace), &defaults());
        assert_eq!(r.kind, Resolved::Version("ws-lean".into()));
        let r = resolve_version("lean", None, None, &defaults());
        assert_eq!(r.kind, Resolved::Version("default-lean".into()));
    }

    #[test]
    fn env_var_names() {
        assert_eq!(env_var_for("charon"), "HAX_CHARON_BINARY");
        assert_eq!(env_var_for("aeneas"), "HAX_AENEAS_BINARY");
    }
}
