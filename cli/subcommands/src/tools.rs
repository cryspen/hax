//! Version management for hax's external tools.
//!
//! Projects declare the tool versions they require in a `hax.toml` at the
//! workspace root (with optional per-member-crate overrides). Resolution
//! follows, from highest to lowest precedence: the `HAX_<TOOL>_BINARY`
//! environment variable, the member crate's `hax.toml`, the workspace-root
//! `hax.toml`, and the built-in defaults embedded in this binary.

use hax_types::cli_options::{MessageFormat, ToolsCommand};

pub mod cache;
pub mod config;
pub mod defaults;
pub mod haxlib;
pub mod install;
pub mod manifest;
pub mod project;
pub mod resolve;
mod subcommands;

/// The tools whose installation hax manages. A `[tools]` entry naming
/// anything else is warned about and skipped.
pub const MANAGED_TOOLS: &[&str] = &["aeneas", "charon"];

/// The declared-only `[versions]` keys: versions hax must know without
/// managing an installation.
pub const DECLARED_VERSION_KEYS: &[&str] = &["lean", "hax-lean-lib"];

/// The executables a managed tool comprises. The first one carries the
/// tool's name.
pub fn tool_executables(tool: &str) -> &'static [&'static str] {
    match tool {
        "aeneas" => &["aeneas"],
        "charon" => &["charon", "charon-driver"],
        _ => &[],
    }
}

/// The outcome of [`provide_tool`]: the tool's executables and the
/// resolution that selected them, so a caller that also needs the resolved
/// version or path (e.g. to pin a matching library) reuses it rather than
/// resolving the tool a second time.
pub struct Provided {
    /// Each of the tool's executables, by name, as an absolute path.
    pub executables: std::collections::BTreeMap<&'static str, std::path::PathBuf>,
    /// How the tool resolved.
    pub resolution: resolve::Resolution,
}

/// Resolve a managed tool for one crate and make its executables
/// available, installing into the cache on demand. Returns the path of
/// each of the tool's executables, together with the resolution.
///
/// A version resolution installs through the manifest-verified pipeline
/// and locates executables inside the cached version directory. A path
/// resolution (`HAX_<TOOL>_BINARY` or a `path` entry in `hax.toml`) points
/// at the executable whose name matches the tool; the remaining
/// executables are resolved by name in the same directory, and a missing
/// sibling is an error. Whenever the resolution deviates from the built-in
/// default, a one-line notice names the version this release was tested
/// with.
pub fn provide_tool(
    tool: &str,
    member: Option<&config::HaxToml>,
    workspace: Option<&config::HaxToml>,
    message_format: MessageFormat,
) -> Result<Provided, String> {
    use hax_types::diagnostics::message::HaxMessage;

    let defaults = defaults::defaults();
    let resolution = resolve::resolve_tool(tool, member, workspace, defaults);
    let default_version = &defaults.tools[tool];
    let notice = |used: String| {
        HaxMessage::NonDefaultToolVersion {
            tool: tool.to_string(),
            used,
            tested: default_version.clone(),
        }
        .report(message_format, None);
    };

    let mut executables = std::collections::BTreeMap::new();
    match &resolution.kind {
        resolve::Resolved::Version(version) => {
            if version != default_version {
                notice(version.clone());
            }
            // A fresh unverified install already warns during download; warn
            // too when reusing an unverified copy from the cache, so the
            // missing-checksum status is not silently dropped on later runs.
            if matches!(
                install::ensure_installed(tool, version, false, message_format)?,
                install::Installed::AlreadyCached { verified: false }
            ) {
                HaxMessage::CachedUnverifiedToolInUse {
                    tool: tool.to_string(),
                    version: version.clone(),
                }
                .report(message_format, None);
            }
            let dir = cache::version_dir(tool, version)?;
            for executable in tool_executables(tool) {
                executables.insert(*executable, cache::executable_path(&dir, executable)?);
            }
        }
        resolve::Resolved::Path(path) => {
            if !path.is_file() {
                return Err(format!(
                    "no executable at {} ({})",
                    path.display(),
                    resolution.source.describe()
                ));
            }
            let dir = path
                .parent()
                .ok_or_else(|| format!("{} has no parent directory", path.display()))?;
            for executable in tool_executables(tool) {
                let sibling = if *executable == tool {
                    path.clone()
                } else {
                    dir.join(executable)
                };
                if !sibling.is_file() {
                    return Err(format!(
                        "`{tool}` comprises the executables {}; `{executable}` was not \
                         found next to the overriding binary (expected {})",
                        tool_executables(tool).join(", "),
                        sibling.display()
                    ));
                }
                executables.insert(*executable, sibling);
            }
            // Announce the override only once it is known to be usable, so a
            // broken path yields the error alone rather than a notice first.
            notice(format!(
                "at {} ({})",
                path.display(),
                resolution.source.describe()
            ));
        }
    }
    Ok(Provided {
        executables,
        resolution,
    })
}

/// Entry point for `cargo hax tools <subcommand>`. Returns the process
/// exit code.
pub fn run(command: &ToolsCommand, message_format: MessageFormat) -> i32 {
    match command {
        ToolsCommand::Show => subcommands::show(message_format),
        ToolsCommand::Install { spec, force } => {
            subcommands::install(spec.as_deref(), *force, message_format)
        }
        ToolsCommand::List {
            tool,
            installed,
            all,
        } => subcommands::list(tool.as_deref(), *installed, *all, message_format),
    }
}
