//! Handlers for the `cargo hax tools` subcommands.

use std::collections::BTreeSet;

use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::{
    HaxLibStatus, HaxMessage, InstallStatus, InstalledTool, MemberOverride, ResolvedValue,
    ToolListing, ToolResolution, ToolVersionListing,
};

use super::defaults::defaults;
use super::install::{Installed, ensure_installed};
use super::project::{ProjectContext, ProjectLayout};
use super::resolve::{Resolution, Resolved, resolve_tool, resolve_version};
use super::{DECLARED_VERSION_KEYS, MANAGED_TOOLS, cache, manifest};

fn error(message: String, message_format: MessageFormat) -> i32 {
    HaxMessage::GenericError { message }.report(message_format, None);
    1
}

/// A resolution as it is reported, for a named entry.
fn reported(name: &str, resolution: &Resolution) -> ToolResolution {
    ToolResolution {
        name: name.to_string(),
        resolved: match &resolution.kind {
            Resolved::Version(version) => ResolvedValue::Version(version.clone()),
            Resolved::Path(path) => ResolvedValue::Path(path.display().to_string()),
        },
        source: resolution.source.describe(),
    }
}

/// `cargo hax tools install`: populate the machine-wide cache.
///
/// With a `<tool>@<version>` argument, installs exactly that; without one,
/// resolves the current project's configuration and installs the union
/// across all workspace crates: pins, member overrides, and defaults.
pub fn install(spec: Option<&str>, force: bool, message_format: MessageFormat) -> i32 {
    let requests: Vec<(String, String)> = match spec {
        Some(spec) => match parse_spec(spec) {
            Ok(request) => vec![request],
            Err(message) => return error(message, message_format),
        },
        None => {
            let ctx = match ProjectContext::load(message_format) {
                Ok(ctx) => ctx,
                Err(message) => return error(message, message_format),
            };
            let workspace = ctx.workspace_config.as_ref();
            let defaults = defaults();
            let mut versions = BTreeSet::new();
            for tool in MANAGED_TOOLS {
                // The workspace-wide resolution, plus each member's: the
                // cache must cover whatever any member's processing
                // resolves to.
                let mut resolutions = vec![resolve_tool(tool, None, workspace, defaults)];
                for member in &ctx.members {
                    if member.config.is_some() {
                        resolutions.push(resolve_tool(
                            tool,
                            member.config.as_ref(),
                            workspace,
                            defaults,
                        ));
                    }
                }
                for resolution in resolutions {
                    match resolution.kind {
                        Resolved::Version(version) => {
                            versions.insert((tool.to_string(), version));
                        }
                        // The committed configuration itself states that
                        // this binary is provided outside the cache.
                        Resolved::Path(path) => {
                            HaxMessage::GenericWarning {
                                message: format!(
                                    "tool `{tool}` resolves to the path {} ({}); \
                                     nothing to install for it",
                                    path.display(),
                                    resolution.source.describe(),
                                ),
                            }
                            .report(message_format, None);
                        }
                    }
                }
            }
            versions.into_iter().collect()
        }
    };

    let mut failed = false;
    let mut installed = Vec::new();
    for (tool, version) in &requests {
        match ensure_installed(tool, version, force, message_format) {
            Ok(outcome) => installed.push(InstalledTool {
                tool: tool.clone(),
                version: version.clone(),
                status: match outcome {
                    Installed::AlreadyCached { verified } => InstallStatus::Cached { verified },
                    Installed::Fresh { verified } => InstallStatus::Installed { verified },
                },
            }),
            Err(message) => {
                failed = true;
                HaxMessage::GenericError {
                    message: format!("could not install {tool} {version}: {message}"),
                }
                .report(message_format, None);
            }
        }
    }
    HaxMessage::ToolsInstalled { installed }.report(message_format, None);
    if failed { 1 } else { 0 }
}

/// Parse a `<tool>@<version>` specification naming a managed tool.
fn parse_spec(spec: &str) -> Result<(String, String), String> {
    let Some((tool, version)) = spec.split_once('@') else {
        return Err(format!(
            "`{spec}` is not a `<tool>@<version>` specification"
        ));
    };
    if !MANAGED_TOOLS.contains(&tool) {
        return Err(format!(
            "`{tool}` is not a managed tool (managed tools: {})",
            MANAGED_TOOLS.join(", ")
        ));
    }
    if version.is_empty() {
        return Err(format!("`{spec}` lacks a version"));
    }
    Ok((tool.to_string(), version.to_string()))
}

/// `cargo hax tools remove`: delete a version from the machine-wide
/// cache. Removal is safe at any time: a later run that needs the version
/// re-downloads it.
pub fn remove(spec: &str, message_format: MessageFormat) -> i32 {
    let (tool, version) = match parse_spec(spec) {
        Ok(request) => request,
        Err(message) => return error(message, message_format),
    };
    match cache::remove_version(&tool, &version) {
        Ok(cache::Removal {
            result: true,
            leftover,
        }) => {
            if let Some(message) = leftover {
                HaxMessage::GenericWarning { message }.report(message_format, None);
            }
            HaxMessage::ToolRemoved { tool, version }.report(message_format, None);
            0
        }
        Ok(cache::Removal { result: false, .. }) => error(
            format!("{tool} {version} is not in the cache; nothing to remove"),
            message_format,
        ),
        Err(message) => error(
            format!("could not remove {tool} {version}: {message}"),
            message_format,
        ),
    }
}

/// `cargo hax tools clean`: delete the entire tool cache. Idempotent:
/// cleaning an empty or absent cache succeeds and reports zero removals.
pub fn clean(message_format: MessageFormat) -> i32 {
    match cache::clean() {
        Ok(cache::Removal {
            result: removed,
            leftover,
        }) => {
            if let Some(message) = leftover {
                HaxMessage::GenericWarning { message }.report(message_format, None);
            }
            HaxMessage::ToolsCleaned { removed }.report(message_format, None);
            0
        }
        Err(message) => error(
            format!("could not clean the tool cache: {message}"),
            message_format,
        ),
    }
}

/// `cargo hax tools pin`: write pins into `hax.toml`, creating the file
/// when missing. Without an argument, pins this release's defaults, which
/// is also how a project moves its pins forward after updating hax; with
/// one, sets a single entry. Nothing is installed.
pub fn pin(spec: Option<&str>, message_format: MessageFormat) -> i32 {
    use super::pin::{Pin, Table};

    let defaults = defaults();
    let pins: Vec<Pin> = match spec {
        Some(spec) => {
            let Some((name, version)) = spec.split_once('@') else {
                return error(
                    format!("`{spec}` is not a `<name>@<version>` specification"),
                    message_format,
                );
            };
            let table = if MANAGED_TOOLS.contains(&name) {
                Table::Tools
            } else if DECLARED_VERSION_KEYS.contains(&name) {
                Table::Versions
            } else {
                return error(
                    format!(
                        "`{name}` is not a pinnable name (tools: {}; versions: {})",
                        MANAGED_TOOLS.join(", "),
                        DECLARED_VERSION_KEYS.join(", ")
                    ),
                    message_format,
                );
            };
            let validation = match table {
                Table::Tools => manifest::validate_version_id(version),
                Table::Versions => super::config::validate_declared_version(name, version),
            };
            if let Err(message) = validation {
                return error(message, message_format);
            }
            // A version the manifest does not list is written anyway: it
            // may postdate this release. Installing it will go through the
            // unverified fallback, so say so now, at pin time.
            if table == Table::Tools && !manifest::manifest().knows_version(name, version) {
                HaxMessage::GenericWarning {
                    message: format!(
                        "{name} {version} is not in this release's manifest; installing \
                         it will go through the unverified fallback"
                    ),
                }
                .report(message_format, None);
            }
            vec![Pin {
                table,
                name: name.to_string(),
                version: version.to_string(),
            }]
        }
        None => MANAGED_TOOLS
            .iter()
            .map(|tool| Pin {
                table: Table::Tools,
                name: tool.to_string(),
                version: defaults.tools[*tool].clone(),
            })
            .chain(DECLARED_VERSION_KEYS.iter().map(|key| Pin {
                table: Table::Versions,
                name: key.to_string(),
                version: defaults.versions[*key].clone(),
            }))
            .collect(),
    };

    // Only the project layout is needed, not its configuration: pinning
    // must work on a `hax.toml` that configuration loading rejects, since
    // rewriting an entry is how such a file is repaired.
    let layout = match ProjectLayout::load(message_format) {
        Ok(layout) => layout,
        Err(message) => return error(message, message_format),
    };
    let target_dir = pin_target_dir(&layout);
    let path = target_dir.join("hax.toml");
    let contents = match std::fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => {
            return error(
                format!("could not read {}: {e}", path.display()),
                message_format,
            );
        }
    };
    let outcome = match super::pin::apply(&contents, &pins) {
        Ok(outcome) => outcome,
        Err(message) => {
            return error(
                format!("could not edit {}: {message}", path.display()),
                message_format,
            );
        }
    };
    // The named entry of a `<name>@<version>` invocation was not written,
    // so the request was not satisfied. The bare form pins whatever it can:
    // a path entry there is the committed configuration doing its job, and
    // is reported as a skip.
    if spec.is_some() && outcome.changes.is_empty() && !outcome.skipped_paths.is_empty() {
        return error(
            format!(
                "tool `{}` is pinned to a path; nothing was written to {}",
                outcome.skipped_paths.join(", "),
                path.display()
            ),
            message_format,
        );
    }
    // The override is announced only when one is actually written: a run
    // that changes nothing writes no file to warn about.
    if !outcome.changes.is_empty() {
        if target_dir != layout.workspace_root {
            HaxMessage::GenericWarning {
                message: format!(
                    "writing a per-crate override for the member crate at {}; \
                     run `cargo hax tools pin` at {} to pin the whole project",
                    target_dir.display(),
                    layout.workspace_root.display(),
                ),
            }
            .report(message_format, None);
        }
        if let Err(e) = std::fs::write(&path, &outcome.contents) {
            return error(
                format!("could not write {}: {e}", path.display()),
                message_format,
            );
        }
    }
    HaxMessage::ToolsPinned {
        path,
        changes: outcome.changes,
        skipped: outcome.skipped_paths,
    }
    .report(message_format, None);
    0
}

/// The directory whose `hax.toml` `pin` edits: the member crate the
/// invocation directory is inside, if any (authoring an override for that
/// crate), the workspace root otherwise. This is the one place where the
/// invocation directory matters: reading never depends on it, but an
/// override is written standing in the crate that wants it.
fn pin_target_dir(layout: &ProjectLayout) -> std::path::PathBuf {
    // `cargo metadata` reports canonical paths; canonicalize the invocation
    // directory too, as the stray-file check does.
    let Ok(invocation_dir) = std::env::current_dir().and_then(std::fs::canonicalize) else {
        return layout.workspace_root.clone();
    };
    layout
        .member_roots
        .iter()
        .filter(|root| **root != layout.workspace_root)
        .filter(|root| invocation_dir.starts_with(root))
        .max_by_key(|root| root.components().count())
        .cloned()
        .unwrap_or_else(|| layout.workspace_root.clone())
}

/// How many versions per tool `list` shows without `--all`.
const LIST_RECENT: usize = 10;

/// `cargo hax tools list`: the versions installable with verification, as
/// recorded in the embedded manifest, plus locally cached ones. Machine
/// wide: works outside a Cargo project.
pub fn list(
    tool: Option<&str>,
    installed_only: bool,
    all: bool,
    message_format: MessageFormat,
) -> i32 {
    let tools: Vec<&str> = match tool {
        Some(tool) if !MANAGED_TOOLS.contains(&tool) => {
            return error(
                format!(
                    "`{tool}` is not a managed tool (managed tools: {})",
                    MANAGED_TOOLS.join(", ")
                ),
                message_format,
            );
        }
        Some(tool) => vec![tool],
        None => MANAGED_TOOLS.to_vec(),
    };

    let manifest = manifest::manifest();
    let defaults = defaults();
    let mut report = Vec::new();
    for tool in tools {
        let installed: BTreeSet<String> = cache::installed_versions(tool).into_iter().collect();
        let default = defaults.tools.get(tool);

        // The manifest's versions and any cached ones, merged into one list,
        // newest first. A version installed through the fallback path can be
        // newer than the manifest, so the two sets are sorted together rather
        // than concatenated. Lexicographic order matches release order for
        // the `nightly-YYYY.MM.DD` tags in use.
        let mut all_versions: BTreeSet<String> = BTreeSet::new();
        all_versions.extend(manifest.versions_of(tool).into_iter().map(String::from));
        all_versions.extend(installed.iter().cloned());
        let ordered: Vec<String> = all_versions.into_iter().rev().collect();

        let recent = if all { ordered.len() } else { LIST_RECENT };
        let mut versions = Vec::new();
        let mut omitted = 0;
        for (index, version) in ordered.iter().enumerate() {
            let is_installed = installed.contains(version);
            if installed_only && !is_installed {
                continue;
            }
            let is_default = default == Some(version);
            // Installed and default versions are always shown; the rest are
            // truncated to the most recent ones.
            if index >= recent && !is_installed && !is_default {
                omitted += 1;
                continue;
            }
            versions.push(ToolVersionListing {
                version: version.clone(),
                installed: is_installed,
                in_manifest: manifest.knows_version(tool, version),
                default: is_default,
                // Whether the cached copy was checksum-verified at install
                // time, read from its metadata; a fallback install records
                // `false`.
                verified: is_installed
                    && cache::version_dir(tool, version)
                        .ok()
                        .and_then(|dir| cache::read_metadata(&dir).ok().flatten())
                        .and_then(|metadata| metadata.checksum_verified)
                        .unwrap_or(false),
            });
        }
        report.push(ToolListing {
            tool: tool.to_string(),
            versions,
            omitted,
        });
    }

    HaxMessage::ToolsList {
        tools: report,
        installed_only,
    }
    .report(message_format, None);
    0
}

/// `cargo hax tools show`: report which tool versions are active in the
/// current project and where each one comes from.
pub fn show(message_format: MessageFormat) -> i32 {
    let ctx = match ProjectContext::load(message_format) {
        Ok(ctx) => ctx,
        Err(message) => {
            HaxMessage::GenericError { message }.report(message_format, None);
            return 1;
        }
    };

    let workspace = ctx.workspace_config.as_ref();
    let defaults = defaults();

    // The workspace-wide resolution: what a crate without overrides gets.
    let mut tools = Vec::new();
    for tool in MANAGED_TOOLS {
        let resolution = resolve_tool(tool, None, workspace, defaults);
        tools.push((tool.to_string(), resolution));
    }
    let mut versions = Vec::new();
    for key in DECLARED_VERSION_KEYS {
        versions.push((
            key.to_string(),
            resolve_version(key, None, workspace, defaults),
        ));
    }

    // Per overriding member crate: only the entries whose resolution differs.
    let mut member_reports = Vec::new();
    for member in &ctx.members {
        if member.config.is_none() {
            continue;
        }
        let member_cfg = member.config.as_ref();
        let differing_tools: Vec<_> = MANAGED_TOOLS
            .iter()
            .map(|tool| {
                (
                    tool.to_string(),
                    resolve_tool(tool, member_cfg, workspace, defaults),
                )
            })
            .filter(|(tool, resolution)| tools.iter().any(|(t, r)| t == tool && r != resolution))
            .collect();
        let differing_versions: Vec<_> = DECLARED_VERSION_KEYS
            .iter()
            .map(|key| {
                (
                    key.to_string(),
                    resolve_version(key, member_cfg, workspace, defaults),
                )
            })
            .filter(|(key, resolution)| versions.iter().any(|(k, r)| k == key && r != resolution))
            .collect();
        if !differing_tools.is_empty() || !differing_versions.is_empty() {
            member_reports.push((member.name.clone(), differing_tools, differing_versions));
        }
    }

    // The hax-lib compatibility of every crate with a direct dependency.
    let hax_lib = super::haxlib::check(&ctx)
        .into_iter()
        .map(|result| HaxLibStatus {
            crate_name: result.crate_name,
            version: result.found,
            compatibility: result.compatibility,
        })
        .collect();

    let reported_entries = |entries: &[(String, Resolution)]| {
        entries
            .iter()
            .map(|(name, resolution)| reported(name, resolution))
            .collect()
    };
    HaxMessage::ToolsShow {
        tools: reported_entries(&tools),
        versions: reported_entries(&versions),
        hax_lib,
        member_overrides: member_reports
            .iter()
            .map(|(name, tools, versions)| MemberOverride {
                crate_name: name.clone(),
                tools: reported_entries(tools),
                versions: reported_entries(versions),
            })
            .collect(),
    }
    .report(message_format, None);
    0
}
