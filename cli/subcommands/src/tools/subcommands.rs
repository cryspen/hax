//! Handlers for the `cargo hax tools` subcommands.

use std::collections::BTreeSet;

use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;

use super::defaults::defaults;
use super::install::{Installed, ensure_installed};
use super::project::ProjectContext;
use super::resolve::{Resolution, Resolved, resolve_tool, resolve_tool_committed, resolve_version};
use super::{DECLARED_VERSION_KEYS, MANAGED_TOOLS, cache, manifest};

fn error(message: String, message_format: MessageFormat) -> i32 {
    HaxMessage::GenericError { message }.report(message_format, None);
    1
}

/// `cargo hax tools install`: populate the machine-wide cache.
///
/// With a `<tool>@<version>` argument, installs exactly that; without one,
/// resolves the current project's committed configuration (ignoring
/// `HAX_<TOOL>_BINARY` overrides) and installs the union across all
/// workspace crates: pins, member overrides, and defaults.
pub fn install(spec: Option<&str>, force: bool, message_format: MessageFormat) -> i32 {
    let requests: Vec<(String, String)> = match spec {
        Some(spec) => {
            let Some((tool, version)) = spec.split_once('@') else {
                return error(
                    format!("`{spec}` is not a `<tool>@<version>` specification"),
                    message_format,
                );
            };
            if !MANAGED_TOOLS.contains(&tool) {
                return error(
                    format!(
                        "`{tool}` is not a managed tool (managed tools: {})",
                        MANAGED_TOOLS.join(", ")
                    ),
                    message_format,
                );
            }
            if version.is_empty() {
                return error(format!("`{spec}` lacks a version"), message_format);
            }
            vec![(tool.to_string(), version.to_string())]
        }
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
                let mut resolutions = vec![resolve_tool_committed(tool, None, workspace, defaults)];
                for member in &ctx.members {
                    if member.config.is_some() {
                        resolutions.push(resolve_tool_committed(
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
    let mut statuses = Vec::new();
    for (tool, version) in &requests {
        match ensure_installed(tool, version, force, message_format) {
            Ok(outcome) => {
                statuses.push((tool.clone(), version.clone(), outcome));
            }
            Err(message) => {
                failed = true;
                HaxMessage::GenericError {
                    message: format!("could not install {tool} {version}: {message}"),
                }
                .report(message_format, None);
            }
        }
    }
    match message_format {
        MessageFormat::Human => {
            for (tool, version, outcome) in &statuses {
                let (verb, suffix) = match outcome {
                    Installed::AlreadyCached { verified: true } => ("Cached", ""),
                    Installed::AlreadyCached { verified: false } => ("Cached", " (unverified)"),
                    Installed::Fresh { verified: true } => ("Installed", ""),
                    Installed::Fresh { verified: false } => ("Installed", " (unverified)"),
                };
                HaxMessage::Step {
                    verb: verb.to_string(),
                    target: format!("{tool} {version}{suffix}"),
                }
                .report(message_format, None);
            }
        }
        MessageFormat::Json => {
            let json = serde_json::json!({
                "installed": statuses
                    .iter()
                    .map(|(tool, version, outcome)| {
                        let status = match outcome {
                            Installed::AlreadyCached { verified: true } => "already cached",
                            Installed::AlreadyCached { verified: false } => {
                                "already cached (NOT verified)"
                            }
                            Installed::Fresh { verified: true } => "installed (checksum verified)",
                            Installed::Fresh { verified: false } => "installed (NOT verified)",
                        };
                        serde_json::json!({
                            "tool": tool,
                            "version": version,
                            "status": status,
                        })
                    })
                    .collect::<Vec<_>>(),
            });
            println!("{json}");
        }
    }
    if failed { 1 } else { 0 }
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
        let mut entries = Vec::new();
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
            let in_manifest = manifest.knows_version(tool, version);
            // Whether the cached copy was checksum-verified at install time,
            // read from its metadata; a fallback install records `false`.
            let verified = is_installed
                && cache::version_dir(tool, version)
                    .ok()
                    .and_then(|dir| cache::read_metadata(&dir).ok().flatten())
                    .and_then(|metadata| metadata.checksum_verified)
                    .unwrap_or(false);
            entries.push((
                version.clone(),
                is_installed,
                in_manifest,
                is_default,
                verified,
            ));
        }
        report.push((tool.to_string(), entries, omitted));
    }

    match message_format {
        MessageFormat::Human => {
            for (index, (tool, entries, omitted)) in report.iter().enumerate() {
                if index > 0 {
                    println!();
                }
                println!("{tool}:");
                if entries.is_empty() {
                    let none = if installed_only {
                        "none installed"
                    } else {
                        "none"
                    };
                    println!("  ({none})");
                }
                // Pad the version column so the markers line up.
                let width = entries
                    .iter()
                    .map(|(version, ..)| version.len())
                    .max()
                    .unwrap_or(0);
                for (version, is_installed, in_manifest, is_default, verified) in entries {
                    let mut marks = Vec::new();
                    if *is_default {
                        marks.push("default");
                    }
                    if *is_installed {
                        marks.push("installed");
                        if !*verified {
                            marks.push("unverified");
                        }
                    }
                    if !*in_manifest {
                        marks.push("not in manifest");
                    }
                    if marks.is_empty() {
                        println!("  {version}");
                    } else {
                        println!("  {version:width$}  ({})", marks.join(", "));
                    }
                }
                if *omitted > 0 {
                    println!("  ... {omitted} older versions omitted (use --all)");
                }
            }
        }
        MessageFormat::Json => {
            let json = serde_json::json!({
                "tools": report
                    .iter()
                    .map(|(tool, entries, omitted)| {
                        serde_json::json!({
                            "tool": tool,
                            "omitted": omitted,
                            "versions": entries
                                .iter()
                                .map(|(version, is_installed, in_manifest, is_default, verified)| {
                                    serde_json::json!({
                                        "version": version,
                                        "installed": is_installed,
                                        "in_manifest": in_manifest,
                                        "default": is_default,
                                        "verified": verified,
                                    })
                                })
                                .collect::<Vec<_>>(),
                        })
                    })
                    .collect::<Vec<_>>(),
            });
            println!("{json}");
        }
    }
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

    // The hax-lib compatibility of every crate with a direct dependency,
    // reported once in the common uniform case.
    let hax_lib = super::haxlib::check(&ctx);
    let status = |result: &super::haxlib::CrateCompatibility| {
        use super::haxlib::Compatibility::*;
        match result.compatibility {
            Compatible => "compatible",
            TooOld => "INCOMPATIBLE: too old for this cargo-hax",
            TooNew => "INCOMPATIBLE: newer than this cargo-hax",
        }
    };
    let uniform = hax_lib.len() > 1
        && hax_lib
            .iter()
            .all(|r| (&r.found, r.compatibility) == (&hax_lib[0].found, hax_lib[0].compatibility));

    match message_format {
        MessageFormat::Human => {
            // Align the name and value columns across every section so the
            // source annotations line up in a single grid.
            let all: Vec<&(String, Resolution)> = tools
                .iter()
                .chain(&versions)
                .chain(
                    member_reports
                        .iter()
                        .flat_map(|(_, member_tools, member_versions)| {
                            member_tools.iter().chain(member_versions.iter())
                        }),
                )
                .collect();
            // The `hax-lib` rows share the grid too, under the `libraries`
            // header, so `hax-lib` reads as a named row rather than a bare
            // version line.
            let name_width = all
                .iter()
                .map(|(name, _)| name.len())
                .chain(hax_lib.iter().map(|_| "hax-lib".len()))
                .max()
                .unwrap_or(0);
            let value_width = all
                .iter()
                .map(|(_, resolution)| resolution_value(resolution).len())
                .chain(hax_lib.iter().map(|result| result.found.len()))
                .max()
                .unwrap_or(0);

            println!("tools:");
            print_entries(&tools, name_width, value_width);
            println!();
            println!("versions:");
            print_entries(&versions, name_width, value_width);
            match &hax_lib[..] {
                [] => {}
                // One version across the project (or a single crate): one row.
                results if uniform || results.len() == 1 => {
                    let result = &results[0];
                    println!();
                    println!("libraries:");
                    println!(
                        "  {name:name_width$}  {value:value_width$}  ({status})",
                        name = "hax-lib",
                        value = result.found,
                        status = status(result),
                    );
                }
                // Crates disagree on the version: one row each, named crate.
                results => {
                    println!();
                    println!("libraries:");
                    for result in results {
                        println!(
                            "  {name:name_width$}  {value:value_width$}  (crate `{crate_name}`: {status})",
                            name = "hax-lib",
                            value = result.found,
                            crate_name = result.crate_name,
                            status = status(result),
                        );
                    }
                }
            }
            for (name, member_tools, member_versions) in &member_reports {
                println!();
                println!("crate `{name}` (overrides):");
                print_entries(member_tools, name_width, value_width);
                print_entries(member_versions, name_width, value_width);
            }
        }
        MessageFormat::Json => {
            let json = serde_json::json!({
                "tools": entries_json(&tools),
                "versions": entries_json(&versions),
                "hax_lib": hax_lib
                    .iter()
                    .map(|result| {
                        serde_json::json!({
                            "crate": result.crate_name,
                            "version": result.found,
                            "compatible": result.compatibility
                                == super::haxlib::Compatibility::Compatible,
                        })
                    })
                    .collect::<Vec<_>>(),
                "member_overrides": member_reports
                    .iter()
                    .map(|(name, tools, versions)| {
                        serde_json::json!({
                            "crate": name,
                            "tools": entries_json(tools),
                            "versions": entries_json(versions),
                        })
                    })
                    .collect::<Vec<_>>(),
            });
            println!("{json}");
        }
    }
    0
}

/// The value shown for a resolution: a version string or a path.
fn resolution_value(resolution: &Resolution) -> String {
    match &resolution.kind {
        Resolved::Version(version) => version.clone(),
        Resolved::Path(path) => path.display().to_string(),
    }
}

fn print_entries(entries: &[(String, Resolution)], name_width: usize, value_width: usize) {
    for (name, resolution) in entries {
        println!(
            "  {name:name_width$}  {value:value_width$}  ({source})",
            value = resolution_value(resolution),
            source = resolution.source.describe(),
        );
    }
}

fn entries_json(entries: &[(String, Resolution)]) -> serde_json::Value {
    entries
        .iter()
        .map(|(name, resolution)| {
            let (kind, value) = match &resolution.kind {
                Resolved::Version(version) => ("version", version.clone()),
                Resolved::Path(path) => ("path", path.display().to_string()),
            };
            serde_json::json!({
                "name": name,
                kind: value,
                "source": resolution.source.describe(),
            })
        })
        .collect()
}
