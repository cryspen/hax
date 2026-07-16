//! Handlers for the `cargo hax tools` subcommands.

use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;

use super::defaults::defaults;
use super::project::ProjectContext;
use super::resolve::{Resolution, Resolved, resolve_tool, resolve_version};
use super::{DECLARED_VERSION_KEYS, MANAGED_TOOLS};

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
            let name_width = all.iter().map(|(name, _)| name.len()).max().unwrap_or(0);
            let value_width = all
                .iter()
                .map(|(_, resolution)| resolution_value(resolution).len())
                .max()
                .unwrap_or(0);

            println!("tools:");
            print_entries(&tools, name_width, value_width);
            println!();
            println!("versions:");
            print_entries(&versions, name_width, value_width);
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
