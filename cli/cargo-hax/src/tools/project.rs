//! Project discovery: which `hax.toml` files apply to the current project.
//!
//! Discovery is bound to the Rust project, not the invocation directory:
//! hax asks Cargo for the workspace root and the member-crate roots and
//! reads `hax.toml` from exactly these directories. A `hax.toml` anywhere
//! else has no effect (and is warned about when it sits between the
//! invocation directory and the workspace root).

use std::path::{Path, PathBuf};

use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;

use super::config::{self, HaxToml};

/// One workspace member crate.
#[derive(Debug, Clone)]
pub struct MemberCrate {
    pub name: String,
    pub root: PathBuf,
    /// The member's own `hax.toml`, if it has one. `None` for the crate
    /// whose root is the workspace root itself: the workspace file covers it.
    pub config: Option<HaxToml>,
}

/// The `hax.toml` configuration of the current project.
#[derive(Debug, Clone)]
pub struct ProjectContext {
    pub workspace_root: PathBuf,
    pub workspace_config: Option<HaxToml>,
    pub members: Vec<MemberCrate>,
    /// The package `cargo metadata` reports as the root of the current
    /// invocation, if any (a virtual workspace has none).
    pub root_package: Option<RootPackage>,
}

/// The package the current invocation processes.
#[derive(Debug, Clone)]
pub struct RootPackage {
    pub name: String,
    pub dir: PathBuf,
}

impl ProjectContext {
    /// The `hax.toml` of the member crate rooted at `dir`, for per-crate
    /// resolution.
    pub fn member_config(&self, dir: &Path) -> Option<&HaxToml> {
        self.members
            .iter()
            .find(|member| member.root == dir)
            .and_then(|member| member.config.as_ref())
    }
}

impl ProjectContext {
    /// Discover the current project with `cargo metadata` and load its
    /// `hax.toml` files. Parse warnings are reported immediately; a
    /// malformed file or a failing `cargo metadata` is an error.
    pub fn load(message_format: MessageFormat) -> Result<Self, String> {
        let metadata = cargo_metadata::MetadataCommand::new()
            .exec()
            .map_err(|e| match e {
                cargo_metadata::Error::CargoMetadata { stderr } => format!(
                    "`cargo metadata` failed (this command must be run inside a \
                     Cargo project):\n{}",
                    stderr.trim()
                ),
                e => format!("`cargo metadata` failed: {e}"),
            })?;

        let workspace_root: PathBuf = metadata.workspace_root.clone().into();
        let workspace_config = load_hax_toml(&workspace_root, message_format)?;

        let mut members = Vec::new();
        for package in metadata
            .packages
            .iter()
            .filter(|p| metadata.workspace_members.contains(&p.id))
        {
            let root: PathBuf = package
                .manifest_path
                .parent()
                .expect("a Cargo.toml always has a parent directory")
                .into();
            let config = if root == workspace_root {
                None
            } else {
                load_hax_toml(&root, message_format)?
            };
            members.push(MemberCrate {
                name: package.name.clone(),
                root,
                config,
            });
        }

        let root_package = metadata.root_package().map(|package| RootPackage {
            name: package.name.clone(),
            dir: package
                .manifest_path
                .parent()
                .expect("a Cargo.toml always has a parent directory")
                .into(),
        });
        let ctx = ProjectContext {
            workspace_root,
            workspace_config,
            members,
            root_package,
        };
        ctx.warn_member_overrides(message_format);
        ctx.warn_stray_files(message_format);
        Ok(ctx)
    }

    /// Overriding members lose the workspace's single answer to "which tool
    /// versions does this project use": keep the divergence visible. Keyed
    /// on the entries' presence, not their effect.
    fn warn_member_overrides(&self, message_format: MessageFormat) {
        for member in &self.members {
            if let Some(config) = &member.config
                && config.has_entries()
            {
                HaxMessage::MemberToolOverrides {
                    crate_name: member.name.clone(),
                    path: config.path.clone(),
                    entries: config.entry_names(),
                }
                .report(message_format, None);
            }
        }
    }

    /// Warn about `hax.toml` files in directories between the invocation
    /// directory and the workspace root that are not member-crate roots:
    /// they have no effect, which is usually a misplaced file.
    fn warn_stray_files(&self, message_format: MessageFormat) {
        // `cargo metadata` reports canonical paths (symlinks resolved), so
        // canonicalize the invocation directory too; otherwise a symlinked
        // checkout (e.g. `/tmp` -> `/private/tmp` on macOS) makes the
        // `starts_with` and per-member comparisons below spuriously fail.
        let Ok(invocation_dir) = std::env::current_dir().and_then(|dir| std::fs::canonicalize(dir))
        else {
            return;
        };
        if !invocation_dir.starts_with(&self.workspace_root) {
            return;
        }
        for dir in invocation_dir.ancestors() {
            if dir == self.workspace_root {
                break;
            }
            let candidate = dir.join("hax.toml");
            if candidate.is_file() && !self.members.iter().any(|m| m.root == dir) {
                HaxMessage::StrayHaxToml { path: candidate }.report(message_format, None);
            }
        }
    }
}

/// Read and parse `<dir>/hax.toml`, treating absence as `None`. Parse
/// warnings are reported immediately; malformed contents are an error.
fn load_hax_toml(dir: &Path, message_format: MessageFormat) -> Result<Option<HaxToml>, String> {
    let path = dir.join("hax.toml");
    let contents = match std::fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("could not read {}: {e}", path.display())),
    };
    match config::parse(&path, &contents) {
        Ok((parsed, warnings)) => {
            for message in warnings {
                HaxMessage::HaxTomlWarning {
                    path: path.clone(),
                    message,
                }
                .report(message_format, None);
            }
            Ok(Some(parsed))
        }
        Err(message) => {
            HaxMessage::HaxTomlError {
                path: path.clone(),
                message,
            }
            .report(message_format, None);
            Err(format!("invalid {}", path.display()))
        }
    }
}
