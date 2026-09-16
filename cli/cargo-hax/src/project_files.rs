use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;
use std::fs;
use std::path::Path;

use super::tools;

pub fn absent_or_empty(path: &Path) -> bool {
    !fs::metadata(path).is_ok_and(|metadata| !metadata.is_file() || metadata.len() > 0)
}

pub fn write_if_absent(path: &Path, contents: &str, message_format: MessageFormat) -> bool {
    if !absent_or_empty(path) {
        HaxMessage::ProducedFile {
            path: path.to_path_buf(),
            wrote: false,
        }
        .report(message_format, None);
        false
    } else {
        write_always(path, contents, message_format)
    }
}

pub fn write_always(path: &Path, contents: &str, message_format: MessageFormat) -> bool {
    let unchanged = fs::read_to_string(path).is_ok_and(|existing| existing == contents);
    if unchanged {
        HaxMessage::ProducedFile {
            path: path.to_path_buf(),
            wrote: false,
        }
        .report(message_format, None);
        return false;
    }
    match fs::write(path, contents) {
        Ok(()) => {
            HaxMessage::ProducedFile {
                path: path.to_path_buf(),
                wrote: true,
            }
            .report(message_format, None);
            false
        }
        Err(e) => {
            HaxMessage::GenericError {
                message: format!("failed to write {}: {}", path.display(), e),
            }
            .report(message_format, None);
            true
        }
    }
}

/// Resolve the `project-files` key for the crate being processed: the
/// member-level value overrides the workspace-level one, consistent with
/// the tool version resolution order; the default is enabled.
pub fn enabled(project: &tools::project::ProjectContext) -> bool {
    project
        .member_config(&project.crate_dir())
        .and_then(|config| config.project_files)
        .or_else(|| {
            project
                .workspace_config
                .as_ref()
                .and_then(|config| config.project_files)
        })
        .unwrap_or(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tools::config::HaxToml;
    use crate::tools::project::ProjectContext;
    use std::path::PathBuf;

    /// A virtual workspace: no root package, so the crate directory is the
    /// working directory, which no member here configures.
    fn virtual_workspace(project_files: Option<bool>) -> ProjectContext {
        ProjectContext {
            workspace_root: PathBuf::from("/ws"),
            workspace_config: Some(HaxToml {
                project_files,
                ..Default::default()
            }),
            members: Vec::new(),
            root_package: None,
            selects_packages: false,
            package_specs: Vec::new(),
        }
    }

    #[test]
    fn a_virtual_workspace_resolves_the_workspace_level_key() {
        assert!(!enabled(&virtual_workspace(Some(false))));
        assert!(enabled(&virtual_workspace(Some(true))));
        assert!(enabled(&virtual_workspace(None)));
    }
}
