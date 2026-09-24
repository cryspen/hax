use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;
use std::fs;
use std::path::Path;

use super::tools;

/// Whether generation treats `path` as absent and would write it. An empty
/// file counts as absent: it holds no content worth preserving (typically
/// the leftover of an interrupted write) and would otherwise never be
/// repaired, since existing files are not touched.
pub fn absent_or_empty(path: &Path) -> bool {
    !fs::metadata(path).is_ok_and(|metadata| !metadata.is_file() || metadata.len() > 0)
}

/// Write `contents` to `path` if [`absent_or_empty`] holds for it.
/// Reports the file as produced (wrote or unchanged) via `HaxMessage`.
/// Returns whether writing failed.
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
    match write_by_rename(path, contents) {
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

/// Replaces `path` in one step: a reader that already opened it, such as
/// `make` parsing a `Makefile.hax` whose recipe runs hax, keeps reading the
/// old contents rather than a mix of both.
fn write_by_rename(path: &Path, contents: &str) -> std::io::Result<()> {
    let mut tmp = path.as_os_str().to_owned();
    tmp.push(".hax-tmp");
    let tmp = std::path::PathBuf::from(tmp);
    fs::write(&tmp, contents)
        .and_then(|()| fs::rename(&tmp, path))
        .inspect_err(|_| {
            let _ = fs::remove_file(&tmp);
        })
}

/// Resolve the `project-files` key for the crate being processed: the
/// member-level value overrides the workspace-level one, consistent with
/// the tool version resolution order; the default is enabled.
pub fn enabled(project: &tools::project::ProjectContext, crate_dir: Option<&Path>) -> bool {
    let crate_dir = crate_dir.map_or_else(|| project.crate_dir(), Path::to_path_buf);
    project
        .member_config(&crate_dir)
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
    fn a_reader_of_the_old_file_keeps_seeing_the_old_contents() {
        use std::io::Read;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("Makefile.hax");
        fs::write(&path, "old").unwrap();
        let mut reader = fs::File::open(&path).unwrap();
        assert!(!write_always(&path, "new contents", MessageFormat::Human));
        let mut read = String::new();
        reader.read_to_string(&mut read).unwrap();
        assert_eq!(read, "old");
        assert_eq!(fs::read_to_string(&path).unwrap(), "new contents");
        assert_eq!(fs::read_dir(dir.path()).unwrap().count(), 1);
    }

    #[test]
    fn a_virtual_workspace_resolves_the_workspace_level_key() {
        assert!(!enabled(&virtual_workspace(Some(false)), None));
        assert!(enabled(&virtual_workspace(Some(true)), None));
        assert!(enabled(&virtual_workspace(None), None));
    }
}
