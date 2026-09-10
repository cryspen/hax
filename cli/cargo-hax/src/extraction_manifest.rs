use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;
use std::collections::BTreeSet;
use std::path::{Component, Path, PathBuf};

pub const MANIFEST: &str = ".hax-extraction";

fn is_inside(path: &Path) -> bool {
    path.components()
        .all(|component| matches!(component, Component::Normal(_)))
}

pub fn read(out_dir: &Path) -> BTreeSet<PathBuf> {
    let Ok(contents) = std::fs::read_to_string(out_dir.join(MANIFEST)) else {
        return BTreeSet::new();
    };
    contents
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(PathBuf::from)
        .filter(|path| is_inside(path))
        .collect()
}

pub fn write(out_dir: &Path, produced: &BTreeSet<PathBuf>, message_format: MessageFormat) -> bool {
    let contents: String = produced
        .iter()
        .map(|path| format!("{}\n", path.display()))
        .collect();
    if let Err(e) = std::fs::write(out_dir.join(MANIFEST), contents) {
        HaxMessage::GenericError {
            message: format!(
                "failed to write {}: {}",
                out_dir.join(MANIFEST).display(),
                e
            ),
        }
        .report(message_format, None);
        return true;
    }
    false
}

pub fn remove_stale(
    out_dir: &Path,
    produced: &BTreeSet<PathBuf>,
    message_format: MessageFormat,
) -> bool {
    let mut error = false;
    let mut directories = BTreeSet::new();
    for stale in read(out_dir).difference(produced) {
        let path = out_dir.join(stale);
        if !path.is_file() {
            continue;
        }
        match std::fs::remove_file(&path) {
            Ok(()) => {
                if let Some(parent) = stale.parent()
                    && parent != Path::new("")
                {
                    directories.insert(parent.to_path_buf());
                }
                HaxMessage::Step {
                    verb: "Removed".to_string(),
                    target: path.display().to_string(),
                }
                .report(message_format, None);
            }
            Err(e) => {
                HaxMessage::GenericError {
                    message: format!("failed to remove {}: {}", path.display(), e),
                }
                .report(message_format, None);
                error = true;
            }
        }
    }
    for directory in directories.iter().rev() {
        let _ = std::fs::remove_dir(out_dir.join(directory));
    }
    error
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(paths: &[&str]) -> BTreeSet<PathBuf> {
        paths.iter().map(PathBuf::from).collect()
    }

    fn touch(dir: &Path, name: &str) {
        let path = dir.join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, "").unwrap();
    }

    #[test]
    fn a_module_the_extraction_stopped_producing_is_removed() {
        let dir = tempfile::tempdir().unwrap();
        touch(dir.path(), "Kept.fst");
        touch(dir.path(), "Gone.fst");
        assert!(!write(
            dir.path(),
            &set(&["Kept.fst", "Gone.fst"]),
            MessageFormat::Human
        ));

        assert!(!remove_stale(
            dir.path(),
            &set(&["Kept.fst"]),
            MessageFormat::Human
        ));
        assert!(dir.path().join("Kept.fst").exists());
        assert!(!dir.path().join("Gone.fst").exists());
    }

    #[test]
    fn files_hax_never_wrote_are_left_alone() {
        let dir = tempfile::tempdir().unwrap();
        touch(dir.path(), "Handwritten.fst");
        touch(dir.path(), "Makefile");
        assert!(!write(
            dir.path(),
            &set(&["Extracted.fst"]),
            MessageFormat::Human
        ));

        assert!(!remove_stale(dir.path(), &set(&[]), MessageFormat::Human));
        assert!(dir.path().join("Handwritten.fst").exists());
        assert!(dir.path().join("Makefile").exists());
    }

    #[test]
    fn a_first_run_has_nothing_to_remove() {
        let dir = tempfile::tempdir().unwrap();
        touch(dir.path(), "Handwritten.fst");
        assert!(read(dir.path()).is_empty());
        assert!(!remove_stale(dir.path(), &set(&[]), MessageFormat::Human));
        assert!(dir.path().join("Handwritten.fst").exists());
    }

    #[test]
    fn a_manifest_cannot_reach_outside_the_extraction_directory() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join(MANIFEST),
            "../Escape.fst\n/etc/passwd\nInside.fst\n",
        )
        .unwrap();
        assert_eq!(read(dir.path()), set(&["Inside.fst"]));
    }

    #[test]
    fn an_emptied_subdirectory_is_removed_with_its_last_file() {
        let dir = tempfile::tempdir().unwrap();
        touch(dir.path(), "sub/Gone.fst");
        assert!(!write(
            dir.path(),
            &set(&["sub/Gone.fst"]),
            MessageFormat::Human
        ));

        assert!(!remove_stale(dir.path(), &set(&[]), MessageFormat::Human));
        assert!(!dir.path().join("sub").exists());
    }
}
