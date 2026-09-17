use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// The extensions an extraction writes. The extraction directory is
/// hax-owned, but it also holds the build files, so only what an extraction
/// could have produced is a candidate for removal.
const EXTRACTED: &[&str] = &["fst", "fsti", "map"];

fn is_extracted(path: &Path) -> bool {
    path.extension()
        .and_then(|e| e.to_str())
        .is_some_and(|e| EXTRACTED.contains(&e))
}

/// Remove the files under `out_dir` that this extraction did not produce.
/// Hand-written F* belongs in `models/` beside the extraction, so anything
/// left here that hax no longer writes is stale.
pub fn remove(out_dir: &Path, produced: &BTreeSet<PathBuf>, message_format: MessageFormat) -> bool {
    let mut error = false;
    let mut directories = BTreeSet::new();
    let mut walk = vec![PathBuf::new()];
    while let Some(relative) = walk.pop() {
        let entries = match std::fs::read_dir(out_dir.join(&relative)) {
            Ok(entries) => entries,
            Err(e) => {
                HaxMessage::GenericError {
                    message: format!("failed to read {}: {e}", out_dir.join(&relative).display()),
                }
                .report(message_format, None);
                return true;
            }
        };
        for entry in entries.flatten() {
            let relative = relative.join(entry.file_name());
            let path = out_dir.join(&relative);
            if path.is_dir() {
                directories.insert(relative.clone());
                walk.push(relative);
                continue;
            }
            if !is_extracted(&relative) || produced.contains(&relative) {
                continue;
            }
            match std::fs::remove_file(&path) {
                Ok(()) => HaxMessage::Step {
                    verb: "Removed".to_string(),
                    target: path.display().to_string(),
                }
                .report(message_format, None),
                Err(e) => {
                    HaxMessage::GenericError {
                        message: format!("failed to remove {}: {e}", path.display()),
                    }
                    .report(message_format, None);
                    error = true;
                }
            }
        }
    }
    // Deepest first, and only when empty: a directory that held nothing but
    // extracted files goes with them.
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
        touch(dir.path(), "Kept.fst.map");
        touch(dir.path(), "Gone.fst");
        touch(dir.path(), "Gone.fsti");

        assert!(!remove(
            dir.path(),
            &set(&["Kept.fst", "Kept.fst.map"]),
            MessageFormat::Human
        ));
        assert!(dir.path().join("Kept.fst").exists());
        assert!(dir.path().join("Kept.fst.map").exists());
        assert!(!dir.path().join("Gone.fst").exists());
        assert!(!dir.path().join("Gone.fsti").exists());
    }

    #[test]
    fn the_build_files_are_not_extraction_output() {
        let dir = tempfile::tempdir().unwrap();
        for name in [
            "Makefile",
            "Makefile.hax",
            ".depend",
            ".hax-roots",
            "hax.fst.config.json",
        ] {
            touch(dir.path(), name);
        }

        assert!(!remove(dir.path(), &set(&[]), MessageFormat::Human));
        for name in [
            "Makefile",
            "Makefile.hax",
            ".depend",
            ".hax-roots",
            "hax.fst.config.json",
        ] {
            assert!(dir.path().join(name).exists(), "{name} was removed");
        }
    }

    #[test]
    fn a_first_run_into_a_populated_directory_clears_it() {
        let dir = tempfile::tempdir().unwrap();
        touch(dir.path(), "Old.fst");
        assert!(!remove(
            dir.path(),
            &set(&["New.fst"]),
            MessageFormat::Human
        ));
        assert!(!dir.path().join("Old.fst").exists());
    }

    #[test]
    fn a_subdirectory_is_cleared_and_removed_with_its_last_file() {
        let dir = tempfile::tempdir().unwrap();
        touch(dir.path(), "sub/Gone.fst");
        touch(dir.path(), "kept/Kept.fst");

        assert!(!remove(
            dir.path(),
            &set(&["kept/Kept.fst"]),
            MessageFormat::Human
        ));
        assert!(!dir.path().join("sub").exists());
        assert!(dir.path().join("kept/Kept.fst").exists());
    }

    #[test]
    fn a_directory_holding_anything_else_stays() {
        let dir = tempfile::tempdir().unwrap();
        touch(dir.path(), "sub/Gone.fst");
        touch(dir.path(), "sub/notes.md");

        assert!(!remove(dir.path(), &set(&[]), MessageFormat::Human));
        assert!(!dir.path().join("sub/Gone.fst").exists());
        assert!(dir.path().join("sub/notes.md").exists());
    }
}
