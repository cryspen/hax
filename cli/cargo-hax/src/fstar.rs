use hax_types::cli_options::MessageFormat;
use std::path::Path;

use super::project_files::{absent_or_empty, write_always};

pub const MAKEFILE: &str = "Makefile";
pub const MAKEFILE_HAX: &str = "Makefile.hax";

/// `Makefile.hax` verbatim, embedded at compile time. hax never parses it;
/// `make` reads it, once written, at build time.
const MAKEFILE_HAX_CONTENTS: &str = include_str!("fstar/Makefile.hax");

const DEFAULT_EXTRACT_COMMAND: &str = "cargo hax into fstar";

#[derive(Debug, PartialEq, Eq)]
enum Ownership {
    Absent,
    Ours,
    Theirs,
}

fn include_targets(line: &str) -> Option<&str> {
    let line = line.trim_start();
    if line.starts_with('#') {
        return None;
    }
    ["include ", "-include ", "sinclude "]
        .iter()
        .find_map(|directive| line.strip_prefix(directive))
}

fn classify(contents: &str) -> Ownership {
    if contents.trim().is_empty() {
        return Ownership::Absent;
    }
    for line in contents.lines() {
        if let Some(targets) = include_targets(line)
            && targets.split_whitespace().any(|name| name == MAKEFILE_HAX)
        {
            return Ownership::Ours;
        }
    }
    Ownership::Theirs
}

fn user_makefile_contents(extract_command: &str) -> String {
    format!(
        "\
ADMIT_MODULES ?=
FSTAR_INCLUDE_DIRS_EXTRA ?=
FSTAR_FLAGS_EXTRA ?=
HAX_EXTRACT_COMMAND ?= {extract_command}

include {MAKEFILE_HAX}
"
    )
}

pub fn generate(
    out_dir: &Path,
    extract_command: Option<&str>,
    message_format: MessageFormat,
) -> bool {
    let makefile = out_dir.join(MAKEFILE);
    let ownership = match std::fs::read_to_string(&makefile) {
        Ok(contents) => classify(&contents),
        Err(_) if absent_or_empty(&makefile) => Ownership::Absent,
        Err(_) => Ownership::Theirs,
    };
    if ownership == Ownership::Theirs {
        return false;
    }

    let mut error = write_always(
        &out_dir.join(MAKEFILE_HAX),
        MAKEFILE_HAX_CONTENTS,
        message_format,
    );
    if ownership == Ownership::Absent {
        let contents = user_makefile_contents(extract_command.unwrap_or(DEFAULT_EXTRACT_COMMAND));
        error |= write_always(&makefile, &contents, message_format);
    }
    error
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_empty_or_missing_makefile_is_ours_to_create() {
        assert_eq!(classify(""), Ownership::Absent);
        assert_eq!(classify("\n  \n"), Ownership::Absent);
    }

    #[test]
    fn every_include_spelling_of_our_file_is_recognized() {
        for line in [
            "include Makefile.hax",
            "-include Makefile.hax",
            "sinclude Makefile.hax",
            "   include Makefile.hax",
            "include Makefile.hax\n",
            "ADMIT_MODULES ?= A.fst\ninclude Makefile.hax\n",
            "include other.mk Makefile.hax",
        ] {
            assert_eq!(classify(line), Ownership::Ours, "for {line:?}");
        }
    }

    #[test]
    fn a_project_that_drives_fstar_itself_is_left_alone() {
        for contents in [
            "include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base",
            "FSTAR_INCLUDE_DIRS_EXTRA += ../models\ninclude ../../Makefile.base\n",
            "# include Makefile.hax\nall:\n\techo hand-written\n",
            "all:\n\techo hand-written\n",
            "include Makefile.hax.bak",
        ] {
            assert_eq!(classify(contents), Ownership::Theirs, "for {contents:?}");
        }
    }

    #[test]
    fn the_user_makefile_names_the_command_that_reproduces_the_extraction() {
        let contents = user_makefile_contents("cargo hax extract chacha20");
        assert!(contents.contains("HAX_EXTRACT_COMMAND ?= cargo hax extract chacha20"));
        assert_eq!(classify(&contents), Ownership::Ours);
    }

    #[test]
    fn the_embedded_makefile_is_the_one_on_disk() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/fstar/Makefile.hax");
        assert_eq!(
            std::fs::read_to_string(path).unwrap(),
            MAKEFILE_HAX_CONTENTS
        );
    }

    fn scaffold(existing: Option<&str>) -> (tempfile::TempDir, bool) {
        let dir = tempfile::tempdir().unwrap();
        if let Some(contents) = existing {
            std::fs::write(dir.path().join(MAKEFILE), contents).unwrap();
        }
        let error = generate(dir.path(), None, MessageFormat::Human);
        (dir, error)
    }

    fn read(dir: &Path, name: &str) -> Option<String> {
        std::fs::read_to_string(dir.join(name)).ok()
    }

    #[test]
    fn an_empty_directory_gets_both_files() {
        let (dir, error) = scaffold(None);
        assert!(!error);
        assert_eq!(
            read(dir.path(), MAKEFILE_HAX).as_deref(),
            Some(MAKEFILE_HAX_CONTENTS)
        );
        let makefile = read(dir.path(), MAKEFILE).unwrap();
        assert!(makefile.contains("include Makefile.hax"));
        assert!(makefile.contains(DEFAULT_EXTRACT_COMMAND));
    }

    #[test]
    fn an_edited_user_makefile_survives_while_ours_is_refreshed() {
        let edited = "ADMIT_MODULES ?= Slow.fst\ninclude Makefile.hax\n";
        let (dir, error) = scaffold(Some(edited));
        assert!(!error);
        std::fs::write(dir.path().join(MAKEFILE_HAX), "stale\n").unwrap();

        assert!(!generate(dir.path(), None, MessageFormat::Human));
        assert_eq!(read(dir.path(), MAKEFILE).as_deref(), Some(edited));
        assert_eq!(
            read(dir.path(), MAKEFILE_HAX).as_deref(),
            Some(MAKEFILE_HAX_CONTENTS)
        );
    }

    #[test]
    fn a_project_with_its_own_build_gets_nothing_at_all() {
        for existing in [
            "include ../../fstar-helpers/Makefile.base\n",
            "HACL_HOME ?= /opt/hacl\nall:\n\tfstar.exe *.fst\n",
        ] {
            let (dir, error) = scaffold(Some(existing));
            assert!(!error);
            assert_eq!(read(dir.path(), MAKEFILE).as_deref(), Some(existing));
            assert_eq!(read(dir.path(), MAKEFILE_HAX), None);
        }
    }

    #[test]
    fn the_extract_command_reaches_the_generated_makefile() {
        let dir = tempfile::tempdir().unwrap();
        assert!(!generate(
            dir.path(),
            Some("cargo hax extract barrett"),
            MessageFormat::Human
        ));
        assert!(
            read(dir.path(), MAKEFILE)
                .unwrap()
                .contains("HAX_EXTRACT_COMMAND ?= cargo hax extract barrett")
        );
    }
}
