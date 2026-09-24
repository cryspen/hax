use hax_types::cli_options::MessageFormat;
use std::path::{Path, PathBuf};

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

/// The files a `make` include directive names, whatever whitespace
/// separates it from them.
fn include_targets(line: &str) -> Option<&str> {
    let line = line.trim_start();
    if line.starts_with('#') {
        return None;
    }
    let (directive, targets) = line.split_once(char::is_whitespace)?;
    matches!(directive, "include" | "-include" | "sinclude").then_some(targets)
}

fn classify(contents: &str) -> Ownership {
    if contents.trim().is_empty() {
        return Ownership::Absent;
    }
    for line in contents.lines() {
        if let Some(targets) = include_targets(line)
            && targets
                .split_whitespace()
                .any(|name| name.trim_start_matches("./") == MAKEFILE_HAX)
        {
            return Ownership::Ours;
        }
    }
    Ownership::Theirs
}

/// The `cargo hax` command `args` spells, `args` being the arguments of
/// the current invocation minus the program name. A scenario run re-enters
/// through `__json` and passes its own command instead, so that spelling
/// is not one this can reproduce.
fn command_of_args(args: &[String]) -> String {
    match args {
        [] => DEFAULT_EXTRACT_COMMAND.to_string(),
        [keyword] if keyword == "__json" => DEFAULT_EXTRACT_COMMAND.to_string(),
        // A make assignment cannot span lines.
        args if args.iter().any(|arg| arg.contains('\n')) => DEFAULT_EXTRACT_COMMAND.to_string(),
        args => match shlex::try_join(args.iter().map(String::as_str)) {
            Ok(joined) => format!("cargo hax {joined}"),
            Err(_) => DEFAULT_EXTRACT_COMMAND.to_string(),
        },
    }
}

/// The command that reproduces this extraction, quoted back from the
/// invocation hax was given.
pub fn invocation_command() -> String {
    command_of_args(&crate::get_args("hax")[1..])
}

/// `to` expressed relative to `from`, both absolute. `None` when they share
/// no component at all (two Windows drives, say), as no relative path then
/// leads from one to the other.
fn relative_to(from: &Path, to: &Path) -> Option<PathBuf> {
    let common = from
        .components()
        .zip(to.components())
        .take_while(|(a, b)| a == b)
        .count();
    if common == 0 {
        return None;
    }
    let up = from.components().skip(common).map(|_| "..");
    let down = to.components().skip(common).map(|c| c.as_os_str());
    let path: PathBuf = up.map(std::ffi::OsStr::new).chain(down).collect();
    Some(if path.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        path
    })
}

/// The directory `make` must run the recorded command from: the one hax was
/// invoked in, so that relative paths in it resolve as they did.
fn extract_dir(out_dir: &Path) -> PathBuf {
    let absolute = |p: &Path| {
        std::path::absolute(p)
            .unwrap_or_else(|_| p.to_path_buf())
            .components()
            .collect::<PathBuf>()
    };
    std::env::current_dir()
        .ok()
        .and_then(|cwd| relative_to(&absolute(out_dir), &absolute(&cwd)))
        .unwrap_or_else(|| PathBuf::from("."))
}

/// `value` as the right-hand side of a make assignment, which would expand
/// `$` and cut at `#`. A backslash is literal unless it precedes `#`.
fn make_escape(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    let mut backslashes = 0;
    for c in value.chars() {
        match c {
            '\\' => backslashes += 1,
            '#' => {
                escaped.extend(std::iter::repeat_n('\\', 2 * backslashes + 1));
                escaped.push('#');
                backslashes = 0;
            }
            c => {
                escaped.extend(std::iter::repeat_n('\\', backslashes));
                backslashes = 0;
                if c == '$' {
                    escaped.push('$');
                }
                escaped.push(c);
            }
        }
    }
    escaped.extend(std::iter::repeat_n('\\', backslashes));
    escaped
}

fn user_makefile_contents(extract_command: &str, extract_dir: &Path) -> String {
    let extract_command = make_escape(extract_command);
    let extract_dir = extract_dir.to_string_lossy();
    let extract_dir = make_escape(&shlex::try_quote(&extract_dir).unwrap_or("'.'".into()));
    format!(
        "\
ADMIT_MODULES ?=
FSTAR_INCLUDE_DIRS_EXTRA ?=
FSTAR_FLAGS_EXTRA ?=
HAX_EXTRACT_COMMAND ?= {extract_command}
HAX_EXTRACT_DIR ?= {extract_dir}

include {MAKEFILE_HAX}
"
    )
}

pub fn generate(out_dir: &Path, extract_command: &str, message_format: MessageFormat) -> bool {
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
        let contents = user_makefile_contents(extract_command, &extract_dir(out_dir));
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
            "include\tMakefile.hax",
            "include ./Makefile.hax",
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
            "includeMakefile.hax",
        ] {
            assert_eq!(classify(contents), Ownership::Theirs, "for {contents:?}");
        }
    }

    #[test]
    fn the_user_makefile_names_the_command_that_reproduces_the_extraction() {
        let contents = user_makefile_contents("cargo hax extract chacha20", Path::new("../../.."));
        assert!(contents.contains("HAX_EXTRACT_COMMAND ?= cargo hax extract chacha20"));
        // `make` runs from the extraction directory, so a relative path in
        // the command needs the directory it was given in.
        assert!(contents.contains("HAX_EXTRACT_DIR ?= ../../.."));
        assert_eq!(classify(&contents), Ownership::Ours);
    }

    #[test]
    fn the_extraction_directory_is_named_relative_to_the_output() {
        let rel = |from: &str, to: &str| {
            relative_to(Path::new(from), Path::new(to)).map(|p| p.display().to_string())
        };
        assert_eq!(
            rel("/ws/proofs/fstar/extraction", "/ws").as_deref(),
            Some("../../..")
        );
        assert_eq!(rel("/ws", "/ws").as_deref(), Some("."));
        assert_eq!(rel("/ws/a", "/ws/b").as_deref(), Some("../b"));
        // The root alone is enough in common.
        assert_eq!(rel("/a", "/b").as_deref(), Some("../b"));
    }

    /// What `make` reads back from the generated assignments.
    fn assigned_by_make(extract_command: &str, extract_dir: &str) -> Option<(String, String)> {
        let dir = tempfile::tempdir().unwrap();
        let contents = user_makefile_contents(extract_command, Path::new(extract_dir));
        std::fs::write(dir.path().join(MAKEFILE), contents).unwrap();
        std::fs::write(
            dir.path().join(MAKEFILE_HAX),
            "$(info $(HAX_EXTRACT_COMMAND))\n$(info $(HAX_EXTRACT_DIR))\nall: ; @:\n",
        )
        .unwrap();
        let out = std::process::Command::new("make")
            .current_dir(dir.path())
            .output()
            .ok()?;
        assert!(out.status.success(), "{out:?}");
        let stdout = String::from_utf8(out.stdout).unwrap();
        let (command, dir) = stdout.trim_end().split_once('\n').unwrap();
        Some((command.to_string(), dir.to_string()))
    }

    #[test]
    fn make_reads_back_the_command_and_directory_verbatim() {
        let command = r"cargo hax -C --features 'a#b' ';' into -i '+x::$y \# z\' fstar";
        let Some((read_command, read_dir)) = assigned_by_make(command, "../my proj#1") else {
            return;
        };
        assert_eq!(read_command, command);
        assert_eq!(read_dir, "'../my proj#1'");
    }

    #[test]
    fn a_multi_line_argument_falls_back_to_the_default_command() {
        assert_eq!(
            command_of_args(&["into".into(), "-i".into(), "a\nb".into(), "fstar".into()]),
            DEFAULT_EXTRACT_COMMAND
        );
    }

    #[test]
    fn the_embedded_makefile_is_the_one_on_disk() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/fstar/Makefile.hax");
        assert_eq!(
            std::fs::read_to_string(path).unwrap(),
            MAKEFILE_HAX_CONTENTS
        );
    }

    #[test]
    fn the_invocation_is_quoted_back_as_the_command_that_reproduces_it() {
        let args = |args: &[&str]| {
            command_of_args(&args.iter().map(ToString::to_string).collect::<Vec<_>>())
        };
        assert_eq!(args(&["into", "fstar"]), "cargo hax into fstar");
        assert_eq!(
            args(&[
                "-C",
                "-p",
                "mycrate",
                ";",
                "into",
                "fstar",
                "--interfaces",
                "+**"
            ]),
            "cargo hax -C -p mycrate ';' into fstar --interfaces '+**'"
        );
        // A `__json` re-entry says nothing about how it was reached.
        assert_eq!(args(&["__json"]), DEFAULT_EXTRACT_COMMAND);
        assert_eq!(args(&[]), DEFAULT_EXTRACT_COMMAND);
    }

    fn scaffold(existing: Option<&str>) -> (tempfile::TempDir, bool) {
        let dir = tempfile::tempdir().unwrap();
        if let Some(contents) = existing {
            std::fs::write(dir.path().join(MAKEFILE), contents).unwrap();
        }
        let error = generate(dir.path(), DEFAULT_EXTRACT_COMMAND, MessageFormat::Human);
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

        assert!(!generate(
            dir.path(),
            DEFAULT_EXTRACT_COMMAND,
            MessageFormat::Human
        ));
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
            "cargo hax extract barrett",
            MessageFormat::Human
        ));
        assert!(
            read(dir.path(), MAKEFILE)
                .unwrap()
                .contains("HAX_EXTRACT_COMMAND ?= cargo hax extract barrett")
        );
    }
}
