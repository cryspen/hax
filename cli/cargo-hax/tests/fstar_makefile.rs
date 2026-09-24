mod common;

use std::path::{Path, PathBuf};
use std::process::Command;

use common::write_executable;

fn makefile_hax() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/fstar/Makefile.hax")
}

/// Moves a file's modification time well into the past.
fn backdate(path: &Path) {
    let file = std::fs::File::options().write(true).open(path).unwrap();
    file.set_modified(std::time::SystemTime::now() - std::time::Duration::from_secs(10))
        .unwrap();
}

fn have(program: &str) -> bool {
    Command::new(program)
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
}

/// A throwaway extraction directory: the shipped `Makefile.hax`, a
/// `Makefile` including it, one F* module, and stub binaries on `PATH`.
struct Project {
    dir: tempfile::TempDir,
    bin: PathBuf,
}

impl Project {
    fn new(fstar_stub: &str) -> Self {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        std::fs::copy(makefile_hax(), root.join("Makefile.hax")).unwrap();
        std::fs::write(root.join("Makefile"), "include Makefile.hax\n").unwrap();
        std::fs::write(root.join("A.fst"), "module A\nlet a : int = 1\n").unwrap();

        let bin = root.join("stub-bin");
        for tool in ["cargo", "cargo-hax", "jq"] {
            write_executable(&bin.join(tool), "#!/bin/sh\nexit 0\n");
        }
        write_executable(&bin.join("fstar.exe"), fstar_stub);
        std::fs::create_dir_all(root.join("proof-libs/fstar/core")).unwrap();
        Project { dir, bin }
    }

    fn root(&self) -> &Path {
        self.dir.path()
    }

    fn make(&self, target: &str) -> (String, bool) {
        self.run(&[target], &[])
    }

    /// The log `FSTAR_STUB_RECORDING` appends one line per invocation to.
    fn fstar_log(&self) -> String {
        std::fs::read_to_string(self.root().join("fstar.log")).unwrap_or_default()
    }

    /// How many times F* checked `module`, as opposed to computing
    /// dependencies.
    fn checks_of(&self, module: &str) -> usize {
        self.fstar_log()
            .lines()
            .filter(|line| !line.contains("--dep") && line.ends_with(&format!(" {module}")))
            .count()
    }

    fn dep_runs(&self) -> usize {
        self.fstar_log()
            .lines()
            .filter(|line| line.contains("--dep"))
            .count()
    }

    fn run(&self, args: &[&str], env: &[(&str, &str)]) -> (String, bool) {
        let path = format!(
            "{}:{}",
            self.bin.display(),
            std::env::var("PATH").unwrap_or_default()
        );
        let out = Command::new("make")
            .args(args)
            .current_dir(self.root())
            .env("PATH", path)
            .env("FSTAR_BIN", self.bin.join("fstar.exe"))
            .env("FSTAR_LOG", self.root().join("fstar.log"))
            .env("FINDLIBS_OUTPUT", self.root().join("proof-libs/fstar/core"))
            .env("HAX_AUTO_EXTRACT", "no")
            .env("NO_COLOR", "1")
            .envs(env.iter().copied())
            .output()
            .unwrap();
        let combined = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        (combined, out.status.success())
    }
}

/// Test fixture: stands in for `fstar.exe` reporting a module cycle.
/// `--dep full` writes the explanation to stdout and fails, which is what
/// the Makefile must keep out of `.depend`.
const FSTAR_STUB_CYCLIC: &str = "#!/bin/sh\n\
     echo 'The cycle contains a subset of the modules in:'\n\
     echo '  B.fst'\n\
     echo 'Recursive dependency on module A.fst.' 1>&2\n\
     exit 1\n";

/// Test fixture: stands in for `fstar.exe` succeeding with an empty
/// dependency graph.
const FSTAR_STUB_WORKING: &str = "#!/bin/sh\necho '# no dependencies'\nexit 0\n";

/// Test fixture: stands in for a working `fstar.exe`, logging every
/// invocation to `$FSTAR_LOG`. Like the real one, it exits 0 given no module
/// to check, and leaves an existing `.checked` file untouched.
const FSTAR_STUB_RECORDING: &str = r#"#!/bin/sh
echo "$@" >> "$FSTAR_LOG"
files=""; dep=0; lax=0; cache=""; next=0
for a in "$@"; do
  if [ "$next" = 1 ]; then cache="$a"; next=0; continue; fi
  case "$a" in
    --cache_dir) next=1 ;;
    --dep) dep=1 ;;
    --lax) lax=1 ;;
    *.fst|*.fsti) files="$files $a" ;;
  esac
done
sfx=.checked
[ "$lax" = 1 ] && sfx=.checked.lax
[ -z "$files" ] && { echo 'fstar.exe: usage' >&2; exit 0; }
if [ "$dep" = 1 ]; then
  for f in $files; do echo "$cache/$f$sfx: $f"; done
  exit 0
fi
mkdir -p "$cache"
for f in $files; do [ -e "$cache/$f$sfx" ] || touch "$cache/$f$sfx"; done
exit 0
"#;

/// Admitting a module moves the cache directory, so the targets `.depend`
/// names move with it. A `.depend` left over from the previous
/// configuration would leave those targets with no source file.
#[test]
fn admitting_a_module_regenerates_depend_for_the_new_cache_directory() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    let (out, ok) = project.make("verify");
    assert!(ok, "{out}");

    let (out, ok) = project.run(&["verify", "ADMIT_MODULES=A.fst"], &[]);
    assert!(ok, "{out}");
    let admitted: Vec<_> = project
        .fstar_log()
        .lines()
        .filter(|line| line.contains("--admit_smt_queries"))
        .map(ToString::to_string)
        .collect();
    assert_eq!(admitted.len(), 1, "log: {}", project.fstar_log());
    assert!(
        admitted[0].ends_with(" A.fst"),
        "the admitted module reached F*: {}",
        admitted[0]
    );
}

/// F* given no module to check exits 0, so a checked target `.depend` does
/// not cover must stop the build rather than pass it.
#[test]
fn a_checked_target_with_no_source_file_fails_the_build() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    assert!(project.make(".depend").1);

    // A `.depend` covering nothing, newer than the roots it is derived
    // from, so that make keeps it.
    std::fs::write(project.root().join(".depend"), "").unwrap();
    backdate(&project.root().join("A.fst"));
    backdate(&project.root().join(".hax-roots"));
    std::fs::write(project.root().join("fstar.log"), "").unwrap();

    let (out, ok) = project.make("verify");
    assert!(!ok, "a target with no source file must not pass:\n{out}");
    assert!(out.contains("has no source file"), "{out}");
    assert_eq!(project.fstar_log(), "", "F* must not have been run");
}

/// Goals that describe or tear down the build must neither extract nor
/// delete F* files that hax cannot regenerate.
#[test]
fn clean_and_the_describing_goals_neither_extract_nor_delete_sources() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    let handwritten = project.root().join("Spec.fsti");
    std::fs::write(&handwritten, "module Spec\n").unwrap();
    std::fs::remove_file(project.root().join("A.fst")).unwrap();

    let extract = [
        ("HAX_AUTO_EXTRACT", "yes"),
        ("HAX_EXTRACT_COMMAND", "touch extracted.marker"),
    ];
    for goal in ["clean", "help", "describe", "include-dirs"] {
        let (out, ok) = project.run(&[goal], &extract);
        assert!(ok, "`make {goal}` failed:\n{out}");
        assert!(
            !project.root().join("extracted.marker").exists(),
            "`make {goal}` ran an extraction"
        );
    }
    assert!(
        handwritten.exists(),
        "`make clean` deleted a hand-written F* file"
    );
}

#[test]
fn a_failed_dep_run_leaves_no_depend_behind_and_stays_recoverable() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_CYCLIC);

    let (first, ok) = project.make(".depend");
    assert!(!ok, "the cyclic dependency run must fail:\n{first}");
    assert!(
        !project.root().join(".depend").exists(),
        "a failed `--dep full` must not leave a `.depend` behind:\n{first}"
    );
    assert!(
        !project.root().join(".depend.tmp").exists(),
        "the scratch file must be cleaned up:\n{first}"
    );

    let (second, ok) = project.make(".depend");
    assert!(!ok, "the second run must fail too:\n{second}");
    assert!(
        !second.contains("missing separator"),
        "a failed dependency run must not corrupt `.depend`:\n{second}"
    );
}

#[test]
fn a_failed_dep_run_preserves_the_last_good_depend() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_WORKING);

    let (out, ok) = project.make(".depend");
    assert!(ok, "the working run must succeed:\n{out}");
    let good = std::fs::read_to_string(project.root().join(".depend")).unwrap();
    assert!(good.contains("no dependencies"), "unexpected: {good:?}");

    write_executable(&project.bin.join("fstar.exe"), FSTAR_STUB_CYCLIC);
    std::fs::write(project.root().join("B.fst"), "module B\nlet b : int = 2\n").unwrap();
    // Backdate, so the run below happens where a filesystem stores mtimes
    // to the second and make would otherwise call `.depend` up to date.
    backdate(&project.root().join(".depend"));

    let (out, ok) = project.make(".depend");
    assert!(!ok, "the cyclic run must fail:\n{out}");
    assert_eq!(
        std::fs::read_to_string(project.root().join(".depend")).unwrap(),
        good,
        "a failed run must leave the last known-good `.depend` untouched"
    );
}

#[test]
fn adding_and_removing_a_module_invalidates_depend() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_WORKING);
    assert!(project.make(".depend").1);

    std::fs::write(project.root().join("B.fst"), "module B\nlet b : int = 2\n").unwrap();
    assert!(project.make(".depend").1);
    let stamp = std::fs::read_to_string(project.root().join(".hax-roots")).unwrap();
    assert!(
        stamp.contains("B.fst"),
        "roots stamp missing B.fst: {stamp:?}"
    );

    std::fs::remove_file(project.root().join("B.fst")).unwrap();
    let (out, ok) = project.make(".depend");
    assert!(ok, "{out}");
    let stamp = std::fs::read_to_string(project.root().join(".hax-roots")).unwrap();
    assert!(
        !stamp.contains("B.fst"),
        "roots stamp still names the removed module: {stamp:?}"
    );
    assert!(
        stamp.contains("A.fst"),
        "the remaining module dropped out of the stamp: {stamp:?}"
    );
}

/// The extraction runs after make has read the directory once, so the
/// modules it writes must still be found.
#[test]
fn auto_extraction_verifies_the_modules_it_writes() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    std::fs::remove_file(project.root().join("A.fst")).unwrap();
    let extract = [
        ("HAX_AUTO_EXTRACT", "yes"),
        ("HAX_EXTRACT_COMMAND", "touch B.fst"),
    ];
    let (out, ok) = project.run(&["verify"], &extract);
    assert!(ok, "{out}");
    assert_eq!(
        project.checks_of("B.fst"),
        1,
        "log: {}",
        project.fstar_log()
    );
}

/// A flag passed through `FSTAR_FLAGS_EXTRA` weakens a check as much as one
/// in `OTHERFLAGS`, so its results must not be reused by a plain run.
#[test]
fn extra_fstar_flags_do_not_share_the_verified_cache() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    let admit = [("FSTAR_FLAGS_EXTRA", "--admit_smt_queries true")];
    let (out, ok) = project.run(&["verify"], &admit);
    assert!(ok, "{out}");
    let (out, ok) = project.make("verify");
    assert!(ok, "{out}");
    assert_eq!(
        project.checks_of("A.fst"),
        2,
        "log: {}",
        project.fstar_log()
    );
}

/// F* keeps a `.checked` file that is still valid, so make must bring it up
/// to date itself, or it would recheck the module on every run.
#[test]
fn a_module_f_star_did_not_rewrite_is_not_rechecked_forever() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    assert!(project.make("verify").1);
    backdate(&project.root().join(".fstar-cache/checked/A.fst.checked"));

    for _ in 0..2 {
        let (out, ok) = project.make("verify");
        assert!(ok, "{out}");
    }
    assert_eq!(
        project.checks_of("A.fst"),
        2,
        "log: {}",
        project.fstar_log()
    );
}

/// A library module may gain an import, so changing one must regenerate
/// `.depend`.
#[test]
fn a_changed_library_module_regenerates_depend() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    std::fs::create_dir(project.root().join("lib")).unwrap();
    std::fs::write(project.root().join("lib/M.fst"), "module M\n").unwrap();
    let lib = [("FSTAR_INCLUDE_DIRS_EXTRA", "lib")];
    assert!(project.run(&[".depend"], &lib).1);
    // `.depend` last, so that it is the newest of them.
    for file in ["lib/M.fst", "A.fst", ".hax-roots", ".depend"] {
        backdate(&project.root().join(file));
    }
    assert!(project.run(&[".depend"], &lib).1);
    assert_eq!(project.dep_runs(), 1, "up to date: {}", project.fstar_log());

    std::fs::write(project.root().join("lib/M.fst"), "module M\nopen A\n").unwrap();
    assert!(project.run(&[".depend"], &lib).1);
    assert_eq!(project.dep_runs(), 2, "log: {}", project.fstar_log());
}

#[test]
fn clean_then_verify_in_one_run_verifies() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    assert!(project.make("verify").1);
    let (out, ok) = project.run(&["clean", "verify"], &[]);
    assert!(ok, "{out}");
    assert_eq!(
        project.checks_of("A.fst"),
        2,
        "log: {}",
        project.fstar_log()
    );
}

/// The include order decides which of two same-named modules F* picks, so
/// removing duplicates must not reorder it.
#[test]
fn include_directories_keep_their_order() {
    if !have("make") {
        return;
    }
    let project = Project::new(FSTAR_STUB_RECORDING);
    let (out, ok) = project.run(&["A.fst-in"], &[("FSTAR_INCLUDE_DIRS_EXTRA", "zz aa zz")]);
    assert!(ok, "{out}");
    let core = project.root().join("proof-libs/fstar/core");
    let expected = format!("--include zz --include aa --include {}", core.display());
    assert!(out.contains(&expected), "{out}");
}
