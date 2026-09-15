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
        let path = format!(
            "{}:{}",
            self.bin.display(),
            std::env::var("PATH").unwrap_or_default()
        );
        let out = Command::new("make")
            .arg(target)
            .current_dir(self.root())
            .env("PATH", path)
            .env("FSTAR_BIN", self.bin.join("fstar.exe"))
            .env("FINDLIBS_OUTPUT", self.root().join("proof-libs/fstar/core"))
            .env("HAX_AUTO_EXTRACT", "no")
            .env("NO_COLOR", "1")
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
