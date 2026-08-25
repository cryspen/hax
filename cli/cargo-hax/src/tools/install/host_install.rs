//! Tests installing the real artifacts for the platform they run on, and
//! running them.
//!
//! A checksum cannot tell whether a binary runs: one built for the wrong
//! architecture, an unsigned one on macOS, and one needing a newer glibc than
//! the host all verify and then fail to execute. Only the system that has to
//! load a binary can answer that, so these tests run natively on each
//! supported platform in CI.
//!
//! They reach the network and install into the real tool cache, exactly as
//! `cargo hax tools install --force` would, and are `#[ignore]`d
//! accordingly.

use std::path::Path;
use std::process::{Command, Stdio};

use hax_types::cli_options::MessageFormat;

use super::{Installed, ensure_installed};
use crate::tools::{cache, defaults::defaults, manifest, tool_executables};

/// The versions this release defaults to must install from their real
/// artifacts and run here. A second install must reuse the cache rather than
/// download again, which every run after the first depends on.
#[test]
#[ignore = "reaches the network, and installs into the tool cache"]
fn default_tools_install_and_run_on_this_platform() {
    assert!(
        std::env::var_os(manifest::MANIFEST_OVERRIDE_ENV).is_none(),
        "{} is set, so this would not test what the release ships",
        manifest::MANIFEST_OVERRIDE_ENV
    );

    for (tool, version) in &defaults().tools {
        // Forcing makes the outcome independent of what the cache already
        // holds: a fresh, checksum-verified download on every run.
        let installed = ensure_installed(tool, version, true, MessageFormat::Json)
            .unwrap_or_else(|e| panic!("installing {tool} {version}: {e}"));
        assert_eq!(
            installed,
            Installed::Fresh { verified: true },
            "{tool} {version} did not install fresh and verified"
        );

        // The next run must reuse that install and still see it as verified:
        // the flag has to survive in the metadata, or later runs warn about an
        // unverified copy.
        let reused = ensure_installed(tool, version, false, MessageFormat::Json)
            .unwrap_or_else(|e| panic!("reusing {tool} {version}: {e}"));
        assert_eq!(
            reused,
            Installed::AlreadyCached { verified: true },
            "{tool} {version} was not reused from the cache"
        );

        let dir = cache::version_dir(tool, version).unwrap();
        for executable in tool_executables(tool) {
            let path = cache::executable_path(&dir, executable)
                .unwrap_or_else(|e| panic!("{tool} {version}: {e}"));
            if runs_on_its_own(executable) {
                assert_runs(&path);
            } else {
                assert_executable(&path);
            }
        }
    }
}

/// Whether the system can be asked to run an executable on its own.
///
/// `charon-driver` cannot: it links against the `librustc_driver` shared
/// library of the toolchain it was built with, which the archive does not
/// ship, so only `charon` can load it, through that toolchain. On Linux the
/// dynamic loader reports the missing library through an ordinary exit,
/// which `assert_runs` accepts, so spawning it still catches a file built
/// for another platform; macOS kills it by signal, indistinguishable from a
/// refused binary, so there being present and executable is all that can be
/// asked of it.
fn runs_on_its_own(executable: &str) -> bool {
    executable != "charon-driver" || cfg!(not(target_os = "macos"))
}

/// Assert a file carries an execute bit, for executables that cannot be
/// held to actually running.
fn assert_executable(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    let mode = std::fs::metadata(path)
        .unwrap_or_else(|e| panic!("could not stat {}: {e}", path.display()))
        .permissions()
        .mode();
    assert!(
        mode & 0o111 != 0,
        "{} is not executable (mode {mode:o})",
        path.display()
    );
}

/// Assert the operating system can load and run an executable.
///
/// Only the loading is under test, so any ordinary exit counts: the tools
/// disagree about what `--version` means, and a usage error still proves the
/// binary ran. What must not happen is failing to spawn (a wrong-architecture
/// or non-executable file) or dying on a signal (how macOS refuses an unsigned
/// arm64 binary).
fn assert_runs(path: &Path) {
    use std::os::unix::process::ExitStatusExt;

    let output = Command::new(path)
        .arg("--version")
        // Nothing may wait on inherited stdin: a tool that prompts would hang
        // the job rather than fail it.
        .stdin(Stdio::null())
        .output()
        .unwrap_or_else(|e| {
            panic!(
                "could not run {}: {e}\nthe artifact may be built for another \
                 platform, or not be an executable at all",
                path.display()
            )
        });
    if let Some(signal) = output.status.signal() {
        panic!(
            "{} was killed by signal {signal} instead of running\n\
             on macOS this is how an unsigned or wrongly signed binary is \
             refused; elsewhere, suspect a corrupt artifact\nstderr: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim(),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `assert_runs` accepts an executable the system can run. `/bin/sh`
    /// exists on every supported platform, and whether it understands
    /// `--version` differs between them, which is the point: the check must
    /// not depend on the exit status.
    #[test]
    fn assert_runs_accepts_a_system_executable() {
        assert_runs(Path::new("/bin/sh"));
    }

    /// And rejects a file the system cannot execute.
    #[test]
    #[should_panic(expected = "could not run")]
    fn assert_runs_rejects_a_non_executable() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("charon");
        std::fs::write(&path, "not an executable").unwrap();
        assert_runs(&path);
    }

    /// `assert_executable` accepts a file with an execute bit.
    #[test]
    fn assert_executable_accepts_a_system_executable() {
        assert_executable(Path::new("/bin/sh"));
    }

    /// And rejects a file without one.
    #[test]
    #[should_panic(expected = "is not executable")]
    fn assert_executable_rejects_a_plain_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("charon-driver");
        std::fs::write(&path, "not an executable").unwrap();
        assert_executable(&path);
    }
}
