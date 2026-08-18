//! The `hax-lib` compatibility check.
//!
//! `cargo-hax` and `hax-lib` are released in lockstep with one version
//! number, and that lockstep pair is the only combination that is tested.
//! The check is therefore strict: a binary accepts exactly the `hax-lib`
//! of its own version. This makes every `cargo-hax` release obligated to
//! ship a matching `hax-lib`, even for binary-only fixes.
//!
//! Only *direct* dependencies are checked, per processed crate; with no
//! direct dependency the check is skipped. The check gates only
//! invocations that process source: the `tools` subcommands never abort
//! on it.
//!
//! Comparisons are made on release versions: a pre-release counts as the
//! release it precedes, on both sides, so a pre-release `cargo-hax` accepts
//! the `hax-lib` released alongside it.

use cargo_metadata::semver::Version;
use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;

use super::project::ProjectContext;

/// A version with its pre-release and build metadata dropped.
fn release(version: &Version) -> Version {
    Version::new(version.major, version.minor, version.patch)
}

/// The one `hax-lib` version this binary accepts: its own release version.
pub fn expected_version() -> Version {
    release(
        &Version::parse(env!("CARGO_PKG_VERSION"))
            .expect("CARGO_PKG_VERSION is always valid semver"),
    )
}

/// How a resolved `hax-lib` version relates to the expected one. Shared
/// with the messages reporting it.
pub use hax_types::diagnostics::message::HaxLibCompatibility as Compatibility;

pub fn classify(found: &Version) -> Compatibility {
    classify_against(&expected_version(), found)
}

/// [`classify`] against an explicit expected version, so versions this
/// binary does not have can be checked.
fn classify_against(expected: &Version, found: &Version) -> Compatibility {
    let found = release(found);
    if found < *expected {
        Compatibility::TooOld
    } else if found > *expected {
        Compatibility::TooNew
    } else {
        Compatibility::Compatible
    }
}

/// One crate's check result, for reporting.
pub struct CrateCompatibility {
    pub crate_name: String,
    pub found: String,
    pub compatibility: Compatibility,
}

/// Check every crate of the project that directly depends on `hax-lib`.
pub fn check(project: &ProjectContext) -> Vec<CrateCompatibility> {
    project
        .members
        .iter()
        .filter_map(|member| {
            let found = member.hax_lib.as_ref()?;
            let compatibility = match Version::parse(found) {
                Ok(version) => classify(&version),
                // An unparseable version cannot be judged; let it pass.
                Err(_) => Compatibility::Compatible,
            };
            Some(CrateCompatibility {
                crate_name: member.name.clone(),
                found: found.clone(),
                compatibility,
            })
        })
        .collect()
}

/// Gate a source-processing invocation: report every incompatibility and
/// return whether execution must abort.
///
/// Only the crates this invocation processes are gated: the root package
/// when there is one, every member for a virtual-workspace invocation.
/// Other members' dependencies are not what this run compiles against
/// (`tools show` still reports them all).
///
/// When the invocation selects packages itself, plain `-p <member>`
/// selections are gated exactly: they name the crates the build compiles
/// against. Any other selection (`--workspace`, `--exclude`, path or
/// version specs) is Cargo's answer to give; the gate then applies to what
/// no selection can dodge: an incompatibility every member shares. The
/// same shared check covers a named selection without any direct `hax-lib`
/// dependency: its build still compiles the members it depends on. A
/// project mixing compatible and incompatible `hax-lib` versions is left to
/// fail at compile time instead of being guessed about.
pub fn enforce(project: &ProjectContext, message_format: MessageFormat) -> bool {
    let all = check(project);
    let shared = |all: Vec<CrateCompatibility>| {
        let any_compatible = all
            .iter()
            .any(|result| result.compatibility == Compatibility::Compatible);
        if any_compatible { Vec::new() } else { all }
    };
    let results: Vec<_> = if project.selects_packages {
        let named_members = !project.package_specs.is_empty()
            && project
                .package_specs
                .iter()
                .all(|spec| project.members.iter().any(|member| &member.name == spec));
        if named_members {
            let (selected, rest): (Vec<_>, Vec<_>) = all
                .into_iter()
                .partition(|result| project.package_specs.contains(&result.crate_name));
            if selected.is_empty() {
                shared(rest)
            } else {
                selected
            }
        } else {
            shared(all)
        }
    } else if let Some(root) = &project.root_package {
        all.into_iter()
            .filter(|result| result.crate_name == root.name)
            .collect()
    } else {
        all
    };
    let expected = expected_version();
    let mut incompatible = false;
    for result in results {
        if result.compatibility == Compatibility::Compatible {
            continue;
        }
        incompatible = true;
        HaxMessage::HaxLibIncompatible {
            crate_name: result.crate_name,
            found: result.found,
            binary: env!("CARGO_PKG_VERSION").to_string(),
            expected: expected.to_string(),
            newer: result.compatibility == Compatibility::TooNew,
        }
        .report(message_format, None);
    }
    incompatible
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classification_directions() {
        let own = Version::parse(env!("CARGO_PKG_VERSION")).unwrap();
        // Only the binary's own version is compatible.
        assert_eq!(classify(&own), Compatibility::Compatible);
        assert_eq!(
            classify(&Version::new(own.major, own.minor, own.patch + 1)),
            Compatibility::TooNew
        );
        assert_eq!(
            classify(&Version::new(own.major, own.minor + 1, 0)),
            Compatibility::TooNew
        );
        if own.patch > 0 {
            assert_eq!(
                classify(&Version::new(own.major, own.minor, own.patch - 1)),
                Compatibility::TooOld
            );
        }
        assert_eq!(classify(&Version::new(0, 2, 0)), Compatibility::TooOld);
    }

    /// A pre-release binary accepts the release it precedes and the
    /// lockstep `hax-lib` carrying the same pre-release.
    #[test]
    fn a_pre_release_is_treated_as_its_release() {
        for own in ["0.4.0-rc.1", "1.2.3-rc.1+build.5"] {
            let own = Version::parse(own).unwrap();
            let expected = release(&own);
            assert_eq!(
                classify_against(&expected, &own),
                Compatibility::Compatible,
                "{own}"
            );
            assert_eq!(
                classify_against(&expected, &expected),
                Compatibility::Compatible,
                "{own}"
            );
        }
    }

    fn workspace(members: &[(&str, &str)], package_specs: &[&str]) -> ProjectContext {
        ProjectContext {
            workspace_root: std::path::PathBuf::from("/ws"),
            workspace_config: None,
            members: members
                .iter()
                .map(|(name, hax_lib)| super::super::project::MemberCrate {
                    name: name.to_string(),
                    root: std::path::PathBuf::from("/ws").join(name),
                    config: None,
                    hax_lib: Some(hax_lib.to_string()),
                })
                .collect(),
            root_package: None,
            selects_packages: true,
            package_specs: package_specs.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// A plain `-p <member>` selection gates exactly the selected members;
    /// any other selection falls back to the lenient any-member-compatible
    /// mode.
    #[test]
    fn package_selections_gate_the_selected_members() {
        let compatible = expected_version().to_string();
        let members = [("good", compatible.as_str()), ("bad", "0.0.1")];
        let format = MessageFormat::Human;
        assert!(enforce(&workspace(&members, &["bad"]), format));
        assert!(enforce(&workspace(&members, &["good", "bad"]), format));
        assert!(!enforce(&workspace(&members, &["good"]), format));
        // A spec that is not a member name and a broad selection (empty
        // specs) both stay lenient: one member is compatible.
        assert!(!enforce(&workspace(&members, &["bad@0.1.0"]), format));
        assert!(!enforce(&workspace(&members, &[]), format));
    }

    /// A named member without a direct `hax-lib` dependency falls back to
    /// the shared check: its build still compiles the members it depends
    /// on.
    #[test]
    fn named_members_without_hax_lib_fall_back_to_the_shared_check() {
        let format = MessageFormat::Human;
        let bin = super::super::project::MemberCrate {
            name: "bin".to_string(),
            root: std::path::PathBuf::from("/ws/bin"),
            config: None,
            hax_lib: None,
        };
        let mut project = workspace(&[("bad", "0.0.1")], &["bin"]);
        project.members.push(bin.clone());
        assert!(enforce(&project, format));
        let compatible = expected_version().to_string();
        let mut project = workspace(&[("bad", "0.0.1"), ("good", compatible.as_str())], &["bin"]);
        project.members.push(bin);
        assert!(!enforce(&project, format));
    }

    /// The version this binary reports never carries a pre-release,
    /// whatever its own version is, so it reads as a version to pin.
    #[test]
    fn the_expected_version_is_a_release_version() {
        let expected = expected_version();
        assert!(expected.pre.is_empty() && expected.build.is_empty());
    }
}
