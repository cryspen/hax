//! The `hax-lib` compatibility check.
//!
//! `cargo-hax` and `hax-lib` are released in lockstep with one version
//! number. The range of `hax-lib` versions a binary accepts is derived
//! from its own version, not maintained by hand: the binary's own minor
//! series, capped at its own patch level (`>=0.3.0, <=0.3.7` for a 0.3.7
//! binary); after 1.0, the same construction one level up (`>=1.0.0,
//! <=1.2.3` for 1.2.3). This is exactly the set of versions the binary
//! can be sure to understand: older same-series releases emit nothing the
//! newer binary does not know, and anything newer than the binary is
//! rejected in favor of updating `cargo-hax`.
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

/// The inclusive range of `hax-lib` versions this binary accepts,
/// derived from its own version.
pub fn supported_range() -> (Version, Version) {
    range_of(
        &Version::parse(env!("CARGO_PKG_VERSION"))
            .expect("CARGO_PKG_VERSION is always valid semver"),
    )
}

/// [`supported_range`] over an explicit version, so the construction can be
/// checked for versions this binary does not have.
///
/// The range is built from `own`'s release version. Taking `own` itself as
/// the cap would make the range empty for a pre-release: `0.4.0-rc.1` ranks
/// below `0.4.0`, so `>=0.4.0, <=0.4.0-rc.1` would admit nothing at all.
fn range_of(own: &Version) -> (Version, Version) {
    let own = release(own);
    let min = if own.major == 0 {
        Version::new(0, own.minor, 0)
    } else {
        Version::new(own.major, 0, 0)
    };
    (min, own)
}

/// How a resolved `hax-lib` version relates to the supported range. Shared
/// with the messages reporting it.
pub use hax_types::diagnostics::message::HaxLibCompatibility as Compatibility;

pub fn classify(found: &Version) -> Compatibility {
    classify_in(&supported_range(), found)
}

/// [`classify`] against an explicit range, so a range this binary does not
/// have can be checked.
fn classify_in((min, max): &(Version, Version), found: &Version) -> Compatibility {
    let found = release(found);
    if found < *min {
        Compatibility::TooOld
    } else if found > *max {
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
/// When the invocation selects packages itself (`-C -p ... ;`), which
/// members it compiles is Cargo's answer to give. The gate then applies to
/// what no selection can dodge: an incompatibility every member shares. A
/// project mixing compatible and incompatible `hax-lib` versions is left to
/// fail at compile time instead of being guessed about.
pub fn enforce(project: &ProjectContext, message_format: MessageFormat) -> bool {
    let all = check(project);
    let results: Vec<_> = if project.selects_packages {
        let any_compatible = all
            .iter()
            .any(|result| result.compatibility == Compatibility::Compatible);
        if any_compatible { Vec::new() } else { all }
    } else if let Some(root) = &project.root_package {
        all.into_iter()
            .filter(|result| result.crate_name == root.name)
            .collect()
    } else {
        all
    };
    let (min, max) = supported_range();
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
            min: min.to_string(),
            max: max.to_string(),
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
    fn range_is_own_series_capped_at_own_version() {
        // This binary is pre-1.0, so the range is its own minor series.
        let own = Version::parse(env!("CARGO_PKG_VERSION")).unwrap();
        let (min, max) = supported_range();
        assert_eq!(min, Version::new(0, own.minor, 0));
        assert_eq!(max, own);
    }

    #[test]
    fn classification_directions() {
        let own = Version::parse(env!("CARGO_PKG_VERSION")).unwrap();
        // The binary's own version and the series floor are compatible.
        assert_eq!(classify(&own), Compatibility::Compatible);
        assert_eq!(
            classify(&Version::new(0, own.minor, 0)),
            Compatibility::Compatible
        );
        // A newer patch is rejected as TooNew: the cap moves with the
        // binary, not the series.
        assert_eq!(
            classify(&Version::new(own.major, own.minor, own.patch + 1)),
            Compatibility::TooNew
        );
        assert_eq!(
            classify(&Version::new(own.major, own.minor + 1, 0)),
            Compatibility::TooNew
        );
        // An older series is TooOld.
        assert_eq!(classify(&Version::new(0, 2, 0)), Compatibility::TooOld);
    }

    /// A pre-release binary accepts the same range as its release, and the
    /// `hax-lib` released alongside it.
    #[test]
    fn a_pre_release_is_treated_as_its_release() {
        for own in ["0.4.0-rc.1", "1.2.3-rc.1+build.5"] {
            let own = Version::parse(own).unwrap();
            let range = range_of(&own);
            let (min, max) = &range;
            assert_eq!(*max, release(&own), "{own}");
            assert!(min <= max, "{own}: empty range {min}..={max}");
            // The lockstep `hax-lib` carries the same pre-release.
            assert_eq!(
                classify_in(&range, &own),
                Compatibility::Compatible,
                "{own}"
            );
            // And the release it precedes, being the cap, is accepted too.
            assert_eq!(classify_in(&range, max), Compatibility::Compatible, "{own}");
        }
    }

    /// The range this binary reports never carries a pre-release, whatever
    /// its own version is, so the reported bounds read as versions to pin.
    #[test]
    fn the_reported_range_is_release_versions() {
        let (min, max) = supported_range();
        assert!(min.pre.is_empty() && min.build.is_empty());
        assert!(max.pre.is_empty() && max.build.is_empty());
        assert!(min <= max);
    }
}
