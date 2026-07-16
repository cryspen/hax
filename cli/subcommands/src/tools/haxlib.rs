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

use cargo_metadata::semver::Version;
use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;

use super::project::ProjectContext;

/// The inclusive range of `hax-lib` versions this binary accepts,
/// derived from its own version.
pub fn supported_range() -> (Version, Version) {
    let own = Version::parse(env!("CARGO_PKG_VERSION"))
        .expect("CARGO_PKG_VERSION is always valid semver");
    let min = if own.major == 0 {
        Version::new(0, own.minor, 0)
    } else {
        Version::new(own.major, 0, 0)
    };
    (min, own)
}

/// How a resolved `hax-lib` version relates to the supported range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Compatibility {
    Compatible,
    /// Too old or on a different series: the project's dependency needs
    /// updating (or an older cargo-hax is needed).
    TooOld,
    /// Newer than the binary (typically after a `cargo update`): update
    /// cargo-hax, or pin `hax-lib` back to the binary's version.
    TooNew,
}

pub fn classify(found: &Version) -> Compatibility {
    let (min, max) = supported_range();
    if *found < min {
        Compatibility::TooOld
    } else if *found > max {
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
pub fn enforce(project: &ProjectContext, message_format: MessageFormat) -> bool {
    let results: Vec<_> = match &project.root_package {
        Some(root) => check(project)
            .into_iter()
            .filter(|result| result.crate_name == root.name)
            .collect(),
        None => check(project),
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
}
