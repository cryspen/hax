//! Generator of the manifest entries for one version of a managed tool: the
//! implementation of `just add-tool-version`.
//!
//! Each artifact comes from the tool's `[fallback]` template and is hashed
//! from that download, so a recorded checksum can never be one copied from
//! the wrong asset. It then goes through the checks a listed entry has to
//! pass, so a moved archive layout or an asset published under the wrong
//! platform's name fails before the entries are committed.
//!
//! Maintainer tooling, hence a test: it stays next to the code it shares and
//! out of the shipped binary.

use hax_types::cli_options::MessageFormat;

use super::manifest_artifacts::check_staged;
use super::{download, sha256_of};
use crate::tools::manifest::{
    self, ArtifactEntry, Manifest, SUPPORTED_PLATFORMS, validate_version_id,
};

/// The `<tool>@<version>` to generate entries for.
const SPEC_ENV: &str = "HAX_ADD_TOOL_VERSION";
/// Where to write them.
const OUT_ENV: &str = "HAX_ADD_TOOL_VERSION_OUT";

/// Write the entries for the version named in [`SPEC_ENV`] to the path in
/// [`OUT_ENV`]. A file rather than stdout, which belongs to the test harness.
#[test]
#[ignore = "maintainer tooling: reaches the network"]
fn add_version() {
    let spec = std::env::var(SPEC_ENV)
        .unwrap_or_else(|_| panic!("{SPEC_ENV} must hold a `<tool>@<version>` specification"));
    let out = std::env::var(OUT_ENV)
        .unwrap_or_else(|_| panic!("{OUT_ENV} must hold the path to write the entries to"));
    let (tool, version) = spec
        .split_once('@')
        .unwrap_or_else(|| panic!("`{spec}` is not a `<tool>@<version>` specification"));

    // The embedded manifest: `include_str!` keeps it in step with the
    // checkout, and no override redirects it.
    let entries =
        entries_for(tool, version, &manifest::embedded()).unwrap_or_else(|e| panic!("{e}"));
    std::fs::write(&out, entries).unwrap_or_else(|e| panic!("could not write {out}: {e}"));
}

/// The entries for one version of a tool, one per platform the tool has a
/// template for, in the order the manifest lists platforms in. A failing
/// artifact fails the whole generation: half a version's entries are not
/// worth committing.
fn entries_for(tool: &str, version: &str, manifest: &Manifest) -> Result<String, String> {
    validate_version_id(version)?;
    let platforms: Vec<&str> = SUPPORTED_PLATFORMS
        .iter()
        .copied()
        .filter(|platform| manifest.fallback_for(tool, version, platform).is_some())
        .collect();
    if platforms.is_empty() {
        return Err(format!(
            "no [fallback] template for {tool} on any supported platform: \
             is it a managed tool?"
        ));
    }

    let mut entries = String::new();
    for platform in platforms {
        let (url, entry_points) = manifest
            .fallback_for(tool, version, platform)
            .expect("the platforms were filtered to those with a template");
        eprintln!("fetching {url}");
        // A staging directory per platform: `download` always writes the same
        // file name.
        let staging = tempfile::tempdir().map_err(|e| format!("could not stage: {e}"))?;
        let context = |e| format!("{tool} {version} on {platform}: {e}");
        let archive = download(&url, staging.path(), MessageFormat::Human).map_err(context)?;
        let entry = ArtifactEntry {
            url,
            sha256: sha256_of(&archive).map_err(context)?,
            entry_points,
        };
        check_staged(tool, &entry, platform, &archive, staging.path()).map_err(context)?;
        entries.push_str(&entry_toml(tool, version, platform, &entry));
    }
    Ok(entries)
}

/// One entry, in the layout the manifest file is written in. The version is
/// validated and the tool is a key of the manifest, so neither needs
/// escaping.
fn entry_toml(tool: &str, version: &str, platform: &str, entry: &ArtifactEntry) -> String {
    let mut block = format!(
        "[tools.{tool}.\"{version}\".{platform}]\nurl = \"{}\"\nsha256 = \"{}\"\n",
        entry.url, entry.sha256
    );
    if let Some(entry_points) = &entry.entry_points {
        let pairs: Vec<String> = entry_points
            .iter()
            .map(|(name, path)| format!("{name} = \"{path}\""))
            .collect();
        block.push_str(&format!("entry_points = {{ {} }}\n", pairs.join(", ")));
    }
    block.push('\n');
    block
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::super::fixtures::{binary_for, make_archive, serve, sha256_hex};
    use super::*;

    const VERSION: &str = "nightly-2026.08.01";

    /// Templates for `charon` on every supported platform, served from
    /// `base`, with the version in the entry-point paths as well as the URL.
    fn template_manifest(base: &str) -> Manifest {
        let sections: String = SUPPORTED_PLATFORMS
            .iter()
            .map(|platform| {
                format!(
                    r#"[fallback.charon.{platform}]
url = "{base}/{platform}/charon-{{version}}.tar.gz"
entry_points = {{ charon = "charon-{{version}}/charon", charon-driver = "charon-{{version}}/charon-driver" }}
"#
                )
            })
            .collect();
        manifest::parse(&sections).unwrap()
    }

    /// The archive each platform's template resolves to, holding an
    /// executable built for `built_for(platform)`.
    fn archives(built_for: impl Fn(&str) -> String) -> Vec<(String, Vec<u8>)> {
        SUPPORTED_PLATFORMS
            .iter()
            .map(|platform| {
                let binary = binary_for(&built_for(platform));
                let charon = format!("charon-{VERSION}/charon");
                let driver = format!("charon-{VERSION}/charon-driver");
                let archive = make_archive(&[
                    (charon.as_str(), binary.as_slice()),
                    (driver.as_str(), binary.as_slice()),
                ]);
                (format!("/{platform}/charon-{VERSION}.tar.gz"), archive)
            })
            .collect()
    }

    /// The generated entries parse back as the verified entries of every
    /// platform.
    #[test]
    fn entries_record_each_platform_with_its_hash_and_substituted_paths() {
        let archives = archives(|platform| platform.to_string());
        let base = serve(archives.iter().cloned().collect::<HashMap<_, _>>());

        let entries = entries_for("charon", VERSION, &template_manifest(&base)).unwrap();

        for (platform, (path, archive)) in SUPPORTED_PLATFORMS.iter().zip(&archives) {
            assert!(
                entries.contains(&format!(
                    "[tools.charon.\"{VERSION}\".{platform}]\n\
                     url = \"{base}{path}\"\n\
                     sha256 = \"{}\"\n\
                     entry_points = {{ charon = \"charon-{VERSION}/charon\", \
                     charon-driver = \"charon-{VERSION}/charon-driver\" }}\n",
                    sha256_hex(archive)
                )),
                "{entries}"
            );
        }
        assert!(!entries.contains("{version}"), "{entries}");

        let parsed = manifest::parse(&entries).unwrap();
        for platform in SUPPORTED_PLATFORMS.iter().copied() {
            assert!(
                parsed.lookup("charon", VERSION, platform).is_some(),
                "{platform} is missing from:\n{entries}"
            );
        }
    }

    /// So a defect no checksum can catch is never recorded as verified.
    #[test]
    fn a_defective_or_missing_artifact_fails_the_generation() {
        // Every platform's URL serving the same x86_64 executable: the asset
        // published under the wrong platform's name.
        let archives = archives(|_| "linux-x86_64".to_string());
        let base = serve(archives.into_iter().collect::<HashMap<_, _>>());
        let manifest = template_manifest(&base);

        let error = entries_for("charon", VERSION, &manifest).unwrap_err();
        assert!(error.contains("on linux-aarch64"), "{error}");
        assert!(error.contains("linux-x86_64 binary"), "{error}");

        // A version the tool never published.
        let error = entries_for("charon", "nightly-2026.01.01", &manifest).unwrap_err();
        assert!(error.contains("on linux-x86_64"), "{error}");
        assert!(error.contains("404"), "{error}");
    }

    #[test]
    fn an_unmanaged_tool_and_an_unusable_version_are_rejected() {
        let manifest = template_manifest("http://127.0.0.1:1");

        let error = entries_for("aeneas", VERSION, &manifest).unwrap_err();
        assert!(error.contains("aeneas"), "{error}");

        // Rejected before anything is fetched: the version goes into the
        // generated entry verbatim.
        let error = entries_for("charon", "../escape", &manifest).unwrap_err();
        assert!(error.contains("../escape"), "{error}");
    }
}
