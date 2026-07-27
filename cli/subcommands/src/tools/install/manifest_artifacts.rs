//! Tests checking the shipped manifest against the artifacts it names.
//!
//! A manifest entry can fail to describe reality: a URL can 404 after an
//! upstream release is retagged, a checksum can be recorded from the wrong
//! file, an archive's layout can move out from under `entry_points`, and an
//! artifact can be published under the wrong platform's name. None of that is
//! visible without fetching the artifact, so the tests that fetch one are
//! `#[ignore]`d and left to CI. They cover all four supported platforms from
//! whichever one runs them: downloading, hashing and reading an archive are
//! platform-independent. Whether a binary *runs* is left to the tests that
//! install and run the real artifacts natively.

use std::path::Path;
use std::time::Duration;

use hax_types::cli_options::MessageFormat;

use super::{archive_format, download, extract, verify_sha256};
use crate::tools::{MANAGED_TOOLS, cache, defaults::defaults, manifest, tool_executables};

/// Every artifact the embedded manifest lists, as
/// `(tool, version, platform, entry)`.
fn listed_artifacts() -> Vec<(String, String, String, manifest::ArtifactEntry)> {
    let manifest = manifest::embedded();
    manifest
        .tools
        .iter()
        .flat_map(|(tool, versions)| {
            versions.iter().flat_map(move |(version, platforms)| {
                platforms.iter().map(move |(platform, entry)| {
                    (
                        tool.clone(),
                        version.clone(),
                        platform.clone(),
                        entry.clone(),
                    )
                })
            })
        })
        .collect()
}

/// The manifest may only name artifacts this binary can actually unpack, on
/// every supported platform.
#[test]
fn listed_urls_and_fallbacks_are_unpackable_archives() {
    for (tool, version, platform, entry) in listed_artifacts() {
        let entry_name = format!("{tool} {version} on {platform}");
        assert!(
            archive_format(&entry.url).is_some(),
            "{entry_name}: {} is not a format `extract` understands",
            entry.url
        );
    }

    // Every managed tool needs a fallback template on every supported
    // platform, or a version the manifest does not list is uninstallable
    // there even though the platform is supported.
    let manifest = manifest::embedded();
    for tool in MANAGED_TOOLS {
        for platform in manifest::SUPPORTED_PLATFORMS.iter().copied() {
            let (url, _) = manifest
                .fallback_for(tool, "v0", platform)
                .unwrap_or_else(|| panic!("no fallback template for {tool} on {platform}"));
            assert!(url.starts_with("https://"), "{tool} on {platform}: {url}");
            assert!(
                archive_format(&url).is_some(),
                "{tool} fallback on {platform}: {url} is not a format `extract` understands"
            );
        }
    }
}

/// A URL that stops resolving breaks a project pinned to that version, not
/// just the current default. Checked with HEADs, so this stays cheap as the
/// manifest grows.
#[test]
#[ignore = "reaches the network"]
fn every_listed_artifact_is_still_published() {
    let failures: Vec<String> = listed_artifacts()
        .iter()
        .filter_map(|(tool, version, platform, entry)| {
            check_published(&entry.url)
                .err()
                .map(|e| format!("{tool} {version} on {platform}: {e}"))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} of the manifest's artifacts are unreachable:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

/// The versions a release resolves to by default. Only the defaults, so that
/// the nightly run's cost stays fixed as the manifest grows.
#[test]
#[ignore = "reaches the network"]
fn default_artifacts_verify() {
    let defaults = &defaults().tools;
    verify_all(
        "default",
        listed_artifacts()
            .into_iter()
            .filter(|(tool, version, ..)| defaults.get(tool) == Some(version))
            .collect(),
    );
}

/// Every listed version: one whose checksum was recorded from the wrong file
/// is uninstallable for whoever pins it. Downloads the whole manifest, so this
/// runs on a change to it rather than nightly.
#[test]
#[ignore = "reaches the network, and downloads every listed artifact"]
fn every_listed_artifact_verifies() {
    verify_all("listed", listed_artifacts());
}

/// Put each artifact through the checks an install performs, reporting all
/// failures rather than the first.
fn verify_all(which: &str, artifacts: Vec<(String, String, String, manifest::ArtifactEntry)>) {
    assert!(!artifacts.is_empty(), "no {which} artifact to verify");
    let failures: Vec<String> = artifacts
        .iter()
        .filter_map(|(tool, version, platform, entry)| {
            check_artifact(tool, entry, platform)
                .err()
                .map(|e| format!("{tool} {version} on {platform}: {e}"))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} of the {} {which} artifacts are broken:\n  {}",
        failures.len(),
        artifacts.len(),
        failures.join("\n  ")
    );
}

/// Whether a URL is still published, without downloading its body: a HEAD,
/// falling back to a one-byte ranged GET for hosts that refuse HEAD.
fn check_published(url: &str) -> Result<(), String> {
    // The same client an install uses, so this reaches the network the same
    // way (proxy, trust store) a user's install would.
    let agent = super::agent(url, Duration::from_secs(60));
    match agent.head(url).call() {
        Ok(_) => Ok(()),
        Err(ureq::Error::Status(403 | 405, _)) => agent
            .get(url)
            .set("Range", "bytes=0-0")
            .call()
            .map(|_| ())
            .map_err(|e| e.to_string()),
        Err(ureq::Error::Status(code, _)) => Err(format!("HTTP status {code} for {url}")),
        Err(e) => Err(format!("{e} for {url}")),
    }
}

/// Download one artifact and put it through the checks an install performs: the
/// checksum, extraction, and the resolution of every executable of the tool.
/// Additionally, that the executables are built for the platform the entry
/// files them under, which no checksum can tell.
fn check_artifact(
    tool: &str,
    entry: &manifest::ArtifactEntry,
    platform: &str,
) -> Result<(), String> {
    let staging = tempfile::tempdir().map_err(|e| format!("could not stage: {e}"))?;
    let archive = download(&entry.url, staging.path(), MessageFormat::Json)?;
    verify_sha256(&archive, &entry.sha256, &entry.url)?;
    let contents = staging.path().join("contents");
    extract(&archive, &entry.url, &contents)?;

    // Resolve the executables the way a real install does, through the entry
    // point metadata, so a moved layout fails here as it would fail a user.
    cache::write_metadata(
        &contents,
        &cache::InstallMetadata {
            entry_points: entry.entry_points.clone(),
            source_url: Some(entry.url.clone()),
            checksum_verified: Some(true),
        },
    )?;
    for executable in tool_executables(tool) {
        let path = cache::executable_path(&contents, executable)?;
        if let Some(built_for) = binary_platform(&path)?
            && built_for != platform
        {
            return Err(format!(
                "`{executable}` is a {built_for} binary, but the artifact is filed \
                 under {platform}"
            ));
        }
    }
    Ok(())
}

/// The platform a native executable was built for, from its ELF or Mach-O
/// header. `None` for anything this does not recognize (a wrapper script, a
/// universal binary), which is not evidence of a mismatch.
fn binary_platform(path: &Path) -> Result<Option<String>, String> {
    use std::io::Read;

    let mut header = [0u8; 20];
    let mut file =
        std::fs::File::open(path).map_err(|e| format!("could not read {}: {e}", path.display()))?;
    if file.read_exact(&mut header).is_err() {
        // Too short to be a native executable.
        return Ok(None);
    }

    // ELF, little-endian (both supported Linux architectures are): the
    // `e_machine` half-word at offset 18.
    if header[..4] == *b"\x7FELF" && header[5] == 1 {
        return Ok(match u16::from_le_bytes([header[18], header[19]]) {
            0x3E => Some("linux-x86_64".to_string()),
            0xB7 => Some("linux-aarch64".to_string()),
            _ => None,
        });
    }
    // Mach-O, 64-bit little-endian: the `cputype` word at offset 4.
    if u32::from_le_bytes([header[0], header[1], header[2], header[3]]) == 0xFEED_FACF {
        return Ok(
            match u32::from_le_bytes([header[4], header[5], header[6], header[7]]) {
                0x0100_0007 => Some("macos-x86_64".to_string()),
                0x0100_000C => Some("macos-aarch64".to_string()),
                _ => None,
            },
        );
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A gzipped tar of `(path, contents)` files, mode 0755.
    fn make_archive(files: &[(&str, &[u8])]) -> Vec<u8> {
        let mut builder = tar::Builder::new(flate2::write::GzEncoder::new(
            Vec::new(),
            flate2::Compression::fast(),
        ));
        for (path, contents) in files {
            let mut header = tar::Header::new_gnu();
            header.set_size(contents.len() as u64);
            header.set_mode(0o755);
            header.set_cksum();
            builder.append_data(&mut header, path, *contents).unwrap();
        }
        builder.into_inner().unwrap().finish().unwrap()
    }

    /// A little-endian ELF header for one of the supported Linux
    /// architectures, padded to a plausible file.
    fn elf(machine: u16) -> Vec<u8> {
        let mut bytes = vec![0u8; 64];
        bytes[..4].copy_from_slice(b"\x7FELF");
        bytes[4] = 2; // 64-bit
        bytes[5] = 1; // little-endian
        bytes[18..20].copy_from_slice(&machine.to_le_bytes());
        bytes
    }

    /// Serve a fixed set of paths on localhost, and return the base URL.
    fn serve(files: std::collections::HashMap<String, Vec<u8>>) -> String {
        let server = tiny_http::Server::http("127.0.0.1:0").unwrap();
        let port = server.server_addr().to_ip().unwrap().port();
        std::thread::spawn(move || {
            for request in server.incoming_requests() {
                match files.get(request.url()) {
                    Some(data) => request
                        .respond(tiny_http::Response::from_data(data.clone()))
                        .unwrap(),
                    None => request.respond(tiny_http::Response::empty(404)).unwrap(),
                }
            }
        });
        format!("http://127.0.0.1:{port}")
    }

    fn sha256_hex(data: &[u8]) -> String {
        hex::encode(<sha2::Sha256 as sha2::Digest>::digest(data))
    }

    fn entry(url: String, sha256: String) -> manifest::ArtifactEntry {
        manifest::ArtifactEntry {
            url,
            sha256,
            entry_points: None,
        }
    }

    /// The checks themselves, driven against a local server: the network tests
    /// above only differ in which host they talk to.
    #[test]
    fn the_artifact_check_accepts_a_good_archive_and_names_each_defect() {
        let driver = elf(0x3E);
        let good = make_archive(&[("bin/charon", &driver), ("bin/charon-driver", &driver)]);
        let arm = elf(0xB7);
        let wrong_arch = make_archive(&[("bin/charon", &arm), ("bin/charon-driver", &arm)]);
        let incomplete = make_archive(&[("bin/charon", &driver)]);
        let base = serve(std::collections::HashMap::from([
            ("/good.tar.gz".to_string(), good.clone()),
            ("/wrong-arch.tar.gz".to_string(), wrong_arch.clone()),
            ("/incomplete.tar.gz".to_string(), incomplete.clone()),
            ("/not-an-archive.tar.gz".to_string(), b"not gzip".to_vec()),
        ]));

        // The happy path: correct checksum, both executables present, built
        // for the platform the entry files them under.
        let good_entry = entry(format!("{base}/good.tar.gz"), sha256_hex(&good));
        check_artifact("charon", &good_entry, "linux-x86_64").unwrap();

        // The same artifact filed under the wrong platform.
        let error = check_artifact("charon", &good_entry, "macos-aarch64").unwrap_err();
        assert!(error.contains("linux-x86_64 binary"), "{error}");
        assert!(error.contains("filed under macos-aarch64"), "{error}");

        // An aarch64 archive published as the x86_64 one: the defect a
        // checksum cannot catch, since the checksum is of the wrong file too.
        let error = check_artifact(
            "charon",
            &entry(format!("{base}/wrong-arch.tar.gz"), sha256_hex(&wrong_arch)),
            "linux-x86_64",
        )
        .unwrap_err();
        assert!(error.contains("linux-aarch64 binary"), "{error}");

        // A checksum recorded from a different file.
        let error = check_artifact(
            "charon",
            &entry(format!("{base}/good.tar.gz"), "0".repeat(64)),
            "linux-x86_64",
        )
        .unwrap_err();
        assert!(error.contains("checksum mismatch"), "{error}");

        // A layout that no longer holds every executable of the tool.
        let error = check_artifact(
            "charon",
            &entry(format!("{base}/incomplete.tar.gz"), sha256_hex(&incomplete)),
            "linux-x86_64",
        )
        .unwrap_err();
        assert!(error.contains("charon-driver"), "{error}");

        // Entry points that point nowhere.
        let mut moved = entry(format!("{base}/good.tar.gz"), sha256_hex(&good));
        moved.entry_points = Some(std::collections::BTreeMap::from([
            ("charon".to_string(), "charon".to_string()),
            ("charon-driver".to_string(), "charon-driver".to_string()),
        ]));
        let error = check_artifact("charon", &moved, "linux-x86_64").unwrap_err();
        assert!(error.contains("charon"), "{error}");

        // A body that is not the archive its URL claims.
        let body = b"not gzip".to_vec();
        let error = check_artifact(
            "charon",
            &entry(format!("{base}/not-an-archive.tar.gz"), sha256_hex(&body)),
            "linux-x86_64",
        )
        .unwrap_err();
        assert!(error.contains("could not extract"), "{error}");

        // And the existence check: a served path, then a missing one.
        check_published(&format!("{base}/good.tar.gz")).unwrap();
        let error = check_published(&format!("{base}/gone.tar.gz")).unwrap_err();
        assert!(error.contains("404"), "{error}");
    }

    /// `binary_platform` reads the two header layouts it claims to, and
    /// declines anything else rather than guessing.
    #[test]
    fn binary_platform_reads_elf_and_macho_headers() {
        let dir = tempfile::tempdir().unwrap();
        let write = |name: &str, bytes: &[u8]| {
            let path = dir.path().join(name);
            std::fs::write(&path, bytes).unwrap();
            path
        };
        let mut elf = [0u8; 20];
        elf[..4].copy_from_slice(b"\x7FELF");
        elf[5] = 1;

        elf[18] = 0x3E;
        assert_eq!(
            binary_platform(&write("elf-x86_64", &elf))
                .unwrap()
                .unwrap(),
            "linux-x86_64"
        );
        elf[18] = 0xB7;
        assert_eq!(
            binary_platform(&write("elf-aarch64", &elf))
                .unwrap()
                .unwrap(),
            "linux-aarch64"
        );
        // An ELF machine we do not map is unknown, not a mismatch.
        elf[18] = 0x28;
        assert!(binary_platform(&write("elf-arm", &elf)).unwrap().is_none());

        let macho = |cputype: u32| {
            let mut bytes = [0u8; 20];
            bytes[..4].copy_from_slice(&0xFEED_FACFu32.to_le_bytes());
            bytes[4..8].copy_from_slice(&cputype.to_le_bytes());
            bytes
        };
        assert_eq!(
            binary_platform(&write("macho-x86_64", &macho(0x0100_0007)))
                .unwrap()
                .unwrap(),
            "macos-x86_64"
        );
        assert_eq!(
            binary_platform(&write("macho-arm64", &macho(0x0100_000C)))
                .unwrap()
                .unwrap(),
            "macos-aarch64"
        );

        // A script, and a file too short to hold either header.
        assert!(
            binary_platform(&write("script", b"#!/bin/sh\nexec charon \"$@\"\n"))
                .unwrap()
                .is_none()
        );
        assert!(
            binary_platform(&write("tiny", b"\x7FELF"))
                .unwrap()
                .is_none()
        );
    }
}
