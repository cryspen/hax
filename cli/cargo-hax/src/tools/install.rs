//! The download-verify-extract-install pipeline.
//!
//! An install is atomic, with a directory rename as the single commit
//! point: download, checksum verification, extraction, and the write of
//! `hax-metadata.toml` all happen in a temporary directory next to the
//! final location. A version directory therefore either does not exist or
//! is complete. The rename also defines behaviour under concurrency:
//! whichever of two racing installs renames second finds the path
//! occupied, discards its copy, and treats the install as a success.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::Path;
use std::sync::{Arc, OnceLock};

use hax_types::cli_options::MessageFormat;
use hax_types::diagnostics::message::HaxMessage;
use sha2::Digest;

use super::cache;
use super::manifest::{manifest, platform_key, validate_entry_point, validate_version_id};

/// How an [`ensure_installed`] call concluded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Installed {
    /// The version was already in the cache (possibly installed
    /// concurrently by another process while we worked). `verified`
    /// records whether that cached copy was checksum-verified at install
    /// time.
    AlreadyCached { verified: bool },
    /// Freshly downloaded and installed. `verified` is false for a
    /// fallback install.
    Fresh { verified: bool },
}

/// Whether an already-cached version recorded a verified checksum in its
/// metadata. A missing or unreadable flag counts as unverified.
fn cached_verified(dir: &Path) -> bool {
    cache::read_metadata(dir)
        .ok()
        .flatten()
        .and_then(|metadata| metadata.checksum_verified)
        .unwrap_or(false)
}

/// What to download and whether it can be verified.
struct Artifact {
    url: String,
    sha256: Option<String>,
    entry_points: Option<BTreeMap<String, String>>,
}

/// Make sure `tool@version` is present in the cache, downloading it if
/// necessary. Returns how the install concluded; the version directory is
/// `cache::version_dir(tool, version)`.
///
/// With `force`, a cached version is re-downloaded and re-verified rather
/// than reused. This is the way to obtain a verified copy of a version
/// first installed through the unverified fallback path: an older cache
/// entry cannot be checked in place, since the checksum is over the
/// archive and the cache holds only the extracted files.
pub fn ensure_installed(
    tool: &str,
    version: &str,
    force: bool,
    message_format: MessageFormat,
) -> Result<Installed, String> {
    validate_version_id(version)?;
    let final_dir = cache::version_dir(tool, version)?;
    if final_dir.is_dir() && !force {
        return Ok(Installed::AlreadyCached {
            verified: cached_verified(&final_dir),
        });
    }

    let platform = platform_key();
    let artifact = match manifest().lookup(tool, version, &platform) {
        Some(entry) => Artifact {
            url: entry.url.clone(),
            sha256: Some(entry.sha256.clone()),
            entry_points: entry.entry_points.clone(),
        },
        None => {
            let (url, entry_points) = manifest()
                .fallback_for(tool, version, &platform)
                .ok_or_else(|| {
                    format!(
                        "no artifact of {tool} {version} is available for platform \
                         {platform} (pre-built artifacts exist for {}); set a \
                         `path` entry in hax.toml to use a binary you provide",
                        super::manifest::SUPPORTED_PLATFORMS.join(", "),
                    )
                })?;
            HaxMessage::UnverifiedInstall {
                tool: tool.to_string(),
                version: version.to_string(),
                url: url.clone(),
            }
            .report(message_format, None);
            Artifact {
                url,
                sha256: None,
                entry_points,
            }
        }
    };

    // Work in a temporary directory next to the final location, so the
    // commit rename stays on one filesystem.
    let tool_dir = final_dir
        .parent()
        .expect("a version directory always has a tool directory as parent");
    std::fs::create_dir_all(tool_dir)
        .map_err(|e| format!("could not create {}: {e}", tool_dir.display()))?;
    let staging = tempfile::Builder::new()
        .prefix(".install-")
        .tempdir_in(tool_dir)
        .map_err(|e| {
            format!(
                "could not create a temporary directory in {}: {e}",
                tool_dir.display()
            )
        })?;

    let archive = download(&artifact.url, staging.path())?;
    if let Some(expected) = &artifact.sha256 {
        verify_sha256(&archive, expected, &artifact.url)?;
    }
    let contents = staging.path().join("contents");
    extract(&archive, &artifact.url, &contents)?;

    // Validate the entry points and check every executable of the tool is
    // reachable; a stale fallback template surfaces here.
    for (name, path) in artifact.entry_points.iter().flatten() {
        let relative = validate_entry_point(path)?;
        if !contents.join(&relative).is_file() {
            return Err(format!(
                "no executable `{name}` at `{path}` inside the archive from {}; \
                 the archive layout may have changed",
                artifact.url
            ));
        }
    }
    cache::write_metadata(
        &contents,
        &cache::InstallMetadata {
            entry_points: artifact.entry_points.clone(),
            source_url: Some(artifact.url.clone()),
            checksum_verified: Some(artifact.sha256.is_some()),
        },
    )?;
    for executable in super::tool_executables(tool) {
        cache::executable_path(&contents, executable)?;
    }

    let verified = artifact.sha256.is_some();

    // A forced reinstall replaces an existing entry: move the old one
    // aside within the staging dir (same filesystem, cleaned up on drop)
    // so a failed swap leaves the previous install recoverable.
    if final_dir.is_dir() {
        let replaced = staging.path().join("replaced");
        std::fs::rename(&final_dir, &replaced).map_err(|e| {
            format!(
                "could not move aside the existing {}: {e}",
                final_dir.display()
            )
        })?;
        if let Err(e) = std::fs::rename(&contents, &final_dir) {
            let _ = std::fs::rename(&replaced, &final_dir);
            return Err(format!(
                "could not move the installed files to {}: {e}",
                final_dir.display()
            ));
        }
        return Ok(Installed::Fresh { verified });
    }

    match std::fs::rename(&contents, &final_dir) {
        Ok(()) => Ok(Installed::Fresh { verified }),
        // A concurrent install won the race: both copies came from the
        // same artifact, so losing it is a success.
        Err(_) if final_dir.is_dir() => Ok(Installed::AlreadyCached {
            verified: cached_verified(&final_dir),
        }),
        Err(e) => Err(format!(
            "could not move the installed files to {}: {e}",
            final_dir.display()
        )),
    }
}

/// Internal override for tests: the per-read download timeout, in seconds.
/// Not part of the user-facing interface; lets a test drive the timeout on
/// a deliberately stalled server without waiting the production default.
const READ_TIMEOUT_OVERRIDE_ENV: &str = "HAX_TOOLS_READ_TIMEOUT_SECS";

/// The per-read timeout for downloads: five minutes, overridable for tests.
fn read_timeout() -> std::time::Duration {
    std::env::var(READ_TIMEOUT_OVERRIDE_ENV)
        .ok()
        .and_then(|value| value.parse().ok())
        .map(std::time::Duration::from_secs)
        .unwrap_or(std::time::Duration::from_secs(300))
}

/// The roots the downloader accepts: the ones bundled with this binary
/// *and* the platform's own store. The bundled roots keep downloads working
/// on an image with no system trust store; the platform's are what an
/// environment terminating TLS with an internal CA installs (including
/// through `SSL_CERT_FILE`/`SSL_CERT_DIR`). An unreadable store is not
/// fatal, as the bundled roots remain.
fn tls_config() -> Arc<rustls::ClientConfig> {
    static CONFIG: OnceLock<Arc<rustls::ClientConfig>> = OnceLock::new();
    CONFIG
        .get_or_init(|| {
            let mut roots = rustls::RootCertStore {
                roots: webpki_roots::TLS_SERVER_ROOTS.to_vec(),
            };
            roots.add_parsable_certificates(rustls_native_certs::load_native_certs().certs);
            // `ureq` links rustls with the *ring* provider, so name it
            // rather than rely on a process-wide default being set.
            Arc::new(
                rustls::ClientConfig::builder_with_provider(
                    rustls::crypto::ring::default_provider().into(),
                )
                .with_safe_default_protocol_versions()
                .expect("the ring provider supports the default protocol versions")
                .with_root_certificates(roots)
                .with_no_client_auth(),
            )
        })
        .clone()
}

/// The host part of a URL, without userinfo or port.
fn host_of(url: &str) -> Option<&str> {
    let rest = url.split_once("://").map_or(url, |(_, rest)| rest);
    let authority = rest.split(['/', '?', '#']).next()?;
    let authority = authority
        .rsplit_once('@')
        .map_or(authority, |(_, host)| host);
    let host = match authority.strip_prefix('[') {
        // An IPv6 literal is bracketed, and any port follows the brackets.
        Some(rest) => rest.split_once(']').map(|(host, _)| host)?,
        None => authority
            .split_once(':')
            .map_or(authority, |(host, _)| host),
    };
    (!host.is_empty()).then_some(host)
}

/// Whether `host` is exempt from the proxy: loopback, which no proxy is
/// expected to reach, or an entry of `no_proxy` (the environment variable's
/// comma-separated list). An entry matches the host and its subdomains; `*`
/// matches everything.
fn host_bypasses_proxy(host: &str, no_proxy: &str) -> bool {
    let loopback = matches!(host, "localhost" | "::1")
        || host.ends_with(".localhost")
        || host.starts_with("127.");
    loopback
        || no_proxy
            .split(',')
            .map(|entry| entry.trim().trim_start_matches('.'))
            .filter(|entry| !entry.is_empty())
            .any(|entry| {
                entry == "*"
                    || host == entry
                    || host
                        .strip_suffix(entry)
                        .is_some_and(|prefix| prefix.ends_with('.'))
            })
}

/// The client every request for `url` goes through.
///
/// Both connecting and each read are bounded, so a stalled or throttled
/// mirror fails the install instead of hanging the build (and CI)
/// indefinitely; the read timeout resets per read, so it does not cap a
/// large-but-progressing download.
///
/// `ureq` reads neither the proxy variables nor the platform's trust store
/// on its own, so an install would fail where `curl` succeeds. `NO_PROXY` is
/// applied here as well, `ureq` 2 not implementing it at all.
fn agent(url: &str, read_timeout: std::time::Duration) -> ureq::Agent {
    let no_proxy = ["NO_PROXY", "no_proxy"]
        .iter()
        .find_map(|name| std::env::var(name).ok())
        .unwrap_or_default();
    let proxied = !host_of(url).is_some_and(|host| host_bypasses_proxy(host, &no_proxy));
    ureq::AgentBuilder::new()
        .timeout_connect(std::time::Duration::from_secs(30))
        .timeout_read(read_timeout)
        .tls_config(tls_config())
        .try_proxy_from_env(proxied)
        .build()
}

/// Download a URL into `dir`, returning the file path.
fn download(url: &str, dir: &Path) -> Result<std::path::PathBuf, String> {
    let agent = agent(url, read_timeout());
    let response = agent.get(url).call().map_err(|e| match e {
        ureq::Error::Status(code, _) => {
            format!("download failed with HTTP status {code} for {url}")
        }
        e => format!("download failed for {url}: {e}"),
    })?;
    let path = dir.join("artifact");
    let mut file = std::fs::File::create(&path)
        .map_err(|e| format!("could not create {}: {e}", path.display()))?;
    std::io::copy(&mut response.into_reader(), &mut file)
        .map_err(|e| format!("download of {url} was interrupted: {e}"))?;
    Ok(path)
}

fn verify_sha256(file: &Path, expected: &str, url: &str) -> Result<(), String> {
    let mut hasher = sha2::Sha256::new();
    let mut reader = std::fs::File::open(file)
        .map_err(|e| format!("could not read back {}: {e}", file.display()))?;
    std::io::copy(&mut reader, &mut hasher).map_err(|e| e.to_string())?;
    let actual = hex::encode(hasher.finalize());
    if actual == expected.to_lowercase() {
        Ok(())
    } else {
        Err(format!(
            "checksum mismatch for {url}:\n  expected sha256 {expected}\n  \
             got             {actual}\nthe download was discarded"
        ))
    }
}

/// Extract a tar archive (gzip or zstd, by URL extension) into `dest`.
fn extract(archive: &Path, url: &str, dest: &Path) -> Result<(), String> {
    let file = std::fs::File::open(archive).map_err(|e| e.to_string())?;
    let reader: Box<dyn Read> = if url.ends_with(".tar.gz") || url.ends_with(".tgz") {
        Box::new(flate2::read::GzDecoder::new(file))
    } else if url.ends_with(".tar.zst") {
        Box::new(zstd::stream::read::Decoder::new(file).map_err(|e| e.to_string())?)
    } else {
        return Err(format!(
            "unsupported archive format for {url}: expected .tar.gz, .tgz or .tar.zst"
        ));
    };
    std::fs::create_dir_all(dest).map_err(|e| e.to_string())?;
    tar::Archive::new(reader)
        .unpack(dest)
        .map_err(|e| format!("could not extract the archive from {url}: {e}"))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_host_is_read_out_of_every_url_shape() {
        for (url, host) in [
            ("https://github.com/o/r/releases/x.tar.gz", "github.com"),
            ("https://github.com:443/o/r", "github.com"),
            ("https://user:pw@mirror.example:8080/x", "mirror.example"),
            ("http://127.0.0.1:45241/good.tar.gz", "127.0.0.1"),
            ("https://[::1]:8080/x", "::1"),
            ("https://github.com", "github.com"),
        ] {
            assert_eq!(host_of(url), Some(host), "{url}");
        }
    }

    #[test]
    fn loopback_and_no_proxy_entries_bypass_the_proxy() {
        // Loopback is exempt whatever `NO_PROXY` says: an internal mirror or
        // a test server is what sits there.
        for host in [
            "localhost",
            "app.localhost",
            "127.0.0.1",
            "127.1.2.3",
            "::1",
        ] {
            assert!(host_bypasses_proxy(host, ""), "{host}");
        }
        // An entry matches the host and its subdomains, with or without a
        // leading dot, and `*` exempts everything.
        assert!(host_bypasses_proxy("mirror.corp", "mirror.corp"));
        assert!(host_bypasses_proxy("dl.mirror.corp", ".mirror.corp"));
        assert!(host_bypasses_proxy(
            "dl.mirror.corp",
            "example.com, mirror.corp"
        ));
        assert!(host_bypasses_proxy("github.com", "*"));
        // Everything else is proxied, including a suffix that is not a
        // domain boundary.
        assert!(!host_bypasses_proxy("github.com", ""));
        assert!(!host_bypasses_proxy("github.com", "mirror.corp"));
        assert!(!host_bypasses_proxy("notmirror.corp", "mirror.corp"));
    }
}
