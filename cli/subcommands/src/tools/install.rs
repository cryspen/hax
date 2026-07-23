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
use std::time::Duration;

use is_terminal::IsTerminal;

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
                         {platform}; set {} or a `path` entry in hax.toml \
                         to use a binary you provide",
                        super::resolve::env_var_for(tool),
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

    // Announce the download only after resolving the artifact, so any
    // unverified-fallback warning above explains this line rather than
    // following it.
    HaxMessage::Step {
        verb: "Downloading".to_string(),
        target: format!("{tool} {version}"),
    }
    .report(message_format, None);

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

    let archive = download(&artifact.url, staging.path(), message_format)?;
    if let Some(expected) = &artifact.sha256 {
        HaxMessage::Step {
            verb: "Verifying".to_string(),
            target: format!("{tool} {version}"),
        }
        .report(message_format, None);
        verify_sha256(&archive, expected, &artifact.url)?;
    }
    HaxMessage::Step {
        verb: "Extracting".to_string(),
        target: format!("{tool} {version}"),
    }
    .report(message_format, None);
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
fn read_timeout() -> Duration {
    std::env::var(READ_TIMEOUT_OVERRIDE_ENV)
        .ok()
        .and_then(|value| value.parse().ok())
        .map(Duration::from_secs)
        .unwrap_or(Duration::from_secs(300))
}

/// Download a URL into `dir`, returning the file path. Shows a progress bar
/// on an interactive terminal (skipped under `--message-format json` and in
/// non-terminal output such as CI logs).
fn download(
    url: &str,
    dir: &Path,
    message_format: MessageFormat,
) -> Result<std::path::PathBuf, String> {
    // Bound both connecting and each read, so a stalled or throttled
    // mirror fails the install instead of hanging the build (and CI)
    // indefinitely. `timeout_read` resets per read, so it does not cap a
    // large-but-progressing download.
    let agent = ureq::AgentBuilder::new()
        .timeout_connect(Duration::from_secs(30))
        .timeout_read(read_timeout())
        .build();
    let response = agent.get(url).call().map_err(|e| match e {
        ureq::Error::Status(code, _) => {
            format!("download failed with HTTP status {code} for {url}")
        }
        e => format!("download failed for {url}: {e}"),
    })?;
    let total: Option<u64> = response
        .header("Content-Length")
        .and_then(|value| value.parse().ok());
    let path = dir.join("artifact");
    let mut file = std::fs::File::create(&path)
        .map_err(|e| format!("could not create {}: {e}", path.display()))?;

    let progress = (matches!(message_format, MessageFormat::Human)
        && std::io::stderr().is_terminal())
    .then(|| progress_bar(total));

    let mut reader = response.into_reader();
    let result = match &progress {
        Some(bar) => std::io::copy(&mut bar.wrap_read(&mut reader), &mut file),
        None => std::io::copy(&mut reader, &mut file),
    };
    if let Some(bar) = &progress {
        bar.finish_and_clear();
    }
    result.map_err(|e| format!("download of {url} was interrupted: {e}"))?;
    Ok(path)
}

/// A progress bar for a download of `total` bytes (a spinner when the size
/// is unknown). Draws to stderr.
fn progress_bar(total: Option<u64>) -> indicatif::ProgressBar {
    use indicatif::{ProgressBar, ProgressStyle};
    match total {
        Some(len) => {
            let bar = ProgressBar::new(len);
            bar.set_style(
                ProgressStyle::with_template(
                    "  {bar:30} {percent:>3}%  {bytes}/{total_bytes}  {bytes_per_sec}",
                )
                .expect("valid template")
                .progress_chars("█▉▊▋▌▍▎▏ "),
            );
            bar
        }
        None => {
            let bar = ProgressBar::new_spinner();
            bar.set_style(
                ProgressStyle::with_template("  {spinner} {bytes} ({bytes_per_sec})")
                    .expect("valid template"),
            );
            bar.enable_steady_tick(Duration::from_millis(100));
            bar
        }
    }
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

    // The progress-bar templates are only rendered on a terminal, so they
    // are never exercised by the integration tests; build both here to catch
    // an invalid template (which would otherwise panic at download time).
    #[test]
    fn progress_bar_templates_are_valid() {
        let _ = progress_bar(Some(1024));
        let _ = progress_bar(None);
    }
}
