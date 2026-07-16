//! The machine-wide tool cache.
//!
//! Installed tool versions live under `$XDG_CACHE_HOME/hax/tools/<tool>/
//! <version>/` (defaulting to `~/.cache/hax/`, uniformly across
//! platforms). A version directory is self-contained: it either does not
//! exist or is complete, and carries a `hax-metadata.toml` recording its
//! entry points and provenance, so using a cached version never consults
//! the manifest. The cache is disposable; deleting any part of it is safe.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use super::manifest::validate_entry_point;

/// The per-installation metadata file, written next to the extracted
/// archive contents. The `hax-` prefix avoids colliding with them.
pub const METADATA_FILE: &str = "hax-metadata.toml";

/// Contents of a version directory's `hax-metadata.toml`. Unknown fields
/// are ignored, leaving room for future per-installation information.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct InstallMetadata {
    /// Executable name to path relative to the version directory. Absent
    /// for archives following the `bin/<name>` convention.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub entry_points: Option<BTreeMap<String, String>>,
    /// Where the artifact was downloaded from.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_url: Option<String>,
    /// Whether the download's SHA-256 was verified against the manifest.
    /// `false` marks a fallback install.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub checksum_verified: Option<bool>,
}

/// The cache root: `$XDG_CACHE_HOME/hax`, else `~/.cache/hax`. The XDG
/// layout is used on every platform, as documented.
pub fn cache_root() -> Result<PathBuf, String> {
    if let Ok(dir) = std::env::var("XDG_CACHE_HOME")
        && !dir.is_empty()
    {
        return Ok(PathBuf::from(dir).join("hax"));
    }
    match std::env::var("HOME") {
        Ok(home) if !home.is_empty() => Ok(PathBuf::from(home).join(".cache").join("hax")),
        _ => Err("cannot locate the hax cache: neither XDG_CACHE_HOME nor HOME is set".into()),
    }
}

/// The directory holding all versions of one tool.
pub fn tool_dir(tool: &str) -> Result<PathBuf, String> {
    Ok(cache_root()?.join("tools").join(tool))
}

/// The directory of one installed tool version.
pub fn version_dir(tool: &str, version: &str) -> Result<PathBuf, String> {
    super::manifest::validate_version_id(version)?;
    Ok(tool_dir(tool)?.join(version))
}

/// The versions of a tool present in the cache, sorted.
pub fn installed_versions(tool: &str) -> Vec<String> {
    let Ok(dir) = tool_dir(tool) else {
        return Vec::new();
    };
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut versions: Vec<String> = entries
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let name = entry.file_name().into_string().ok()?;
            // Skip in-progress temporary install directories and strays.
            (entry.file_type().ok()?.is_dir() && !name.starts_with('.')).then_some(name)
        })
        .collect();
    versions.sort();
    versions
}

/// Read a version directory's metadata. A missing file is `None` (the
/// `bin/` convention applies); an unreadable one is an error, since the
/// executables' locations may depend on it.
pub fn read_metadata(dir: &Path) -> Result<Option<InstallMetadata>, String> {
    let path = dir.join(METADATA_FILE);
    let contents = match std::fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("could not read {}: {e}", path.display())),
    };
    toml::from_str(&contents)
        .map(Some)
        .map_err(|e| format!("invalid {}: {e}", path.display()))
}

pub fn write_metadata(dir: &Path, metadata: &InstallMetadata) -> Result<(), String> {
    let path = dir.join(METADATA_FILE);
    let contents = toml::to_string_pretty(metadata)
        .map_err(|e| format!("could not serialize install metadata: {e}"))?;
    std::fs::write(&path, contents).map_err(|e| format!("could not write {}: {e}", path.display()))
}

/// Locate an executable inside an installed version directory: its
/// metadata `entry_points` if present, the `bin/<name>` convention
/// otherwise. The executable must exist.
pub fn executable_path(dir: &Path, executable: &str) -> Result<PathBuf, String> {
    let relative = match read_metadata(dir)? {
        Some(InstallMetadata {
            entry_points: Some(entry_points),
            ..
        }) if entry_points.contains_key(executable) => {
            validate_entry_point(&entry_points[executable])?
        }
        _ => Path::new("bin").join(executable),
    };
    let path = dir.join(relative);
    if path.is_file() {
        Ok(path)
    } else {
        Err(format!(
            "executable `{executable}` not found in {}: tried {}",
            dir.display(),
            path.display()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metadata_round_trips() {
        let dir = tempfile::tempdir().unwrap();
        let metadata = InstallMetadata {
            entry_points: Some(BTreeMap::from([("charon".into(), "charon".into())])),
            source_url: Some("https://example.com/a.tar.gz".into()),
            checksum_verified: Some(false),
        };
        write_metadata(dir.path(), &metadata).unwrap();
        let read = read_metadata(dir.path()).unwrap().unwrap();
        assert_eq!(read.entry_points, metadata.entry_points);
        assert_eq!(read.source_url, metadata.source_url);
        assert_eq!(read.checksum_verified, Some(false));
    }

    #[test]
    fn missing_metadata_is_none_and_unknown_fields_are_ignored() {
        let dir = tempfile::tempdir().unwrap();
        assert!(read_metadata(dir.path()).unwrap().is_none());
        std::fs::write(
            dir.path().join(METADATA_FILE),
            "future_field = 1\n[entry_points]\ncharon = \"charon\"\n",
        )
        .unwrap();
        let metadata = read_metadata(dir.path()).unwrap().unwrap();
        assert_eq!(metadata.entry_points.unwrap()["charon"], "charon");
    }

    #[test]
    fn executable_path_prefers_entry_points_and_falls_back_to_bin() {
        let dir = tempfile::tempdir().unwrap();
        // bin/ convention.
        std::fs::create_dir(dir.path().join("bin")).unwrap();
        std::fs::write(dir.path().join("bin/aeneas"), "").unwrap();
        assert_eq!(
            executable_path(dir.path(), "aeneas").unwrap(),
            dir.path().join("bin/aeneas")
        );
        // entry_points override.
        std::fs::write(dir.path().join("charon"), "").unwrap();
        write_metadata(
            dir.path(),
            &InstallMetadata {
                entry_points: Some(BTreeMap::from([("charon".into(), "charon".into())])),
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            executable_path(dir.path(), "charon").unwrap(),
            dir.path().join("charon")
        );
        // Missing executables are an error naming the tried path.
        let err = executable_path(dir.path(), "missing").unwrap_err();
        assert!(err.contains("bin/missing"), "{err}");
    }

    #[test]
    fn escaping_entry_points_in_metadata_are_rejected() {
        let dir = tempfile::tempdir().unwrap();
        write_metadata(
            dir.path(),
            &InstallMetadata {
                entry_points: Some(BTreeMap::from([("x".into(), "../../etc/passwd".into())])),
                ..Default::default()
            },
        )
        .unwrap();
        assert!(executable_path(dir.path(), "x").is_err());
    }
}
