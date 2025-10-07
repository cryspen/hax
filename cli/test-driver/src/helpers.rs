//! Helper functions that implement small bits of logic used across modules.

use anyhow::{Context, Result, anyhow};
use hax_frontend_exporter::{DefId, DefPathItem, DisambiguatedDefPathItem};
use hax_types::cli_options::BackendName;
use serde::{Serialize, de::DeserializeOwned};
use std::{fs, path::Path, process::Stdio};
use tokio::{io::AsyncWriteExt, process::Command};
use walkdir::WalkDir;

use crate::log::{BackendJobKind, JobKind};

/// Returns `true` if `child` is defined within the item `parent`.
pub fn def_id_under(parent: &DefId, child: &DefId) -> bool {
    let parent_path = &parent.path;
    let child_path = &child.path;

    if parent_path.len() > child_path.len() {
        return false;
    }

    parent_path
        .iter()
        .enumerate()
        .all(|(i, chunk)| &child_path[i] == chunk)
}

/// Converts a [`DefId`] into a human readable string.
pub fn string_of_def_id(def_id: &DefId) -> String {
    def_id
        .path
        .iter()
        .map(|path| match &path.data {
            DefPathItem::Impl => "impl",
            DefPathItem::TypeNs(s)
            | DefPathItem::ValueNs(s)
            | DefPathItem::MacroNs(s)
            | DefPathItem::LifetimeNs(s) => s.as_str(),
            DefPathItem::Closure => "|_|",
            _ => "_",
        })
        .collect::<Vec<_>>()
        .join("::")
}

/// Returns the module name encoded in the first component of the [`DefId`].
pub fn module_name(def_id: &DefId) -> Option<String> {
    match def_id.path.first() {
        Some(DisambiguatedDefPathItem {
            data: DefPathItem::TypeNs(module_name),
            disambiguator: 0,
        }) => Some(module_name.clone()),
        _ => None,
    }
}

#[extension_traits::extension(pub trait BackendNameExt)]
impl BackendName {
    /// Convenience helper that wires a backend to a job kind.
    fn job_kind(self, kind: BackendJobKind) -> JobKind {
        JobKind::BackendJob {
            kind,
            backend: self,
        }
    }
}

pub fn copy_dir_recursive(src: &Path, dst: &Path) -> std::io::Result<()> {
    for entry in WalkDir::new(src) {
        let entry = entry?;
        let rel_path = entry.path().strip_prefix(src).unwrap();
        let dest_path = dst.join(rel_path);

        if entry.file_type().is_dir() {
            fs::create_dir_all(&dest_path)?;
        } else {
            fs::copy(entry.path(), &dest_path)?;
        }
    }
    Ok(())
}

/// Runs a command, writes JSON input to its stdin, captures stdout, and parses it as JSON output.
pub async fn run_json_command<I, O>(
    job: Option<&JobKind>,
    program: &Path,
    args: &[&str],
    workdir: &Path,
    input: &I,
) -> Result<O>
where
    I: Serialize + ?Sized,
    O: DeserializeOwned,
{
    // Spawn the child process
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .current_dir(workdir)
        .spawn()
        .with_context(|| format!("failed to spawn process: {}", program.display()))?;

    // Write JSON input to stdin
    if let Some(mut stdin) = child.stdin.take() {
        let json = serde_json::to_vec(input).context("failed to serialize input as JSON")?;
        stdin
            .write_all(&json)
            .await
            .context("failed to write to stdin")?;
        stdin.shutdown().await.context("failed to shutdown stdin")?;
    } else {
        return Err(anyhow!("stdin was not piped"));
    }

    let output = child
        .wait_with_output()
        .await
        .context("failed to wait for process")?;

    let stderr = String::from_utf8_lossy(&output.stderr);
    if let Some(job) = job {
        let stdout = String::from_utf8_lossy(&output.stdout);
        job.report(crate::log::ReportMessage::Stderr(stderr.to_string()));
        job.report(crate::log::ReportMessage::Stdout(stdout.to_string()));
    }

    // Wait for process and collect output
    if !output.status.success() {
        return Err(anyhow!(
            "process exited with non-zero status {}: {}",
            output.status.code().unwrap_or(-1),
            stderr
        ));
    }

    // Parse stdout JSON to output type
    let parsed = serde_json::from_slice::<O>(&output.stdout)
        .with_context(|| format!("failed to parse stdout JSON. Stderr: {}", stderr))?;

    Ok(parsed)
}
