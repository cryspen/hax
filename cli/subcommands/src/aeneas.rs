//! Aeneas-Lean backend: runs the charon + aeneas pipeline to translate Rust to Lean.
//! This bypasses the hax frontend exporter and engine entirely.
//!
//! The pipeline is:
//!   1. Run charon on the crate to produce an LLBC file
//!   2. Run aeneas on the LLBC file to produce Lean extraction
//!   3. Optionally generate a lakefile for the Lean project

use hax_types::cli_options::*;
use hax_types::diagnostics::message::HaxMessage;
use std::collections::HashMap;
use std::time::SystemTime;
use std::path::{Path, PathBuf};
use std::{fs, process};

use super::find_binary;

mod lakefile;

const AENEAS_BINARY_NAME: &str = "aeneas";
const AENEAS_BINARY_ENV: &str = "HAX_AENEAS_BINARY";
const CHARON_BINARY_NAME: &str = "charon";
const CHARON_BINARY_ENV: &str = "HAX_CHARON_BINARY";
const BACKEND_DIR: &str = "aeneas-lean";

/// Forward all aeneas output lines.
fn report_output(lines: &[String], message_format: MessageFormat) {
    for line in lines {
        HaxMessage::SubprocessOutput {
            prefix: "aeneas".into(),
            line: line.clone(),
        }
        .report(message_format, None);
    }
}

/// Forward aeneas error output, truncating if longer than 10 lines
/// and writing the full log to a file.
fn report_error_output(lines: &[String], lean_dir: &Path, message_format: MessageFormat) {
    const MAX_LINES: usize = 10;

    report_output(&lines[..lines.len().min(MAX_LINES)], message_format);

    if lines.len() > MAX_LINES {
        let log_path = lean_dir.join("aeneas-error.log");
        let _ = fs::write(&log_path, lines.join("\n"));
        HaxMessage::OutputTruncated {
            prefix: "aeneas".into(),
            remaining: lines.len() - MAX_LINES,
            log_path,
        }
        .report(message_format, None);
    }
}

/// Collect aeneas output lines from stdout and stderr, filtering out
/// progress bar escape sequences from stderr.
fn collect_output_lines(output: &process::Output) -> Vec<String> {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let mut lines: Vec<String> = Vec::new();

    for line in stdout.lines() {
        if !line.is_empty() {
            lines.push(line.to_string());
        }
    }
    for line in stderr.lines() {
        let stripped = line.trim();
        if stripped.is_empty() || stripped.contains("[?25l") || stripped.contains("[?25h") {
            continue;
        }
        lines.push(line.to_string());
    }

    lines
}
/// Runs the charon + aeneas pipeline for the `aeneas-lean` backend.
/// Returns `true` if an error occurred.
pub fn run(
    options: &AeneasLeanOptions,
    output_dir: Option<PathBuf>,
    verbose: u8,
    message_format: MessageFormat,
) -> bool {
    let aeneas = find_binary(AENEAS_BINARY_NAME, AENEAS_BINARY_ENV, message_format);
    let charon = find_binary(CHARON_BINARY_NAME, CHARON_BINARY_ENV, message_format);

    let crate_dir = std::env::current_dir().expect("Could not get current directory");

    let crate_name = cargo_metadata::MetadataCommand::new()
        .current_dir(&crate_dir)
        .exec()
        .ok()
        .and_then(|m| m.root_package().map(|p| p.name.replace('-', "_")))
        .unwrap_or_else(|| "output".to_string());

    // Output directory layout:
    //   <lean_dir>/
    //     extraction/   <- Lean files produced by aeneas
    //     llbc/         <- LLBC file produced by charon
    //     lakefile.toml <- (optional) Lean project file
    //     lean-toolchain
    let lean_dir = output_dir.unwrap_or_else(|| crate_dir.join("proofs").join(BACKEND_DIR));
    let out_dir = lean_dir.join("extraction");
    let llbc_dir = lean_dir.join("llbc");

    fs::create_dir_all(&out_dir).unwrap_or_else(|e| {
        HaxMessage::GenericError {
            message: format!("failed to create output directory: {}", e),
        }
        .report(message_format, None);
    });

    fs::create_dir_all(&llbc_dir).unwrap_or_else(|e| {
        HaxMessage::GenericError {
            message: format!("failed to create llbc directory: {}", e),
        }
        .report(message_format, None);
    });
    let llbc_file = llbc_dir.join(format!("{}.llbc", crate_name));

    // Running charon

    HaxMessage::RunningStep {
        step: "charon".into(),
    }
    .report(message_format, None);

    let charon_status = process::Command::new(&charon)
        .args([
            "cargo",
            "--preset=aeneas",
            "--dest-file",
            llbc_file.to_str().expect("non-UTF8 path"),
        ])
        .current_dir(&crate_dir)
        .stderr(process::Stdio::inherit())
        .status();

    match charon_status {
        Ok(status) if status.success() => {}
        Ok(status) => {
            HaxMessage::GenericError {
                message: format!("charon exited with non-zero code {}", status.code().unwrap_or(-1)),
            }
            .report(message_format, None);
            return true;
        }
        Err(e) => {
            HaxMessage::GenericError {
                message: format!("failed to run charon: {}", e),
            }
            .report(message_format, None);
            return true;
        }
    }

    // Running Aeneas

    // Snapshot modification times of .lean files before aeneas runs
    let mtimes_before: HashMap<PathBuf, SystemTime> = fs::read_dir(&out_dir)
        .into_iter()
        .flatten()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "lean"))
        .filter_map(|e| {
            let path = e.path();
            fs::metadata(&path)
                .and_then(|m| m.modified())
                .ok()
                .map(|mtime| (path, mtime))
        })
        .collect();

    HaxMessage::RunningStep {
        step: format!("aeneas on {}", llbc_file.display()),
    }
    .report(message_format, None);

    let aeneas_output = process::Command::new(&aeneas)
        .args([
            "-backend",
            "lean",
            llbc_file.to_str().expect("non-UTF8 path"),
            "-dest",
            out_dir.to_str().expect("non-UTF8 path"),
        ])
        .current_dir(&crate_dir)
        .output();

    let output = match aeneas_output {
        Ok(output) => output,
        Err(e) => {
            HaxMessage::GenericError {
                message: format!("failed to run aeneas: {}", e),
            }
            .report(message_format, None);
            return true;
        }
    };

    let all_lines = collect_output_lines(&output);

    // Forward aeneas output (always on error, only in verbose mode on success)
    if !output.status.success() {
        report_error_output(&all_lines, &lean_dir, message_format);
    } else if verbose > 0 {
        report_output(&all_lines, message_format);
    }

    // Report results

    // Report .lean files: "wrote" if new or mtime changed, "unchanged" otherwise
    if let Ok(entries) = fs::read_dir(&out_dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().is_none_or(|ext| ext != "lean") {
                continue;
            }
            let new_mtime = fs::metadata(&path).and_then(|m| m.modified()).ok();
            let wrote = match (mtimes_before.get(&path), new_mtime) {
                (Some(old), Some(new)) => *old != new,
                (None, Some(_)) => true,
                _ => continue,
            };
            HaxMessage::ProducedFile {
                path: path.clone(),
                wrote,
            }
            .report(message_format, None);
        }
    }

    // Generate lakefile if requested
    if options.lakefile {
        lakefile::generate(&lean_dir, &crate_name, message_format);
    }

    if !output.status.success() {
        HaxMessage::GenericError {
            message: format!("aeneas exited with non-zero code {}", output.status.code().unwrap_or(-1)),
        }
        .report(message_format, None);
        return true;
    }

    false
}
