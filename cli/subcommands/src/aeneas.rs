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
use std::path::{Path, PathBuf};
use std::time::SystemTime;
use std::{fs, process};

use super::find_binary;

mod lakefile;

const AENEAS_BINARY_NAME: &str = "aeneas";
const AENEAS_BINARY_ENV: &str = "HAX_AENEAS_BINARY";
const CHARON_BINARY_NAME: &str = "charon";
const CHARON_BINARY_ENV: &str = "HAX_CHARON_BINARY";
const BACKEND_DIR: &str = "aeneas-lean";

const EXPECTED_AENEAS_VERSION: &str = env!("HAX_EXPECTED_AENEAS_VERSION");
const EXPECTED_CHARON_VERSION: &str = env!("HAX_EXPECTED_CHARON_VERSION");

/// Check that a binary reports the expected version, warn if not.
fn check_version(binary: &Path, expected: &str, message_format: MessageFormat) {
    if expected.is_empty() {
        return;
    }

    let is_aeneas = binary.file_name().is_some_and(|n| n == "aeneas");
    let args: &[&str] = if is_aeneas { &["-version"] } else { &["version"] };

    let output = match process::Command::new(binary).args(args).output() {
        Ok(o) => String::from_utf8_lossy(&o.stdout).to_string(),
        Err(_) => return,
    };
    let first_line = output.lines().next().unwrap_or("");

    // `aeneas -version` outputs "aeneas <sha>"; compare SHA prefixes.
    // `charon version` outputs a semver like "0.1.174"; compare exactly.
    let actual = if is_aeneas {
        first_line
            .split_whitespace()
            .nth(1)
            .unwrap_or("")
            .get(..expected.len())
            .unwrap_or("")
    } else {
        first_line.trim()
    };

    if actual != expected {
        let name = binary.file_name().unwrap_or_default().to_string_lossy();
        HaxMessage::GenericWarning {
            message: format!(
                "{name} version mismatch: expected {expected}, found {actual}. \
                 Run ./install-aeneas.sh to get the pinned version."
            ),
        }
        .report(message_format, None);
    }
}

/// Convert a snake_case crate name to CamelCase for Lean.
pub fn to_camel_case(name: &str) -> String {
    name.split('_')
        .map(|s| {
            let mut c = s.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().to_string() + c.as_str(),
            }
        })
        .collect()
}

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
/// unless verbose mode is on. Always writes the full log to a file.
fn report_error_output(
    lines: &[String],
    lean_dir: &Path,
    verbose: u8,
    message_format: MessageFormat,
) {
    const MAX_LINES: usize = 10;

    let show = if verbose > 0 {
        lines.len()
    } else {
        lines.len().min(MAX_LINES)
    };
    report_output(&lines[..show], message_format);

    if lines.len() > MAX_LINES {
        let log_path = lean_dir.join("aeneas-error.log");
        let _ = fs::write(&log_path, lines.join("\n"));
        if verbose == 0 {
            HaxMessage::OutputTruncated {
                prefix: "aeneas".into(),
                remaining: lines.len() - MAX_LINES,
                log_path,
            }
            .report(message_format, None);
        }
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
    const INSTALL_HINT: &str = "Install with: ./install-aeneas.sh (or ./setup.sh --aeneas)";
    let aeneas = find_binary(
        AENEAS_BINARY_NAME,
        AENEAS_BINARY_ENV,
        message_format,
        Some(INSTALL_HINT),
    );
    let charon = find_binary(
        CHARON_BINARY_NAME,
        CHARON_BINARY_ENV,
        message_format,
        Some(INSTALL_HINT),
    );

    check_version(&aeneas, EXPECTED_AENEAS_VERSION, message_format);
    check_version(&charon, EXPECTED_CHARON_VERSION, message_format);

    let metadata = cargo_metadata::MetadataCommand::new()
        .exec()
        .expect("Could not read cargo metadata");
    let crate_dir = metadata
        .root_package()
        .map(|p| {
            PathBuf::from(&p.manifest_path)
                .parent()
                .unwrap()
                .to_path_buf()
        })
        .unwrap_or_else(|| std::env::current_dir().expect("Could not get current directory"));
    let crate_name = metadata
        .root_package()
        .map(|p| p.name.replace('-', "_"))
        .unwrap_or_else(|| "output".to_string());

    // Convert crate name to PascalCase for the Lean package/directory name.
    let pkg_name = to_camel_case(&crate_name);

    // Output directory layout:
    //   <lean_dir>/
    //     <PkgName>/Extraction/   <- Lean files produced by aeneas
    //     llbc/                   <- LLBC file produced by charon
    //     lakefile.toml           <- (optional) Lean project file
    //     lean-toolchain
    let lean_dir = output_dir.unwrap_or_else(|| crate_dir.join("proofs").join(BACKEND_DIR));
    let out_dir = lean_dir.join(&pkg_name).join("Extraction");
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

    let mut charon_cmd = process::Command::new(&charon);
    charon_cmd.args([
        "cargo",
        "--preset=aeneas",
        "--dest-file",
        llbc_file.to_str().expect("non-UTF8 path"),
    ]);
    if let Some(extra) = &options.charon_args {
        charon_cmd.args(extra.split_whitespace());
    }
    let charon_status = charon_cmd
        .current_dir(&crate_dir)
        .stderr(process::Stdio::inherit())
        .status();

    match charon_status {
        Ok(status) if status.success() => {}
        Ok(status) => {
            HaxMessage::GenericError {
                message: format!(
                    "charon exited with non-zero code {}",
                    status.code().unwrap_or(-1)
                ),
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

    let mut aeneas_cmd = process::Command::new(&aeneas);
    aeneas_cmd.args([
        "-backend",
        "lean",
        llbc_file.to_str().expect("non-UTF8 path"),
        "-dest",
        out_dir.to_str().expect("non-UTF8 path"),
    ]);
    if let Some(extra) = &options.aeneas_args {
        aeneas_cmd.args(extra.split_whitespace());
    }
    let aeneas_output = aeneas_cmd.current_dir(&crate_dir).output();

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
        report_error_output(&all_lines, &lean_dir, verbose, message_format);
    } else if verbose > 0 {
        report_output(&all_lines, message_format);
    }

    // Rename the main output file from <PkgName>.lean to Funs.lean
    let aeneas_main_file = out_dir.join(format!("{}.lean", pkg_name));
    let funs_file = out_dir.join("Funs.lean");
    if aeneas_main_file.exists() {
        let _ = fs::rename(&aeneas_main_file, &funs_file);
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
            message: format!(
                "aeneas exited with non-zero code {}",
                output.status.code().unwrap_or(-1)
            ),
        }
        .report(message_format, None);
        return true;
    }

    false
}
