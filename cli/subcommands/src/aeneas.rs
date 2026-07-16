//! Lean backend: runs the charon + aeneas pipeline to translate Rust to Lean.
//! This bypasses the hax frontend exporter and engine entirely.
//!
//! The pipeline is:
//!   1. Run charon on the crate to produce an LLBC file
//!   2. Run aeneas (`-split-files -specs hax -subdir <PkgName>/Extraction`) on
//!      the LLBC file to produce the Lean extraction under `<PkgName>/Extraction/`
//!   3. Optionally generate a lakefile for the Lean project

use hax_types::cli_options::*;
use hax_types::diagnostics::message::HaxMessage;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::SystemTime;
use std::{fs, process};

use super::tools;

mod lakefile;

const BACKEND_DIR: &str = "lean";

// Flags that should trigger a warning when passed to charon/aeneas
const CHARON_WARN_FLAGS: &[&str] = &["--dest-file"];
const AENEAS_WARN_FLAGS: &[&str] = &["-backend", "-dest", "-subdir", "-split-files"];

/// Shell-split a user-supplied extra-args string, reporting a fatal error on
/// unmatched quotes. Returns an empty vector if `s` is `None`.
fn shell_split(s: Option<&str>, who: &str, message_format: MessageFormat) -> Vec<String> {
    let Some(s) = s else { return Vec::new() };
    match shlex::split(s) {
        Some(v) => v,
        None => {
            HaxMessage::GenericError {
                message: format!("could not parse --{who}-args (unmatched quote?): {s}"),
            }
            .report(message_format, None);
            std::process::exit(1);
        }
    }
}

/// Warn if the user's extra args re-specify a flag that the pipeline already
/// sets and relies on (e.g. those controlling where output is written). Such
/// flags are still forwarded — the tools keep the last occurrence — but
/// overriding them can break the charon→aeneas handoff or the layout the
/// generated proof project assumes. Matches both `-flag` and `-flag=value`.
fn warn_on_reserved_flags(
    user_args: &[String],
    reserved: &[&str],
    tool: &str,
    message_format: MessageFormat,
) {
    let overridden: Vec<&str> = reserved
        .iter()
        .copied()
        .filter(|&flag| {
            let prefix = format!("{flag}=");
            user_args
                .iter()
                .any(|arg| arg == flag || arg.starts_with(&prefix))
        })
        .collect();
    if !overridden.is_empty() {
        HaxMessage::GenericWarning {
            message: format!(
                "--{tool}-args re-specifies {tool} flag(s) the pipeline sets and relies on: {}. \
                 They are still forwarded, but this may break \
                 the extraction or the generated proof project.",
                overridden.join(", ")
            ),
        }
        .report(message_format, None);
    }
}

/// Format a `Command` as a copy-pasteable, shell-quoted invocation for display.
/// Args containing spaces or shell metacharacters (e.g. `{impl X for _}`,
/// `register_tool(_hax)`, `host.rustflags=["--cfg","hax"]`) are quoted so the
/// printed line can be pasted into a shell verbatim. Display-only: the real
/// command is executed without a shell, so quoting never affects execution.
fn format_command(cmd: &process::Command) -> String {
    let parts: Vec<String> = std::iter::once(cmd.get_program())
        .chain(cmd.get_args())
        .map(|p| p.to_string_lossy().into_owned())
        .collect();
    shlex::try_join(parts.iter().map(String::as_str)).unwrap_or_else(|_| parts.join(" "))
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
/// Runs the charon + aeneas pipeline for the `lean` backend.
/// Returns `true` if an error occurred.
pub fn run(
    options: &LeanOptions,
    output_dir: Option<PathBuf>,
    verbose: u8,
    message_format: MessageFormat,
) -> bool {
    // Project discovery and per-crate tool resolution: the crate being
    // processed is the root package of the current invocation.
    let project = match tools::project::ProjectContext::load(message_format) {
        Ok(project) => project,
        Err(message) => {
            HaxMessage::GenericError { message }.report(message_format, None);
            return true;
        }
    };
    let crate_dir = project
        .root_package
        .as_ref()
        .map(|package| package.dir.clone())
        .unwrap_or_else(|| std::env::current_dir().expect("Could not get current directory"));
    let crate_name = project
        .root_package
        .as_ref()
        .map(|package| package.name.replace('-', "_"))
        .unwrap_or_else(|| "output".to_string());

    let member = project.member_config(&crate_dir);
    let workspace = project.workspace_config.as_ref();
    let provide = |tool: &str| match tools::provide_tool(tool, member, workspace, message_format) {
        Ok(provided) => Some(provided),
        Err(message) => {
            HaxMessage::GenericError { message }.report(message_format, None);
            None
        }
    };
    // Charon finds `charon-driver` next to its own executable; providing
    // the tool guarantees the sibling is there.
    let (Some(charon), Some(aeneas)) = (provide("charon"), provide("aeneas")) else {
        return true;
    };
    let charon = charon.executables["charon"].clone();
    // Keep aeneas's resolution: the generated lakefile pins the aeneas Lean
    // library to the matching version, reusing this resolution rather than
    // resolving aeneas a second time.
    let tools::Provided {
        executables: aeneas_executables,
        resolution: aeneas_resolution,
    } = aeneas;
    let aeneas = aeneas_executables["aeneas"].clone();

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

    HaxMessage::Step {
        verb: "Running".to_string(),
        target: "charon".to_string(),
    }
    .report(message_format, None);

    // Parse once so we can both inspect and forward the user's charon flags.
    // `--dest-file` is reserved: its value is fed verbatim to aeneas below.
    let user_charon_args = shell_split(options.charon_args.as_deref(), "charon", message_format);
    warn_on_reserved_flags(
        &user_charon_args,
        CHARON_WARN_FLAGS,
        "charon",
        message_format,
    );

    let mut charon_cmd = process::Command::new(&charon);
    charon_cmd.args([
        "cargo",
        "--preset=aeneas",
        "--dest-file",
        llbc_file.to_str().expect("non-UTF8 path"),
        // Compile the crate as hax does: set `--cfg=hax_compilation` (so hax-lib
        // proc macros emit their verification artifacts) and register the `_hax`
        // tool attribute namespace.
        "--rustc-arg=--cfg=hax_compilation",
        "--rustc-arg=-Zcrate-attr=feature(register_tool)",
        "--rustc-arg=-Zcrate-attr=register_tool(_hax)",
    ]);
    // User-supplied charon flags go before the `--` cargo separator.
    charon_cmd.args(&user_charon_args);
    // Everything after `--` is forwarded to cargo: build the host (proc-macro)
    // crates with `--cfg hax` too, so hax-lib macros expand consistently.
    charon_cmd.args([
        "--",
        "-Zhost-config",
        "-Ztarget-applies-to-host",
        "--config",
        r#"host.rustflags=["--cfg","hax"]"#,
    ]);
    if verbose > 0 {
        HaxMessage::SubprocessOutput {
            prefix: "cmd".into(),
            line: format_command(&charon_cmd),
        }
        .report(message_format, None);
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

    // Parse once so we can both inspect and forward the user's aeneas flags. The
    // output-layout flags are reserved: overriding them moves the output away
    // from where the per-file report and `--lakefile` generation expect it.
    let user_aeneas_args = shell_split(options.aeneas_args.as_deref(), "aeneas", message_format);
    warn_on_reserved_flags(
        &user_aeneas_args,
        AENEAS_WARN_FLAGS,
        "aeneas",
        message_format,
    );

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

    HaxMessage::Step {
        verb: "Running".to_string(),
        target: format!("aeneas on {}", llbc_file.display()),
    }
    .report(message_format, None);

    // We run aeneas with `-core-models-lib` so it uses hax's core models library
    // for the translation, `-split-files` so it emits the function and type files
    // (`Funs.lean`/`Types.lean`, and any proof-obligation / external-template
    // files) separately, and `-subdir <PkgName>/Extraction` so they land in
    // `<lean_dir>/<PkgName>/Extraction/` with import paths prefixed by
    // `<PkgName>.Extraction.`
    let subdir = format!("{pkg_name}/Extraction");
    let mut aeneas_cmd = process::Command::new(&aeneas);
    aeneas_cmd.args([
        "-backend",
        "lean",
        "-core-models-lib",
        "-split-files",
        "-specs",
        "hax",
        llbc_file.to_str().expect("non-UTF8 path"),
        "-dest",
        lean_dir.to_str().expect("non-UTF8 path"),
        "-subdir",
        &subdir,
    ]);
    aeneas_cmd.args(&user_aeneas_args);
    if verbose > 0 {
        HaxMessage::SubprocessOutput {
            prefix: "cmd".into(),
            line: format_command(&aeneas_cmd),
        }
        .report(message_format, None);
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
        use tools::resolve::{Resolved, resolve_version};
        let defaults = tools::defaults::defaults();
        let version_of = |resolution: tools::resolve::Resolution| match resolution.kind {
            Resolved::Version(version) => version,
            Resolved::Path(_) => unreachable!("`[versions]` entries always resolve to versions"),
        };
        // The aeneas Lean proof library must match the aeneas binary; its
        // rev is the resolved aeneas version, reused from the resolution
        // that selected the binary above. A path-resolved aeneas has no
        // version hax can name, so the default is pinned instead.
        let aeneas_rev = match aeneas_resolution.kind {
            Resolved::Version(version) => version,
            Resolved::Path(path) => {
                let default = defaults.tools["aeneas"].clone();
                HaxMessage::GenericWarning {
                    message: format!(
                        "aeneas resolves to the local binary {}; pinning the aeneas Lean \
                         library to the default {default} in the generated lakefile",
                        path.display()
                    ),
                }
                .report(message_format, None);
                default
            }
        };
        let pins = lakefile::LakefilePins {
            aeneas_rev,
            lean_toolchain: version_of(resolve_version("lean", member, workspace, defaults)),
            hax_lean_lib_rev: version_of(resolve_version(
                "hax-lean-lib",
                member,
                workspace,
                defaults,
            )),
        };
        lakefile::generate(&lean_dir, &crate_name, &pins, message_format);
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
