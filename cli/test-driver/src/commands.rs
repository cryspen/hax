//! Async helpers that wrap the `cargo hax` commands and diagnostic plumbing.
//!
//! This module is intentionally lightweight: it only hides the raw command
//! invocation details and structures the diagnostics that are produced by the
//! backend.

use anyhow::{Context as _, Result};
use hax_frontend_exporter::DefId;
use hax_types::{
    cli_options::{BackendName, MessageFormat},
    diagnostics::message::HaxMessage,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use crate::{
    directives::{Directive, ErrorCode, ItemDirective},
    helpers,
    log::{JobKind, ReportMessage},
};

/// Runs `cargo hax serialize` and returns the path of the produced `.haxmeta`
/// file.
pub async fn hax_serialize(flags: &[&str]) -> Result<PathBuf> {
    static PERMITS: tokio::sync::Semaphore = tokio::sync::Semaphore::const_new(1);
    let _permit = PERMITS.acquire().await?;
    let mut command = tokio::process::Command::new("cargo");
    command.args(["hax", "--message-format", "json", "serialize"]);
    command.args(flags);
    let out = command.output().await?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let raw_stdout = stdout.clone();
    let stderr = String::from_utf8_lossy(&out.stderr);
    let path = stdout
        .lines()
        .flat_map(|s| serde_json::from_str::<HaxMessage>(s))
        .find_map(|hax_message| match hax_message {
            HaxMessage::ProducedFile { path, .. } => Some(path.clone()),
            _ => None,
        })
        .with_context(|| format!("`{command:?}` produced no haxmeta file\n\n\nstderr={stderr}\n\n\nstdout={raw_stdout}"))?;
    Ok(path)
}

/// Captures the output of a `cargo hax into` invocation.
pub struct HaxEngineOutput {
    pub error_code: i32,
    pub messages: Vec<OutMsg>,
    pub stderr: String,
}

impl HaxEngineOutput {
    /// Forwards the captured stderr/stdout to the logging infrastructure.
    pub fn report_stderr_and_stdout(&self, job: JobKind) {
        job.report(ReportMessage::Stderr(self.stderr.clone()));
        job.report(ReportMessage::Stdout({
            let rendered = self
                .messages
                .iter()
                .filter_map(|message| message.render())
                .collect::<Vec<_>>();
            rendered.join("\n")
        }));
    }

    /// Extracts the diagnostics that were emitted by the engine.
    pub fn diagnostics(&self) -> Diagnostics {
        let set: HashSet<_> = self
            .messages
            .iter()
            .filter_map(Diagnostic::try_from_out_msg)
            .collect();
        Diagnostics::new(set.into_iter())
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
/// A single diagnostic message emitted by the backend.
pub struct Diagnostic {
    pub def_id: Option<DefId>,
    pub error_code: ErrorCode,
    pub full_message: OutMsg,
}

impl Diagnostic {
    fn try_from_out_msg(out_msg: &OutMsg) -> Option<Self> {
        match out_msg {
            OutMsg::Hax(HaxMessage::Diagnostic { diagnostic, .. }) => Some(Self {
                def_id: diagnostic.owner_id.clone(),
                error_code: ErrorCode::new(diagnostic.kind.code()),
                full_message: out_msg.clone(),
            }),
            _ => None,
        }
    }

    /// Returns `true` if this diagnostic belongs to the provided item or one of
    /// its descendants.
    pub fn is_for_item(&self, item_id: &DefId) -> bool {
        self.def_id
            .as_ref()
            .map(|child| helpers::def_id_under(item_id, child))
            .unwrap_or(true)
    }
}

/// Diagnostic multimap keyed by [`ErrorCode`].
pub struct Diagnostics(HashMap<ErrorCode, Vec<Diagnostic>>);

impl Diagnostics {
    fn new(it: impl Iterator<Item = Diagnostic>) -> Self {
        let mut map: HashMap<_, Vec<_>> = HashMap::new();
        for diag in it {
            map.entry(diag.error_code.clone()).or_default().push(diag);
        }
        Self(map)
    }

    /// Removes a diagnostic from Self if the diagnostic is for the item
    /// `item_id` (or below), and if the diagnostic is tagged with an error that
    /// matches `error_code`.
    /// Returns `Some(_)` if a matching diagnostic was found.
    /// Removes (and returns) a diagnostic that matches the provided item and
    /// error code, if present.
    pub fn remove(&mut self, item_id: &DefId, error_code: &ErrorCode) -> Option<Diagnostic> {
        if let Some(diags) = self.0.get_mut(error_code)
            && let Some((i, diag)) = diags
                .iter()
                .enumerate()
                .find(|(_, diag)| diag.is_for_item(item_id))
        {
            let diag = diag.clone();
            diags.swap_remove(i);
            Some(diag)
        } else {
            None
        }
    }

    /// Iterates over the retained diagnostic messages.
    pub fn iter(&self) -> impl Iterator<Item = &OutMsg> {
        self.0.values().flatten().map(|diag| &diag.full_message)
    }

    /// Queues directives that should be promoted into the source code for all
    /// diagnostics that remain unexpected.
    pub async fn add_directives_in_files(
        &self,
        backend: BackendName,
        fallback_def_id: &DefId,
    ) -> Result<()> {
        for diag in self.0.values().flatten() {
            let owner_id = diag.def_id.as_ref().unwrap_or(fallback_def_id);
            let Some(span) = crate::span_hint::span_hint(owner_id).await? else {
                println!("No span for {}", helpers::string_of_def_id(owner_id));
                continue;
            };
            let (Some(span_path), line, is_mod) = span.get_file_and_line() else {
                continue;
            };

            use crate::promote_directives::*;
            let kind = LineKind::Directive {
                directive: Directive::Item(ItemDirective::Failure {
                    kind: crate::directives::FailureKind::Extract,
                    backends: std::iter::once((backend, vec![diag.error_code.clone()])).collect(),
                }),
                bang: is_mod,
            };
            push_line(span_path, Line { line, kind })?;
        }

        Ok(())
    }
}

/// Executes `cargo hax into` for the specified backend.
pub async fn hax_engine(
    haxmeta: &Path,
    test_module_name: &str,
    output_dir: &Path,
    backend: BackendName,
    into_flags: &[String],
    backend_flags: &[String],
) -> Result<HaxEngineOutput> {
    let mut command = tokio::process::Command::new("cargo");
    command.args(["hax", "--message-format", "json", "--haxmeta"]);
    command.arg(haxmeta);
    command.arg("into");
    command.arg("--output-dir");
    command.arg(output_dir);
    command.args(["--prune-haxmeta", test_module_name]);
    command.args(into_flags);
    command.arg(backend.to_string());
    command.args(backend_flags);
    let out = command.output().await?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    let messages = stdout
        .lines()
        .map(|s| {
            serde_json::from_str::<OutMsg>(s).unwrap_or_else(|_| OutMsg::Unknown(s.to_string()))
        })
        .collect();
    Ok(HaxEngineOutput {
        error_code: out
            .status
            .code()
            .context("No error code: was the process terminated?")?,
        messages,
        stderr,
    })
}

/// The JSON-encoded messages `cargo hax` can emit
#[derive(Serialize, Deserialize, Debug, Clone, Hash, Eq, PartialEq)]
#[serde(untagged)]
/// JSON messages emitted by `cargo hax`.
pub enum OutMsg {
    Cargo(cargo_metadata::CompilerMessage),
    Hax(HaxMessage),
    Unknown(String),
}

impl OutMsg {
    /// Renders the message into a human-readable string, when possible.
    pub fn render(&self) -> Option<String> {
        let owner = if let OutMsg::Hax(HaxMessage::Diagnostic {
            diagnostic:
                hax_types::diagnostics::Diagnostics {
                    owner_id: Some(owner),
                    ..
                },
            ..
        }) = &self
        {
            Some(format!("owner={owner:?}"))
        } else {
            None
        };
        match self {
            OutMsg::Cargo(compiler_message) => Some(
                compiler_message
                    .message
                    .rendered
                    .clone()
                    .unwrap_or_else(|| compiler_message.message.message.clone()),
            ),
            OutMsg::Hax(hax_message) => hax_message
                .clone()
                .render(MessageFormat::Human, None)
                .map(|s| format!("{s}{}", owner.unwrap_or("".into()))),
            OutMsg::Unknown(unknown) => Some(unknown.clone()),
        }
    }
}
