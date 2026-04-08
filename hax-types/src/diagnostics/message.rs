use crate::cli_options::{Backend, BackendName, MessageFormat};
use crate::diagnostics::report::ReportCtx;
use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
#[repr(u8)]
pub enum HaxMessage {
    Diagnostic {
        diagnostic: super::Diagnostics,
        working_dir: Option<PathBuf>,
    } = 254,
    BinaryNotFound {
        binary_name: String,
        env_var: String,
        hint: Option<String>,
    } = 0,
    ProducedFile {
        path: PathBuf,
        wrote: bool,
    } = 1,
    HaxEngineFailure {
        exit_code: i32,
    } = 2,
    CargoBuildFailure = 3,
    WarnExperimentalBackend {
        backend: Backend,
    } = 4,
    ProfilingData(crate::engine_api::ProfilingData) = 5,
    Stats {
        errors_per_item: Vec<(hax_frontend_exporter::DefId, usize)>,
    } = 6,
    GenericError {
        message: String,
    } = 7,
    RunningStep {
        step: String,
    } = 9,
    SubprocessOutput {
        prefix: String,
        line: String,
    } = 10,
    OutputTruncated {
        prefix: String,
        remaining: usize,
        log_path: PathBuf,
    } = 11,
    UnsupportedOption {
        option: String,
        backend: BackendName,
    } = 12,
}

impl HaxMessage {
    // https://doc.rust-lang.org/reference/items/enumerations.html#pointer-casting
    pub fn discriminant(&self) -> u16 {
        unsafe { *(self as *const Self as *const u16) }
    }

    pub fn code(&self) -> String {
        match self {
            HaxMessage::Diagnostic { diagnostic, .. } => diagnostic.kind.code(),
            _ => format!("CARGOHAX{:0>4}", self.discriminant()),
        }
    }
}

const ENGINE_BINARY_NAME: &str = "hax-engine";

use annotate_snippets::{Level, Renderer};

impl HaxMessage {
    pub fn report(self, message_format: MessageFormat, rctx: Option<&mut ReportCtx>) {
        if let Some(rendered) = self.render(message_format, rctx) {
            println!("{rendered}")
        }
    }
    pub fn report_styled(self, rctx: Option<&mut ReportCtx>) {
        println!("{}", self.render_styled(rctx))
    }

    pub fn render(
        self,
        message_format: MessageFormat,
        mut rctx: Option<&mut ReportCtx>,
    ) -> Option<String> {
        if let (Some(r), HaxMessage::Diagnostic { diagnostic, .. }) = (rctx.as_mut(), &self)
            && r.seen_already(diagnostic.clone())
        {
            return None;
        }
        Some(match message_format {
            MessageFormat::Json => serde_json::to_string(&self).unwrap(),
            MessageFormat::Human => self.render_styled(rctx),
        })
    }
    pub fn render_styled(self, rctx: Option<&mut ReportCtx>) -> String {
        let renderer = Renderer::styled();
        match self {
            Self::Diagnostic {
                diagnostic,
                working_dir,
            } => {
                let mut _rctx = None;
                let rctx = rctx.unwrap_or_else(|| _rctx.get_or_insert(ReportCtx::default()));
                diagnostic.with_message(
                    rctx,
                    working_dir.as_ref().map(PathBuf::as_path),
                    Level::Error,
                    |msg| format!("{}", renderer.render(msg)),
                )
            }
            Self::BinaryNotFound {
                binary_name,
                env_var,
                hint,
            } => {
                use colored::Colorize;
                let mut message = format!(
                    "hax: The binary [{}] was not found in your [PATH].\n\
                     Please make sure it is installed and is in PATH!\n\
                     Hint: set the [{}] environment variable to provide its path explicitly.",
                    binary_name, env_var
                );
                if let Some(hint) = hint {
                    message.push_str(&format!("\n{}", hint.bright_black()));
                }
                format!("{}", renderer.render(Level::Error.title(&message)))
            }
            Self::ProducedFile { mut path, wrote } => {
                // Make path relative if possible
                if let Ok(current_dir) = std::env::current_dir() {
                    if let Ok(relative) = path.strip_prefix(current_dir) {
                        path = PathBuf::from(".").join(relative).to_path_buf();
                    }
                }
                let title = if wrote {
                    format!("hax: wrote file {}", path.display())
                } else {
                    format!("hax: unchanged file {}", path.display())
                };
                format!("{}", renderer.render(Level::Info.title(&title)))
            }
            Self::HaxEngineFailure { exit_code } => {
                let title = format!(
                    "hax: {} exited with non-zero code {}",
                    ENGINE_BINARY_NAME, exit_code,
                );
                format!("{}", renderer.render(Level::Error.title(&title)))
            }
            Self::ProfilingData(data) => {
                fn format_with_dot(shift: u32, n: u64) -> String {
                    let factor = 10u64.pow(shift);
                    format!("{}.{}", n / factor, n % factor)
                }
                let title = format!(
                    "hax[profiling]: {}: {}ms, memory={}, {} item{}{}",
                    data.context,
                    format_with_dot(6, data.time_ns),
                    data.memory,
                    data.quantity,
                    if data.quantity > 1 { "s" } else { "" },
                    if data.errored {
                        " (note: this failed!)"
                    } else {
                        ""
                    }
                );
                format!("{}", renderer.render(Level::Info.title(&title)))
            }
            Self::Stats { errors_per_item } => {
                let success_items = errors_per_item.iter().filter(|(_, n)| *n == 0).count();
                let total = errors_per_item.len();
                let title = format!(
                    "hax: {}/{} items were successfully translated ({}% success rate)",
                    success_items,
                    total,
                    (success_items * 100) / total
                );
                format!("{}", renderer.render(Level::Info.title(&title)))
            }
            Self::CargoBuildFailure => {
                let title =
                    "hax: running `cargo build` was not successful, continuing anyway.".to_string();
                format!("{}", renderer.render(Level::Warning.title(&title)))
            }
            Self::WarnExperimentalBackend { backend } => {
                let title = format!(
                    "hax: Experimental backend \"{}\" is work in progress.",
                    backend
                );
                format!("{}", renderer.render(Level::Warning.title(&title)))
            }
            Self::GenericError { message } => {
                let title = format!("hax: {}", message);
                format!("{}", renderer.render(Level::Error.title(&title)))
            }
            Self::RunningStep { step } => {
                use colored::Colorize;
                format!("{:>12} {}", "Running".bold().green(), step)
            }
            Self::SubprocessOutput { prefix, line } => {
                format!("{:>12} > {}", prefix, line)
            }
            Self::OutputTruncated {
                prefix,
                remaining,
                log_path,
            } => {
                format!(
                    "{:>12} > ... ({} more lines, full output in {})",
                    prefix,
                    remaining,
                    log_path.display()
                )
            }
            Self::UnsupportedOption { option, backend } => {
                let title = format!(
                    "hax: option {} is not supported by the {} backend and will be ignored",
                    option, backend
                );
                format!("{}", renderer.render(Level::Warning.title(&title)))
            }
        }
    }
}
