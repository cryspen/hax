use crate::cli_options::{Backend, BackendName, MessageFormat};
use crate::diagnostics::report::ReportCtx;
use crate::prelude::*;

/// What a `hax.toml` entry resolved to.
#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum ResolvedValue {
    Version(String),
    /// The path of a `path` entry, as given.
    Path(String),
}

/// One resolved tool or declared version: what it is, what it resolved to,
/// and a description of where that came from.
#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
pub struct ToolResolution {
    pub name: String,
    #[serde(flatten)]
    pub resolved: ResolvedValue,
    pub source: String,
}

impl ToolResolution {
    /// The resolved version or path, as shown.
    fn value(&self) -> &str {
        match &self.resolved {
            ResolvedValue::Version(value) | ResolvedValue::Path(value) => value,
        }
    }
}

/// How a resolved `hax-lib` version relates to the range a `cargo-hax`
/// binary accepts.
#[derive_group(Serializers)]
#[derive(Debug, Clone, Copy, JsonSchema, Hash, Eq, PartialEq)]
pub enum HaxLibCompatibility {
    Compatible,
    /// Older than the binary: the project's dependency needs updating
    /// (or an older cargo-hax is needed).
    TooOld,
    /// Newer than the binary (typically after a `cargo update`): update
    /// cargo-hax, or pin `hax-lib` back to the binary's version.
    TooNew,
}

impl HaxLibCompatibility {
    /// The parenthesized status `tools show` annotates a `hax-lib` row with.
    fn describe(self) -> &'static str {
        match self {
            Self::Compatible => "compatible",
            Self::TooOld => "INCOMPATIBLE: too old for this cargo-hax",
            Self::TooNew => "INCOMPATIBLE: newer than this cargo-hax",
        }
    }
}

/// The `hax-lib` version one crate's direct dependency resolved to.
#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
pub struct HaxLibStatus {
    #[serde(rename = "crate")]
    pub crate_name: String,
    pub version: String,
    pub compatibility: HaxLibCompatibility,
}

/// The entries one member crate resolves differently from the workspace.
#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
pub struct MemberOverride {
    #[serde(rename = "crate")]
    pub crate_name: String,
    pub tools: Vec<ToolResolution>,
    pub versions: Vec<ToolResolution>,
}

/// One version of one tool, as `tools list` reports it.
#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
pub struct ToolVersionListing {
    pub version: String,
    pub installed: bool,
    pub in_manifest: bool,
    pub default: bool,
    /// Whether the cached copy was checksum-verified at install time.
    /// Meaningless unless `installed`.
    pub verified: bool,
}

/// The versions of one tool, as `tools list` reports them.
#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
pub struct ToolListing {
    pub tool: String,
    pub versions: Vec<ToolVersionListing>,
    /// How many versions were left out of `versions` as too old.
    pub omitted: usize,
}

/// How one version came to be in the cache.
#[derive_group(Serializers)]
#[derive(Debug, Clone, Copy, JsonSchema, Hash, Eq, PartialEq)]
pub enum InstallStatus {
    /// Already in the cache, `verified` as recorded at install time.
    Cached { verified: bool },
    /// Freshly downloaded and installed.
    Installed { verified: bool },
}

/// One tool version an `install` run accounted for.
#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema, Hash, Eq, PartialEq)]
pub struct InstalledTool {
    pub tool: String,
    pub version: String,
    pub status: InstallStatus,
}

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
    GenericWarning {
        message: String,
    } = 8,
    Step {
        verb: String,
        target: String,
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
    HaxTomlWarning {
        path: PathBuf,
        message: String,
    } = 13,
    HaxTomlError {
        path: PathBuf,
        message: String,
    } = 14,
    MemberToolOverrides {
        crate_name: String,
        path: PathBuf,
        entries: Vec<String>,
    } = 15,
    StrayHaxToml {
        path: PathBuf,
    } = 16,
    UnverifiedInstall {
        tool: String,
        version: String,
        url: String,
    } = 17,
    NonDefaultToolVersion {
        tool: String,
        used: String,
        tested: String,
    } = 18,
    HaxLibIncompatible {
        crate_name: String,
        found: String,
        binary: String,
        expected: String,
        newer: bool,
    } = 19,
    CachedUnverifiedToolInUse {
        tool: String,
        version: String,
    } = 20,
    /// The result of `cargo hax tools show`.
    ToolsShow {
        /// The workspace-wide resolution of each managed tool.
        tools: Vec<ToolResolution>,
        /// The workspace-wide resolution of each declared-only version.
        versions: Vec<ToolResolution>,
        /// Every crate with a direct `hax-lib` dependency.
        hax_lib: Vec<HaxLibStatus>,
        member_overrides: Vec<MemberOverride>,
    } = 21,
    /// The result of `cargo hax tools list`.
    ToolsList {
        tools: Vec<ToolListing>,
        /// Whether the listing was restricted to cached versions, which is
        /// what an empty listing means.
        installed_only: bool,
    } = 22,
    /// The result of `cargo hax tools install`: the versions now in the
    /// cache. Versions that failed to install are reported as errors of
    /// their own and are absent here.
    ToolsInstalled {
        installed: Vec<InstalledTool>,
    } = 23,
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
        // A message that renders to nothing has nothing to print: a report
        // of an empty listing must not become a blank line.
        if let Some(rendered) = self.render(message_format, rctx)
            && !rendered.is_empty()
        {
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
            Self::GenericWarning { message } => {
                let title = format!("hax: {}", message);
                format!("{}", renderer.render(Level::Warning.title(&title)))
            }
            Self::Step { verb, target } => {
                use colored::Colorize;
                format!("{:>12} {}", verb.bold().green(), target)
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
            Self::HaxTomlWarning { path, message } => {
                let title = format!("hax: {}: {}", path.display(), message);
                format!("{}", renderer.render(Level::Warning.title(&title)))
            }
            Self::HaxTomlError { path, message } => {
                let title = format!("hax: {}: {}", path.display(), message);
                format!("{}", renderer.render(Level::Error.title(&title)))
            }
            Self::MemberToolOverrides {
                crate_name,
                path,
                entries,
            } => {
                let title = format!(
                    "hax: crate `{}` overrides the workspace tool configuration ({}) in {}. \
                     Prefer a single workspace-wide pin where possible.",
                    crate_name,
                    entries.join(", "),
                    path.display()
                );
                format!("{}", renderer.render(Level::Warning.title(&title)))
            }
            Self::HaxLibIncompatible {
                crate_name,
                found,
                binary,
                expected,
                newer,
            } => {
                let remedy = if newer {
                    format!(
                        "update cargo-hax to the release matching hax-lib {found}, or pin\n\
                         the `hax-lib` dependency to {expected} in Cargo.toml"
                    )
                } else {
                    format!(
                        "update the `hax-lib` dependency to {expected}, e.g. with\n\
                         `cargo update -p hax-lib --precise {expected}`, or install cargo-hax {found}"
                    )
                };
                let title = format!(
                    "incompatible `hax-lib` version\n\n\
                     this cargo-hax binary ({binary}) requires hax-lib {expected}\n\
                     found hax-lib {found} in Cargo.lock (crate `{crate_name}`)\n\n\
                     {remedy}"
                );
                format!("{}", renderer.render(Level::Error.title(&title)))
            }
            Self::NonDefaultToolVersion { tool, used, tested } => {
                let title =
                    format!("hax: using {tool} {used}; this hax release was tested with {tested}");
                format!("{}", renderer.render(Level::Info.title(&title)))
            }
            Self::UnverifiedInstall { tool, version, url } => {
                let title = format!(
                    "{tool} {version} is not in this release's manifest; \
                     installing without checksum verification"
                );
                let source = format!("source {url}");
                let remedy = format!(
                    "once a checksum ships, run \
                     `cargo hax tools install {tool}@{version} --force` to verify"
                );
                format!(
                    "{}",
                    renderer.render(
                        Level::Warning
                            .title(&title)
                            .footer(Level::Note.title(&source))
                            .footer(Level::Help.title(&remedy))
                    )
                )
            }
            Self::StrayHaxToml { path } => {
                let title = format!(
                    "hax: found {} outside the workspace root and member crate roots; \
                     it has no effect and is ignored",
                    path.display()
                );
                format!("{}", renderer.render(Level::Warning.title(&title)))
            }
            Self::CachedUnverifiedToolInUse { tool, version } => {
                let title = format!(
                    "using {tool} {version} from the cache; it was installed \
                     without checksum verification"
                );
                let remedy = format!(
                    "run `cargo hax tools install {tool}@{version} --force` to \
                     re-download and verify it once a checksum ships"
                );
                format!(
                    "{}",
                    renderer.render(
                        Level::Warning
                            .title(&title)
                            .footer(Level::Help.title(&remedy))
                    )
                )
            }
            Self::ToolsShow {
                tools,
                versions,
                hax_lib,
                member_overrides,
            } => render_tools_show(&tools, &versions, &hax_lib, &member_overrides),
            Self::ToolsList {
                tools,
                installed_only,
            } => render_tools_list(&tools, installed_only),
            Self::ToolsInstalled { installed } => render_tools_installed(&installed),
        }
    }
}

/// The name the `hax-lib` rows of `tools show` are labelled with.
const HAX_LIB_ROW: &str = "hax-lib";

/// One `  <name>  <value>  (<source>)` row of the `tools show` grid.
fn resolution_rows(
    entries: &[ToolResolution],
    name_width: usize,
    value_width: usize,
) -> impl Iterator<Item = String> + '_ {
    entries.iter().map(move |entry| {
        format!(
            "  {name:name_width$}  {value:value_width$}  ({source})",
            name = entry.name,
            value = entry.value(),
            source = entry.source,
        )
    })
}

/// `tools show`: the resolutions of the project, section by section, with
/// the name and value columns aligned across every section so the source
/// annotations line up in a single grid.
fn render_tools_show(
    tools: &[ToolResolution],
    versions: &[ToolResolution],
    hax_lib: &[HaxLibStatus],
    member_overrides: &[MemberOverride],
) -> String {
    let all = || {
        tools.iter().chain(versions).chain(
            member_overrides
                .iter()
                .flat_map(|member| member.tools.iter().chain(&member.versions)),
        )
    };
    // The `hax-lib` rows share the grid too, so `hax-lib` reads as a named
    // row rather than a bare version line.
    let name_width = all()
        .map(|entry| entry.name.len())
        .chain(hax_lib.iter().map(|_| HAX_LIB_ROW.len()))
        .max()
        .unwrap_or(0);
    let value_width = all()
        .map(|entry| entry.value().len())
        .chain(hax_lib.iter().map(|status| status.version.len()))
        .max()
        .unwrap_or(0);
    let hax_lib_row = |status: &HaxLibStatus, annotation: String| {
        format!(
            "  {name:name_width$}  {value:value_width$}  ({annotation})",
            name = HAX_LIB_ROW,
            value = status.version,
        )
    };

    let mut lines = vec!["tools:".to_string()];
    lines.extend(resolution_rows(tools, name_width, value_width));
    lines.push(String::new());
    lines.push("versions:".to_string());
    lines.extend(resolution_rows(versions, name_width, value_width));

    // One version across the project (or a single crate) is one row; crates
    // that disagree get one row each, naming the crate.
    let uniform = hax_lib.iter().all(|status| {
        (&status.version, status.compatibility) == (&hax_lib[0].version, hax_lib[0].compatibility)
    });
    match hax_lib {
        [] => {}
        [first, ..] => {
            lines.push(String::new());
            lines.push("libraries:".to_string());
            if uniform {
                lines.push(hax_lib_row(
                    first,
                    first.compatibility.describe().to_string(),
                ));
            } else {
                lines.extend(hax_lib.iter().map(|status| {
                    hax_lib_row(
                        status,
                        format!(
                            "crate `{}`: {}",
                            status.crate_name,
                            status.compatibility.describe()
                        ),
                    )
                }));
            }
        }
    }

    for member in member_overrides {
        lines.push(String::new());
        lines.push(format!("crate `{}` (overrides):", member.crate_name));
        lines.extend(resolution_rows(&member.tools, name_width, value_width));
        lines.extend(resolution_rows(&member.versions, name_width, value_width));
    }
    lines.join("\n")
}

/// `tools list`: one block per tool, each version annotated with what is
/// known about it.
fn render_tools_list(tools: &[ToolListing], installed_only: bool) -> String {
    let mut blocks = Vec::new();
    for listing in tools {
        let mut lines = vec![format!("{}:", listing.tool)];
        if listing.versions.is_empty() {
            lines.push(format!(
                "  ({})",
                if installed_only {
                    "none installed"
                } else {
                    "none"
                }
            ));
        }
        // Pad the version column so the markers line up.
        let width = listing
            .versions
            .iter()
            .map(|version| version.version.len())
            .max()
            .unwrap_or(0);
        for version in &listing.versions {
            let mut marks = Vec::new();
            if version.default {
                marks.push("default".to_string());
            }
            if version.installed {
                marks.push("installed".to_string());
                if !version.verified {
                    marks.push("unverified".to_string());
                }
            }
            if !version.in_manifest {
                marks.push("not in manifest".to_string());
            }
            lines.push(if marks.is_empty() {
                format!("  {}", version.version)
            } else {
                format!(
                    "  {version:width$}  ({marks})",
                    version = version.version,
                    marks = marks.join(", ")
                )
            });
        }
        if listing.omitted > 0 {
            lines.push(format!(
                "  ... {} older versions omitted (use --all)",
                listing.omitted
            ));
        }
        blocks.push(lines.join("\n"));
    }
    blocks.join("\n\n")
}

/// `tools install`: one Cargo-style line per version now in the cache.
fn render_tools_installed(installed: &[InstalledTool]) -> String {
    use colored::Colorize;
    installed
        .iter()
        .map(|entry| {
            let (verb, verified) = match entry.status {
                InstallStatus::Cached { verified } => ("Cached", verified),
                InstallStatus::Installed { verified } => ("Installed", verified),
            };
            let suffix = if verified { "" } else { " (unverified)" };
            format!(
                "{:>12} {} {}{}",
                verb.bold().green(),
                entry.tool,
                entry.version,
                suffix
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}
