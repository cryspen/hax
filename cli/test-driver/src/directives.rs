//! Parses `@` directives.

use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    fmt::Display,
    hash::Hash,
    str::FromStr,
};

mod parser;

use anyhow::{Context, Error, Result, bail};
use clap::Parser;
use hax_frontend_exporter::{AttrArgs, AttributeKind, MetaItemLit};
use hax_types::cli_options::{BackendName, BackendOptions, Command, Options};

use crate::directives::parser::FailEntry;

/// Parses the payload of an `@cli:` directive.
fn parse_cli(raw_cli: &str) -> Result<(BackendName, Vec<String>, Vec<String>)> {
    let cli = shlex::split(raw_cli)
                .with_context(|| format!("Could not parse `{raw_cli}` as a valid shell command. This is probably due to unclosed quote."))?;
    let options =
        Options::try_parse_from(["hax"].into_iter().chain(cli.iter().map(|s| s.as_str())))?;

    let Command::Backend(backend_options) = options.command else {
        unreachable!("Expected backend options since the command starts with `into `!")
    };

    if backend_options.prune_haxmeta.is_some() {
        bail!("Specifying manually a `--prune_haxmeta` is forbiden")
    }
    if backend_options.debug_engine.is_some() {
        bail!("Specifying manually a `--debug_engine` is forbiden")
    }
    if backend_options.profile {
        bail!("Specifying manually a `--profile` is forbiden")
    }
    if backend_options.stats {
        bail!("Specifying manually a `--stats` is forbidden")
    }

    let backend_options_with_profile = BackendOptions {
        profile: true,
        ..backend_options.clone()
    };

    let backend = BackendName::from(&backend_options.backend);
    let (into_flags, backend_flags) = (0..cli.len())
        .find_map(|i| {
            let (lhs, rhs): (&[String], &[String]) = (&cli[..i], &cli[(i + 1)..]);
            let cli = std::iter::once("hax".to_string()).chain(
                lhs.iter().cloned().chain(
                    ["--profile".into(), backend.to_string()]
                        .into_iter()
                        .chain(rhs.iter().cloned()),
                ),
            );
            if let Ok(options) = Options::try_parse_from(cli)
                && options.command == Command::Backend(backend_options_with_profile.clone())
            {
                return Some((lhs[1..].to_vec(), rhs.to_vec()));
            } else {
                None
            }
        })
        .expect("Could not split arguments!");

    Ok((backend, into_flags, backend_flags))
}

impl TryFrom<parser::Directive> for Directive {
    type Error = Error;

    fn try_from(value: parser::Directive) -> Result<Self> {
        Ok(match value {
            parser::Directive::Cli { flags } => {
                let (backend, into_flags, backend_flags) = parse_cli(&flags)?;
                Self::Test(TestDirective::SetCli {
                    backend,
                    into_flags,
                    backend_flags,
                })
            }
            parser::Directive::Backend { backend, value } => {
                Self::Test(TestDirective::BackendDirective {
                    backend: parse_backend_name(&backend)?,
                    directive: value,
                })
            }
            parser::Directive::Off { backends } => Self::Test(TestDirective::Off {
                backends: backends
                    .into_iter()
                    .map(|s| parse_backend_name(s.as_str()))
                    .collect::<Result<HashSet<_>>>()?,
            }),
            parser::Directive::Fail { kind, entries } => Self::Item(ItemDirective::Failure {
                kind,
                backends: entries
                    .into_iter()
                    .map(|FailEntry { backend, errcodes }| {
                        Ok((
                            parse_backend_name(&backend)?,
                            errcodes.into_iter().map(ErrorCode::new).collect(),
                        ))
                    })
                    .collect::<Result<_>>()?,
            }),
        })
    }
}

impl FromStr for Directive {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        Ok(Directive::try_from(parser::parse_directive(s)?)?)
    }
}

impl Display for TestDirective {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestDirective::SetCli {
                backend,
                into_flags,
                backend_flags,
            } => {
                let join = |v: &Vec<String>| shlex::try_join(v.iter().map(|s| s.as_str())).unwrap();
                write!(
                    f,
                    "@cli: {} {backend} {}",
                    join(into_flags),
                    join(backend_flags)
                )
            }
            TestDirective::BackendDirective { backend, directive } => {
                write!(f, "@backend({backend}): {directive}")
            }
            TestDirective::Off { backends } => {
                write!(
                    f,
                    "@off: {}",
                    backends
                        .iter()
                        .map(BackendName::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

impl Display for ItemDirective {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ItemDirective::Failure { kind, backends } => {
                write!(f, "@fail({kind}): ")?;
                let mut first = true;
                for (backend, errors) in backends {
                    if errors.is_empty() {
                        continue;
                    }
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(
                        f,
                        "{backend}({})",
                        errors
                            .iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Directive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Directive::Test(test_directive) => test_directive.fmt(f),
            Directive::Item(item_directive) => item_directive.fmt(f),
        }
    }
}

impl Display for FailureKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FailureKind::Typecheck => write!(f, "tc"),
            FailureKind::Extract => write!(f, "extraction"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Directives that apply to an entire test module.
pub enum TestDirective {
    SetCli {
        /// The backend we are setting command line options for.
        backend: BackendName,
        /// The flags to put on the `cargo hax into` command.
        into_flags: Vec<String>,
        /// The flags to put on the `cargo hax into <backend>` command.
        backend_flags: Vec<String>,
    },
    BackendDirective {
        backend: BackendName,
        directive: String,
    },
    Off {
        backends: HashSet<BackendName>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Unified representation of every directive accepted by the driver.
pub enum Directive {
    Test(TestDirective),
    Item(ItemDirective),
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Kinds of failures that can be expected by directives.
pub enum FailureKind {
    Typecheck,
    Extract,
}

#[derive(Clone, Debug, Eq)]
/// Wrapper that normalizes comparisons between error codes.
pub struct ErrorCode {
    /// The raw error code we received or the user typed
    original: String,
    /// The "normalized" version, used for hashing and comparison.
    normalized: String,
}

impl Hash for ErrorCode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // `original` is ignore purposely
        self.normalized.hash(state);
    }
}

impl ErrorCode {
    pub fn new(original: String) -> Self {
        let normalized = {
            fn trim(s: &str) -> &str {
                s.trim_start_matches('0')
            }
            if let Some(s) = original.strip_prefix("HAX") {
                format!("HAX{}", trim(s))
            } else {
                trim(&original).to_string()
            }
        };
        Self {
            original,
            normalized,
        }
    }
}

impl PartialEq for ErrorCode {
    fn eq(&self, other: &Self) -> bool {
        &self.normalized == &other.normalized
    }
}

impl Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.original.fmt(f)
    }
}

impl Directive {
    /// Attempts to merge two directives of the same kind, returning `true` when
    /// the merge succeeds.
    pub fn merge(&mut self, other: &Self) -> bool {
        match (self, other) {
            (
                Directive::Item(ItemDirective::Failure { kind, backends }),
                Directive::Item(ItemDirective::Failure {
                    kind: kind_,
                    backends: backends_,
                }),
            ) if kind == kind_ => {
                for backend_name in backends_.keys() {
                    if let Entry::Vacant(entry) = backends.entry(*backend_name) {
                        entry.insert(vec![]);
                    }
                }
                for (backend_name, errors) in backends {
                    if let Some(other_errors) = backends_.get(backend_name) {
                        errors.extend_from_slice(other_errors)
                    }
                }
                true
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Directives that target a single item.
pub enum ItemDirective {
    Failure {
        kind: FailureKind,
        backends: HashMap<BackendName, Vec<ErrorCode>>,
    },
}

fn parse_backend_name(s: &str) -> Result<BackendName> {
    <BackendName as clap::ValueEnum>::from_str(s, true)
        .ok()
        .context("Parsing backend name")
}

/// Returns the textual content of a doc comment attribute, if any.
pub fn comment_of_attribute(attribute: &hax_frontend_exporter::Attribute) -> Option<&str> {
    match &attribute {
        hax_frontend_exporter::Attribute::Parsed(AttributeKind::DocComment { comment, .. }) => {
            Some(comment.as_str())
        }
        hax_frontend_exporter::Attribute::Unparsed(hax_frontend_exporter::AttrItem {
            path,
            args:
                AttrArgs::Eq {
                    expr: MetaItemLit { symbol, .. },
                    ..
                },
            ..
        }) if path == "doc" => Some(symbol.as_str()),
        _ => None,
    }
}

/// Attempts to parse a directive encoded in the provided attribute.
pub fn directive_of_attribute(
    attribute: &hax_frontend_exporter::Attribute,
) -> Result<Option<Directive>> {
    let Some(comment) = comment_of_attribute(attribute) else {
        return Ok(None);
    };
    let comment = comment.trim();
    if let Some(directive) = comment.strip_prefix("@") {
        Ok(Some(Directive::from_str(directive.trim())?))
    } else {
        Ok(None)
    }
}
