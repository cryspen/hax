use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};

mod parser;

use anyhow::{Context, Error, Result, bail};
use clap::Parser;
use hax_frontend_exporter::AttributeKind;
use hax_types::cli_options::{Backend, BackendName, BackendOptions, Command, Options};

use crate::directives::parser::FailEntry;

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
        bail!("Specifying manually a `--stats` is forbiden")
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
                            errcodes.into_iter().map(ErrorCode).collect(),
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TestDirective {
    SetCli {
        /// The backend we setting command line options for.
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
pub enum Directive {
    Test(TestDirective),
    Item(ItemDirective),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FailureKind {
    Typecheck,
    Extract,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ErrorCode(pub String);

#[derive(Clone, Debug, Eq, PartialEq)]
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

pub fn directive_of_attribute(
    attribute: &hax_frontend_exporter::Attribute,
) -> Result<Option<Directive>> {
    let hax_frontend_exporter::Attribute::Parsed(AttributeKind::DocComment { comment, .. }) =
        attribute
    else {
        return Ok(None);
    };
    let comment = comment.trim();
    if let Some(directive) = comment.strip_prefix("@") {
        Ok(Some(Directive::from_str(directive.trim())?))
    } else {
        Ok(None)
    }
}
