#![feature(rustc_private)]

use std::{
    collections::{HashMap, HashSet},
    env::set_current_dir,
    fmt::Display,
    fs::{self, File},
    path::{Path, PathBuf},
    str::FromStr,
    sync::{Arc, LazyLock},
};

use anyhow::{Context as _, Result, bail};
use clap::Parser;
use futures::future::TryJoinAll;
use hax_frontend_exporter::{AttributeKind, DefId, DefPathItem, DisambiguatedDefPathItem, Item};
use hax_types::{
    cli_options::{BackendName, MessageFormat},
    diagnostics::message::HaxMessage,
    driver_api::HaxMeta,
};

use crate::directives::{Directive, ErrorCode, FailureKind, ItemDirective, TestDirective};

mod cli;
mod commands;
mod directives;
mod log;
use commands::*;
use log::*;

fn module_name(def_id: &DefId) -> Option<String> {
    match def_id.path.first() {
        Some(DisambiguatedDefPathItem {
            data: DefPathItem::TypeNs(module_name),
            disambiguator: 0,
        }) => Some(module_name.clone()),
        _ => None,
    }
}

#[derive(Clone, Debug)]
struct TestModule {
    module_name: String,
    def_id: DefId,
    test_directives: Vec<TestDirective>,
    items: Vec<(DefId, Vec<ItemDirective>)>,
}

impl TestModule {
    fn expected_errors(&self, backend: BackendName, kind: FailureKind) -> Vec<(DefId, ErrorCode)> {
        self.items
            .iter()
            .flat_map(|(def_id, directives)| {
                directives.iter().flat_map(|directive| match directive {
                    ItemDirective::Failure { kind: k, backends } if *k == kind => {
                        Some(backends.iter().filter_map(|(b, errors)| {
                            if backend == *b {
                                Some(errors.iter().map(|e| (def_id.clone(), e.clone())))
                            } else {
                                None
                            }
                        }))
                    }
                    _ => None,
                })
            })
            .flatten()
            .flatten()
            .collect()
    }
}

#[extension_traits::extension(trait ExtIntoIterator)]
impl<T, U: Iterator<Item = T>> U {
    fn expect_le_one(mut self) -> Result<Option<T>> {
        match (self.next(), self.next()) {
            (None, None) => Ok(None),
            (Some(first), None) => Ok(Some(first)),
            _ => bail!("expect_one_or_less: got 2 or more"),
        }
    }
}

impl TestModule {
    fn cli(&self, backend: BackendName) -> Result<(Vec<String>, Vec<String>)> {
        Ok(self
            .test_directives
            .iter()
            .filter_map(|directive| match directive {
                TestDirective::SetCli {
                    backend: b,
                    into_flags,
                    backend_flags,
                } if *b == backend => Some((into_flags.clone(), backend_flags.clone())),
                _ => None,
            })
            .expect_le_one()
            .context("Multiple @cli flags for the same backend")?
            .unwrap_or_default())
    }
    fn off(&self) -> HashSet<BackendName> {
        self.test_directives
            .iter()
            .filter_map(|directive| match directive {
                TestDirective::Off { backends } => Some(backends.into_iter()),
                _ => None,
            })
            .flatten()
            .copied()
            .collect()
    }
}

async fn collect() -> Result<Vec<TestModule>> {
    let (haxmeta, _): (HaxMeta<()>, _) =
        HaxMeta::read(fs::File::open(&haxmeta(&["--kind"]).await?).unwrap());
    let map = haxmeta
        .items
        .iter()
        .map(|item| {
            let directives = item
                .attributes
                .attributes
                .iter()
                .map(|attr| directives::directive_of_attribute(attr))
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .flatten();
            Ok((item.owner_id.clone(), directives))
        })
        .collect::<Result<Vec<_>>>()?;
    let mut tests: HashMap<String, TestModule> = HashMap::new();
    let mut items: HashMap<String, Vec<_>> = HashMap::new();
    for (def_id, directives) in map {
        let Some(module_name) = module_name(&def_id) else {
            continue;
        };
        let mut test_directives = vec![];
        let mut item_directives = vec![];
        for directive in directives {
            match directive {
                Directive::Test(test_directive) => test_directives.push(test_directive),
                Directive::Item(item_directive) => item_directives.push(item_directive),
            }
        }
        test_directives.reverse();
        item_directives.reverse();
        if def_id.path.len() == 1 {
            tests.insert(
                module_name.clone(),
                TestModule {
                    items: vec![(def_id.clone(), item_directives)],
                    def_id,
                    module_name,
                    test_directives,
                },
            );
        } else {
            if !test_directives.is_empty() {
                bail!(
                    "Item {:#?} has a test-level directive, but it is not a test",
                    def_id
                )
            }
            if !item_directives.is_empty() {
                items
                    .entry(module_name)
                    .or_default()
                    .push((def_id, item_directives));
            }
        }
    }
    for (module_name, items) in items {
        let test_module = tests.get_mut(&module_name).unwrap();
        for (def_id, directives) in items {
            test_module.items.push((def_id, directives))
        }
    }
    Ok(tests.into_values().collect())
}

#[derive(Clone, Debug)]
struct BackendTestsContext {
    tests: Vec<TestModule>,
    backend: BackendName,
    options: cli::Cli,
}

#[derive(Clone, Debug)]
struct BackendTestContext {
    test: TestModule,
    backend: BackendName,
    options: cli::Cli,
    haxmeta: PathBuf,
}

impl BackendTestContext {
    async fn run(self) -> Result<()> {
        static PERMITS: tokio::sync::Semaphore = tokio::sync::Semaphore::const_new(16);
        let _permit = PERMITS.acquire().await?;
        self.backend
            .job_kind(BackendJobKind::CargoHaxInto {
                test: self.test.module_name.to_string(),
            })
            .run(async |job| self.run_inner(job).await)
            .await
    }
    async fn run_inner(&self, job: JobKind) -> Result<()> {
        let (into_flags, backend_flags) = self.test.cli(self.backend)?;

        let out_dir = self
            .options
            .cache_dir()
            .join(&self.test.module_name)
            .join(self.backend.to_string());
        fs::create_dir_all(&out_dir)?;

        let HaxEngineOutput {
            error_code,
            messages,
            stderr,
        } = hax_engine(
            &self.haxmeta,
            &self.test.module_name,
            &out_dir,
            self.backend,
            &into_flags[..],
            &backend_flags[..],
        )
        .await?;

        job.report(ReportMessage::Stderr(stderr));
        job.report(ReportMessage::Stdout({
            let rendered = messages
                .iter()
                .filter_map(|message| message.render())
                .collect::<Vec<_>>();
            rendered
                .iter()
                .flat_map(|lines| lines.lines())
                .collect::<Vec<_>>()
                .join("\n")
        }));

        let error_codes = messages
            .iter()
            .filter_map(|message| match message {
                OutMsg::Hax(HaxMessage::Diagnostic { diagnostic, .. }) => Some((
                    diagnostic.owner_id.clone(),
                    diagnostic.kind.code(),
                    message.clone(),
                )),
                _ => None,
            })
            .collect::<Vec<_>>();

        let mut expected_errors = self
            .test
            .expected_errors(self.backend, FailureKind::Extract);

        let mut every_error_codes_matched = true;

        for (def_id, code, message) in &error_codes {
            let def_id = def_id.as_ref().unwrap_or(&self.test.def_id);
            fn def_id_under(parent: &DefId, child: &DefId) -> bool {
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

            if let Some((index, _)) =
                expected_errors
                    .iter()
                    .enumerate()
                    .find(|(_, (parent, error_code))| {
                        def_id_under(parent, &def_id) && error_code.0 == *code
                    })
            {
                expected_errors.remove(index);
            } else {
                job.report_message(message.render().unwrap());
                every_error_codes_matched = false;
            }
        }

        if !every_error_codes_matched {
            bail!("unexpected extraction failures");
        }

        if !expected_errors.is_empty() {
            let expected_errors = expected_errors
                .iter()
                .map(|(def_id, code)| {
                    let def_id: String = def_id
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
                        .join("::");
                    format!("{} in {def_id}", code.0)
                })
                .collect::<Vec<_>>()
                .join(", ");
            bail!(
                "Expected the following extraction errors: {}",
                expected_errors
            );
        }

        if error_code != 0 && error_codes.is_empty() {
            bail!("cargo hax into {}: exited with non-zero code", self.backend)
        }

        Ok(())
    }
}

#[extension_traits::extension(trait BackendNameExt)]
impl BackendName {
    fn job_kind(self, kind: BackendJobKind) -> JobKind {
        JobKind::BackendJob {
            kind,
            backend: self,
        }
    }
}

impl BackendTestsContext {
    async fn haxmeta(&self) -> Result<PathBuf> {
        self.backend
            .job_kind(BackendJobKind::CargoHaxSerialize)
            .run(|_| async {
                let original_path = haxmeta(&["-b", self.backend.to_string().as_str()]).await?;
                let path = self
                    .options
                    .cache_dir()
                    .join(format!("{}.haxmeta", self.backend));
                tokio::fs::rename(original_path, &path).await?;
                Ok(path)
            })
            .await
    }
    async fn run(self) -> Result<()> {
        let haxmeta = self.haxmeta().await?;

        self.tests
            .iter()
            .cloned()
            .map(|test| BackendTestContext {
                test,
                backend: self.backend,
                options: self.options.clone(),
                haxmeta: haxmeta.clone(),
            })
            .map(async |context| tokio::spawn(context.run()).await)
            .collect::<TryJoinAll<_>>()
            .await?
            .into_iter()
            .collect::<Result<Vec<_>>>()?;

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let options = cli::Cli::parse();
    options.prepare_folders()?;
    set_current_dir(options.tests_crate_dir()).unwrap();

    let disabled_backends = [
        BackendName::Ssprove,
        BackendName::Coq,
        BackendName::Easycrypt,
        BackendName::ProVerif,
        BackendName::Rust,
        BackendName::GenerateRustEngineNames,
    ];
    let backends: Vec<_> = BackendName::iter()
        .filter(|backend| !disabled_backends.contains(backend))
        .collect();

    let cache_dir = PathBuf::from(".hax-tests");
    let _ = tokio::fs::create_dir_all(&cache_dir).await;

    let tests = JobKind::ResolveTests.run(|_| collect()).await?;

    backends
        .iter()
        .copied()
        .map(async |backend| {
            let context = BackendTestsContext {
                tests: tests
                    .iter()
                    .filter(|test| !test.off().contains(&backend))
                    .cloned()
                    .collect(),
                options: options.clone(),
                backend,
            };
            backend
                .job_kind(BackendJobKind::NumberBackendJobs(context.tests.len()))
                .report_no_message();
            tokio::spawn(context.run()).await
        })
        .collect::<TryJoinAll<_>>()
        .await?
        .into_iter()
        .collect::<Result<Vec<_>>>()?;

    Ok(())
}
