//! Orchestrates the execution of Hax backend integration tests.
//!
//! The binary discovers test modules, spawns extraction jobs for each enabled
//! backend, and reconciles the diagnostics that were observed with the
//! directives encoded in the test sources.

#![feature(rustc_private)]
#![warn(
    rustdoc::broken_intra_doc_links,
    unused_qualifications,
    unused_crate_dependencies
)]

use std::{
    collections::{HashMap, HashSet},
    env::set_current_dir,
    fs::{self},
    path::{Path, PathBuf},
    sync::{LazyLock, Mutex},
};

use anyhow::{Context as _, Result, bail};
use clap::Parser;
use futures::future::TryJoinAll;
use hax_frontend_exporter::{DefId, DefKind};
use hax_types::{cli_options::BackendName, driver_api::HaxMeta};

use crate::directives::{Directive, ErrorCode, FailureKind, ItemDirective, TestDirective};

mod cli;
mod commands;
mod directives;
mod helpers;
mod log;
mod promote_directives;
mod span_hint;

use commands::*;
use helpers::BackendNameExt;
use log::*;

#[derive(Clone, Debug)]
/// Representation of a test module extracted from the Hax metadata.
struct TestModule {
    module_name: String,
    module_path: PathBuf,
    def_id: DefId,
    test_directives: Vec<TestDirective>,
    items: Vec<(DefId, Vec<ItemDirective>)>,
}

impl TestModule {
    /// Returns the diagnostics that should be emitted for the provided backend
    /// and failure kind.
    fn expected_diagnostics(
        &self,
        backend: BackendName,
        kind: FailureKind,
    ) -> Vec<(DefId, ErrorCode)> {
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
    /// Ensures that the iterator produces at most one element.
    fn expect_le_one(mut self) -> Result<Option<T>> {
        match (self.next(), self.next()) {
            (None, None) => Ok(None),
            (Some(first), None) => Ok(Some(first)),
            _ => bail!("expect_one_or_less: got 2 or more"),
        }
    }
}

impl TestModule {
    /// Resolves the optional `@cli` directive attached to the module.
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
    /// Returns the set of backends disabled for this module.
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

/// Builds the in-memory representation of every test module present in the
/// serialized Hax metadata.
async fn collect() -> Result<Vec<TestModule>> {
    let (haxmeta, _): (HaxMeta<()>, _) =
        HaxMeta::read(fs::File::open(&hax_serialize(&["--kind"]).await?)?);

    span_hint::init(&haxmeta.items)?;

    let map = haxmeta
        .items
        .iter()
        .map(|item| {
            let directives = item
                .attributes
                .attributes
                .iter()
                .map(|attr| directives::directive_of_attribute(attr))
                .collect::<Result<Vec<Option<_>>>>()?
                .into_iter()
                .flatten();
            Ok((item.owner_id.clone(), directives))
        })
        .collect::<Result<Vec<_>>>()?;
    let mut tests: HashMap<String, TestModule> = HashMap::new();
    let mut items: HashMap<String, Vec<_>> = HashMap::new();
    for (def_id, directives) in map {
        let Some(module_name) = helpers::module_name(&def_id) else {
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
            if def_id.kind != DefKind::Mod {
                continue;
            }
            let module_path = span_hint::span_hint(&def_id)
                .await?
                .context("internal error: every test module item should have a span hint")?;

            let module_path = module_path
                .module_file
                .clone()
                .with_context(|| format!("internal error: every test module item should have a `module_file`. Found none for {:?}.", helpers::string_of_def_id(&def_id)))?.canonicalize()
                .context("internal error: cannot canonicalize module path")?;

            tests.insert(
                module_name.clone(),
                TestModule {
                    items: vec![(def_id.clone(), item_directives)],
                    def_id,
                    module_name,
                    module_path,
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
        let test_module = tests
            .get_mut(&module_name)
            .expect("Loop above is supposed to populate `tests` correctly");
        for (def_id, directives) in items {
            test_module.items.push((def_id, directives))
        }
    }

    Ok(tests.into_values().collect())
}

#[derive(Clone, Debug)]
/// Snapshot of the context necessary to run all tests for one backend.
struct BackendTestsContext {
    tests: Vec<TestModule>,
    backend: BackendName,
    options: cli::Cli,
}

#[derive(Clone, Debug)]
/// Per-test execution context.
struct BackendTestContext {
    test: TestModule,
    backend: BackendName,
    options: cli::Cli,
    haxmeta: PathBuf,
}

impl BackendTestContext {
    /// Executes the full backend workflow for a single test module.
    async fn run(self) -> Result<()> {
        let _permit = self.options.semaphore_permit_for_test().await?;
        let out_dir = self
            .backend
            .job_kind(BackendJobKind::CargoHaxInto {
                test: self.test.module_name.to_string(),
            })
            .run(async |job| self.run_inner(job).await)
            .await?;
        self.snapshots(&out_dir).await?;
        Ok(())
    }

    /// Invokes `cargo hax into` for the current backend.
    async fn call_engine(&self, job: JobKind, out_dir: &Path) -> Result<HaxEngineOutput> {
        let (into_flags, backend_flags) = self.test.cli(self.backend)?;
        let output = hax_engine(
            &self.haxmeta,
            &self.test.module_name,
            &out_dir,
            self.backend,
            &into_flags[..],
            &backend_flags[..],
        )
        .await?;
        output.report_stderr_and_stdout(job);
        Ok(output)
    }

    /// Writes diagnostics for the job and converts unexpected/missing
    /// diagnostics into user-facing errors.
    async fn report_results(
        &self,
        job: JobKind,
        exit_status: i32,
        unexpected_diagnostics: Diagnostics,
        missing_expected_diagnostics: Vec<(DefId, ErrorCode)>,
    ) -> Result<()> {
        let unexpected_diagnostics = unexpected_diagnostics
            .iter()
            .flat_map(OutMsg::render)
            .collect::<Vec<_>>();

        for rendered in &unexpected_diagnostics {
            job.report_message(rendered);
        }
        for (did, error_code) in &missing_expected_diagnostics {
            // TODO: add precise directive span, display nice error message
            job.report_message(format!(
                "expected error {error_code} on item `{did}`, got none",
                did = helpers::string_of_def_id(did)
            ));
        }

        const ERROR: bool = false;
        match (
            unexpected_diagnostics.is_empty(),
            missing_expected_diagnostics.is_empty(),
            exit_status == 0,
        ) {
            (ERROR, ERROR, _) => {
                bail!(
                    "unexpected extraction failure(s), and expected extraction failure(s) not found"
                )
            }
            (ERROR, _, _) => bail!("unexpected extraction failure(s)"),
            (_, ERROR, _) => bail!("expected extraction failure(s) not found"),
            _ => Ok(()),
        }
    }

    async fn snapshots(&self, out_dir: &Path) -> Result<()> {
        static DIRS: LazyLock<Mutex<HashSet<PathBuf>>> =
            LazyLock::new(|| Mutex::new(HashSet::new()));

        let relative_path_to_test = self
            .test
            .module_path
            .strip_prefix(self.options.tests_crate_dir().join("src"))
            .context("internal error, cannot figure out relative path of test module")?;
        let relative_path_to_test = relative_path_to_test.with_file_name(
            relative_path_to_test
                .file_stem()
                .context("internal error, test module has no `*.rs` extension?")?,
        );
        let path_to_snapshots = self
            .options
            .tests_crate_dir()
            .join("snapshots")
            .join(relative_path_to_test)
            .join(self.backend.to_string());

        if !DIRS.lock().unwrap().insert(path_to_snapshots.clone()) {
            panic!(
                "Internal error: we are trying to output twice to {}",
                path_to_snapshots.display(),
            )
        }

        if path_to_snapshots.exists() {
            fs::remove_dir_all(&path_to_snapshots)?
        }
        fs::create_dir_all(path_to_snapshots.parent().unwrap())?;

        fs::rename(out_dir, path_to_snapshots)?;

        Ok(())
    }

    async fn run_inner(&self, job: JobKind) -> Result<PathBuf> {
        let out_dir = self
            .options
            .cache_dir()
            .join(&self.test.module_name)
            .join(self.backend.to_string());
        if out_dir.exists() {
            fs::remove_dir_all(&out_dir)?;
        }
        fs::create_dir_all(&out_dir)?;

        let engine_out = self.call_engine(job.clone(), &out_dir).await?;

        let mut diagnostics = engine_out.diagnostics();
        if engine_out.error_code != 0 && diagnostics.iter().next().is_none() {
            bail!(
                "the engine ended with a non-null exit code, but no diagnostic could be found. See stdout and stderr."
            )
        }

        let (unexpected_diagnostics, missing_expected_diagnostics) = {
            let missing_expected_diagnostics: Vec<_> = self
                .test
                .expected_diagnostics(self.backend, FailureKind::Extract)
                .into_iter()
                .filter(|(diag, error_code)| diagnostics.remove(diag, error_code).is_none())
                .collect();
            (diagnostics, missing_expected_diagnostics)
        };

        if self.options.promote_directives() {
            unexpected_diagnostics
                .add_directives_in_files(self.backend, &self.test.def_id)
                .await?;
        }

        self.report_results(
            job,
            engine_out.error_code,
            unexpected_diagnostics,
            missing_expected_diagnostics,
        )
        .await?;
        Ok(out_dir)
    }
}

impl BackendTestsContext {
    /// Compute the haxmeta for this backend.
    async fn haxmeta(&self) -> Result<PathBuf> {
        self.backend
            .job_kind(BackendJobKind::CargoHaxSerialize)
            .run(|_| async {
                let original_path =
                    hax_serialize(&["-b", self.backend.to_string().as_str()]).await?;
                let path = self
                    .options
                    .cache_dir()
                    .join(format!("{}.haxmeta", self.backend));
                tokio::fs::rename(original_path, &path).await?;
                Ok(path)
            })
            .await
    }
    /// Executes every test module for the backend.
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
    let mut options = cli::Cli::parse();
    options.canonicalize()?;
    set_current_dir(options.tests_crate_dir()).with_context(|| {
        format!(
            "Could not change directory to {}",
            options.tests_crate_dir().display()
        )
    })?;

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
    let _ = tokio::fs::create_dir_all(&cache_dir)
        .await
        .with_context(|| {
            format!(
                "Could not create the cache directory {}",
                cache_dir.display()
            )
        })?;

    let tests = JobKind::ResolveTests.run(|_| collect()).await?;

    let result = backends
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
        .collect::<Result<Vec<_>>>();

    promote_directives::save()?;
    result?;

    Ok(())
}
