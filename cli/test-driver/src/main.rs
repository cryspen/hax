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
    collections::HashSet,
    env::set_current_dir,
    fs::{self},
    path::{Path, PathBuf},
    sync::{LazyLock, Mutex},
};

use anyhow::{Context as _, Result, bail};
use clap::Parser;
use futures::future::TryJoinAll;
use hax_frontend_exporter::DefId;
use hax_types::cli_options::BackendName;

use crate::{
    directives::{ErrorCode, FailureKind},
    test_module::{TestModule, compute_test_modules},
};

mod cli;
mod commands;
mod directives;
mod helpers;
mod log;
mod promote_directives;
mod span_hint;
mod test_module;

use commands::*;
use helpers::BackendNameExt;
use log::*;

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
        self.move_to_snapshots_directory(&out_dir).await?;
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

    /// Move the given output extraction directory to the canonical path the snapshots belongs to.
    async fn move_to_snapshots_directory(&self, out_dir: &Path) -> Result<()> {
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
        fs::rename(out_dir, &path_to_snapshots)?;
        helpers::delete_sourcemaps(&path_to_snapshots)?;
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

/// Backend disabled by default.
const DISABLED_BACKENDS: &'static [BackendName] = &[
    BackendName::Easycrypt,
    BackendName::Rust,
    BackendName::GenerateRustEngineNames,
];

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

    let backends: Vec<_> = BackendName::iter()
        .filter(|backend| !DISABLED_BACKENDS.contains(backend))
        .collect();

    let cache_dir = options.cache_dir();
    let _ = tokio::fs::create_dir_all(&cache_dir)
        .await
        .with_context(|| {
            format!(
                "Could not create the cache directory {}",
                cache_dir.display()
            )
        })?;

    let tests = JobKind::ResolveTests
        .run(|_| compute_test_modules())
        .await?;

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
