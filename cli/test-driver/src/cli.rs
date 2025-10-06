//! Command-line interface helpers.

use anyhow::{Result, bail};
use clap::Parser;
use std::{
    env::current_dir,
    fs::create_dir_all,
    path::{Path, PathBuf},
    sync::OnceLock,
};
use tokio::sync::{AcquireError, Semaphore, SemaphorePermit};

#[derive(Debug, Clone, Parser)]
/// Test driver for hax.
#[command(version, about, long_about = None)]
pub struct Cli {
    /// Root path of the crate that contains the integration tests.
    tests_crate_dir: PathBuf,
    /// Folder that stores intermediate artifacts produced by the
    /// driver.
    #[clap(long, short, default_value = current_dir().unwrap().join(".hax-tests-cache").into_os_string())]
    cache_dir: PathBuf,
    /// Maximum number of jobs that are allowed to execute concurrently.
    #[clap(long, short, default_value_t = num_cpus::get())]
    jobs: usize,
    /// Enabling this flag will add directives to the Rust source files so that
    /// the errors collected are marked as expected.
    /// This can be useful when adding a new backend to hax.
    #[clap(long)]
    promote_directives: bool,
}

impl Cli {
    pub fn canonicalize(&mut self) -> Result<()> {
        self.prepare_folders()?;
        self.tests_crate_dir = self.tests_crate_dir.canonicalize()?;
        self.cache_dir = self.cache_dir.canonicalize()?;
        Ok(())
    }

    /// Returns the root of the crate that contains the integration tests.
    pub fn tests_crate_dir(&self) -> PathBuf {
        self.tests_crate_dir.canonicalize().unwrap()
    }
    /// Returns the folder that stores intermediate artifacts produced by the
    /// driver.
    pub fn cache_dir(&self) -> &Path {
        &self.cache_dir
    }
    /// Maximum number of jobs that are allowed to execute concurrently.
    pub fn jobs(&self) -> usize {
        self.jobs
    }

    pub fn promote_directives(&self) -> bool {
        self.promote_directives
    }

    /// Acquires a permit from the shared semaphore that limits concurrency.
    #[must_use]
    pub async fn semaphore_permit_for_test<'a>(
        &'a self,
    ) -> Result<SemaphorePermit<'a>, AcquireError> {
        static SEMAPHORE: OnceLock<Semaphore> = OnceLock::new();
        SEMAPHORE
            .get_or_init(|| Semaphore::new(self.jobs()))
            .acquire()
            .await
    }

    /// Creates the folder structure that the driver relies upon before running
    /// any work.
    pub fn prepare_folders(&self) -> Result<()> {
        if !self.tests_crate_dir().exists() {
            bail!("The test crate provided doesn't exist")
        }
        create_dir_all(self.cache_dir())?;
        Ok(())
    }
}
