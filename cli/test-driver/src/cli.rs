use anyhow::{Context as _, Result, bail};
use clap::{Parser, Subcommand};
use std::{
    env::current_dir,
    fs::create_dir_all,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, Parser)]
#[command(version, about, long_about = None)]
pub struct Cli {
    tests_crate_dir: PathBuf,
    #[clap(long, short, default_value = current_dir().unwrap().join(".hax-tests-cache").into_os_string())]
    cache_dir: PathBuf,
    #[clap(long, short)]
    snapshot_dir: Option<PathBuf>,
    #[clap(long, short, default_value_t = num_cpus::get())]
    jobs: usize,
}

impl Cli {
    pub fn tests_crate_dir(&self) -> &Path {
        &self.tests_crate_dir
    }
    pub fn cache_dir(&self) -> &Path {
        &self.cache_dir
    }
    pub fn snapshot_dir(&self) -> PathBuf {
        self.snapshot_dir
            .clone()
            .unwrap_or_else(|| self.tests_crate_dir.join("snapshots"))
    }
    pub fn jobs(&self) -> usize {
        self.jobs
    }

    pub fn prepare_folders(&self) -> Result<()> {
        if !self.tests_crate_dir().exists() {
            bail!("The test crate provided doesn't exist")
        }
        create_dir_all(self.cache_dir())?;
        create_dir_all(self.snapshot_dir())?;
        Ok(())
    }
}
