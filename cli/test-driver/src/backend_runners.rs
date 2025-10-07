use anyhow::Result;
use hax_types::cli_options::BackendName;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

use crate::{directives::ErrorCode, log::JobKind};

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Input {
    pub directives: Vec<String>,
    pub hax_root: PathBuf,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct LineRange {
    pub start: usize,
    pub end: Option<usize>,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Error {
    pub error_code: ErrorCode,
    // pub file: Option<PathBuf>,
    // pub line_range: Option<LineRange>,
    pub rendered: String,
}

#[derive(Clone, Copy, Debug)]
pub struct Runner {
    command_path: &'static Path,
}

impl Runner {
    pub async fn run(
        &self,
        job: &JobKind,
        dir: &Path,
        directives: Vec<String>,
    ) -> Result<Vec<Error>> {
        let input = Input {
            directives,
            hax_root: PathBuf::from("/Users/lucasfranceschino/repos/hax/test-framework"),
        };
        crate::helpers::run_json_command(Some(job), &self.command_path, &[], &dir, &input).await
    }
}

// trait BackendRunner {
//     fn run(&self, input: Input) -> Output;
// }

// pub async fn runner(backend: BackendName) -> Option<Box<dyn BackendRunner>> {
//     None
// }

// async fn find_command(name: &str) -> PathBuf {}

pub fn run(backend: BackendName) -> Option<Runner> {
    match backend {
        BackendName::Fstar => Some(Runner {
            command_path: Path::new(
                "/Users/lucasfranceschino/repos/hax/test-framework/cli/test-driver/backend-runners/fstar.sh",
            ),
        }),
        _ => None,
    }
}

// pub fn run(
//     job: JobKind,
//     backend: BackendName,
//     dir: &Path,
//     // input: Input,
// ) -> Option<Box<dyn Future<Output = Result<Output>>>> {
//     let dir = dir.to_path_buf();
//     match backend {
//         BackendName::Fstar => Some(Box::new(async move {
//             crate::helpers::run_json_command(
//             Some(job),
//             "/Users/lucasfranceschino/repos/hax/test-framework/cli/test-driver/backend-runners/fstar.sh",
//             &[],
//             &dir,
//             &input,
//         ).await
//         })),
//         _ => None,
//         // BackendName::Coq => todo!(),
//         // BackendName::Ssprove => todo!(),
//         // BackendName::Easycrypt => todo!(),
//         // BackendName::ProVerif => todo!(),
//         // BackendName::Lean => todo!(),
//         // BackendName::Rust => todo!(),
//         // BackendName::GenerateRustEngineNames => todo!(),
//     }
// }
