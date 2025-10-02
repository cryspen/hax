use anyhow::{Context as _, Result, bail};
use hax_types::{
    cli_options::{BackendName, MessageFormat},
    diagnostics::message::HaxMessage,
};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

pub async fn haxmeta(flags: &[&str]) -> Result<PathBuf> {
    static PERMITS: tokio::sync::Semaphore = tokio::sync::Semaphore::const_new(1);
    let _permit = PERMITS.acquire().await?;
    let mut command = tokio::process::Command::new("cargo");
    command.args(["hax", "--message-format", "json", "serialize"]);
    command.args(flags);
    let out = command.output().await?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let raw_stdout = stdout.clone();
    let stderr = String::from_utf8_lossy(&out.stderr);
    let path = stdout
        .lines()
        .flat_map(|s| serde_json::from_str::<HaxMessage>(s))
        .find_map(|hax_message| match hax_message {
            HaxMessage::ProducedFile { path, .. } => Some(path.clone()),
            _ => None,
        })
        .with_context(|| format!("`{command:?}` produced no haxmeta file\n\n\nstderr={stderr}\n\n\nstdout={raw_stdout}"))?;
    Ok(path)
}

pub struct HaxEngineOutput {
    pub error_code: i32,
    pub messages: Vec<OutMsg>,
    pub stderr: String,
}

pub async fn hax_engine(
    haxmeta: &Path,
    test_module_name: &str,
    output_dir: &Path,
    backend: BackendName,
    into_flags: &[String],
    backend_flags: &[String],
) -> Result<HaxEngineOutput> {
    let mut command = tokio::process::Command::new("cargo");
    command.args(["hax", "--message-format", "json", "--haxmeta"]);
    command.arg(haxmeta);
    command.arg("into");
    command.arg("--output-dir");
    command.arg(output_dir);
    command.args(["--prune-haxmeta", test_module_name]);
    command.args(into_flags);
    command.arg(backend.to_string());
    command.args(backend_flags);
    let out = command.output().await?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    let messages = stdout
        .lines()
        .map(|s| {
            serde_json::from_str::<OutMsg>(s).unwrap_or_else(|_| OutMsg::Unknown(s.to_string()))
        })
        .collect();
    Ok(HaxEngineOutput {
        error_code: out.status.code().unwrap_or(0),
        messages,
        stderr,
    })
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(untagged)]
pub enum OutMsg {
    Cargo(cargo_metadata::CompilerMessage),
    Hax(HaxMessage),
    Unknown(String),
}

impl OutMsg {
    pub fn render(&self) -> Option<String> {
        match self {
            OutMsg::Cargo(compiler_message) => {
                Some(compiler_message.message.rendered.clone().unwrap())
            }
            OutMsg::Hax(hax_message) => hax_message.clone().render(MessageFormat::Human, None),
            OutMsg::Unknown(unknown) => Some(unknown.clone()),
        }
    }
}
