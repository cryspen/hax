//! Fixtures shared by the tool-management integration tests: fixture
//! archives, a local HTTP server to serve them, the Cargo crates and stub
//! executables a run needs, and how the binary is invoked.
//!
//! `cargo-hax` is a binary crate, so its own `#[cfg(test)]` modules cannot
//! reach this and keep their own copies of what they need.

// Each integration test uses a subset of these.
#![allow(dead_code)]

use std::collections::HashMap;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use sha2::Digest;

/// The manifest platform key of the host, as the binary under test computes
/// it.
pub fn platform() -> String {
    format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH)
}

/// Build a gzipped tar archive holding the given (path, contents) files,
/// each executable.
pub fn make_archive(files: &[(&str, &str)]) -> Vec<u8> {
    let mut builder = tar::Builder::new(flate2::write::GzEncoder::new(
        Vec::new(),
        flate2::Compression::fast(),
    ));
    for (path, contents) in files {
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(0o755);
        header.set_cksum();
        builder
            .append_data(&mut header, path, contents.as_bytes())
            .unwrap();
    }
    builder.into_inner().unwrap().finish().unwrap()
}

pub fn sha256_hex(data: &[u8]) -> String {
    hex::encode(sha2::Sha256::digest(data))
}

/// A fixture HTTP server serving a fixed set of paths.
pub struct Server {
    pub base_url: String,
    _handle: std::thread::JoinHandle<()>,
}

pub fn serve(files: HashMap<String, Vec<u8>>) -> Server {
    let server = tiny_http::Server::http("127.0.0.1:0").unwrap();
    let port = server.server_addr().to_ip().unwrap().port();
    let files = Arc::new(files);
    let handle = std::thread::spawn(move || {
        for request in server.incoming_requests() {
            let url = request.url().to_string();
            match files.get(&url) {
                Some(data) => request
                    .respond(tiny_http::Response::from_data(data.clone()))
                    .unwrap(),
                None => request.respond(tiny_http::Response::empty(404)).unwrap(),
            }
        }
    });
    Server {
        base_url: format!("http://127.0.0.1:{port}"),
        _handle: handle,
    }
}

/// A shell-script stub that records its invocation in the working directory
/// and exits successfully.
pub fn stub(marker: &str) -> String {
    format!("#!/bin/sh\necho \"$@\" > {marker}\nexit 0\n")
}

pub fn write_executable(path: &Path, contents: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, contents).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
}

/// A minimal library crate named `name` at `dir`.
pub fn write_crate(dir: &Path, name: &str) {
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n"),
    )
    .unwrap();
    std::fs::write(dir.join("src/lib.rs"), "").unwrap();
}

/// Stub charon, the sibling driver it needs, and aeneas in `bin`, each
/// recording its invocation in the working directory.
pub fn write_tool_stubs(bin: &Path) {
    for (name, marker) in [
        ("charon", "charon-invoked"),
        ("charon-driver", "driver-invoked"),
        ("aeneas", "aeneas-invoked"),
    ] {
        write_executable(&bin.join(name), &stub(marker));
    }
}

/// Point a crate's `hax.toml` at the charon and aeneas binaries in `bin`.
pub fn write_path_entries(crate_dir: &Path, bin: &Path) {
    std::fs::write(
        crate_dir.join("hax.toml"),
        format!(
            "[tools]\ncharon = {{ path = \"{}\" }}\naeneas = {{ path = \"{}\" }}\n",
            bin.join("charon").display(),
            bin.join("aeneas").display(),
        ),
    )
    .unwrap();
}

/// The `cargo-hax` these tests build.
pub fn cargo_hax() -> PathBuf {
    env!("CARGO_BIN_EXE_cargo-hax").into()
}

/// A `cargo-hax` invocation, deaf to a tool manifest the ambient environment
/// may point at.
pub fn command(binary: &Path, args: &[&str], current_dir: &Path) -> Command {
    let mut cmd = Command::new(binary);
    cmd.args(args)
        .current_dir(current_dir)
        .env_remove("HAX_TOOLS_MANIFEST");
    cmd
}

/// Run `cmd` to completion, returning its interleaved output and whether it
/// succeeded. Interleaved because which stream a message takes is not what
/// these tests are about.
pub fn output_of(cmd: &mut Command) -> (String, bool) {
    let output = cmd.output().unwrap();
    (
        format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
        output.status.success(),
    )
}
