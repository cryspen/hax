//! Fixtures shared by the tool-management integration tests: fixture
//! archives, a local HTTP server to serve them, and the Cargo crates and
//! stub executables a run needs.
//!
//! `cargo-hax` is a binary crate, so its own `#[cfg(test)]` modules cannot
//! reach this and keep their own copies of what they need.

// Each integration test uses a subset of these.
#![allow(dead_code)]

use std::collections::HashMap;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
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

/// Run the `cargo-hax` binary under test with `args` in `current_dir`,
/// returning its combined stdout/stderr and whether it succeeded.
/// `HAX_TOOLS_MANIFEST` is scrubbed so the run sees the built-in manifest;
/// `envs` are set on top.
pub fn run_hax(args: &[&str], current_dir: &Path, envs: &[(&str, &str)]) -> (String, bool) {
    let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_cargo-hax"));
    cmd.args(args)
        .current_dir(current_dir)
        .env_remove("HAX_TOOLS_MANIFEST");
    for (var, value) in envs {
        cmd.env(var, value);
    }
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

/// A `hax.toml` `[tools]` table pointing charon and aeneas at the binaries
/// in `bin`.
pub fn path_entries(bin: &Path) -> String {
    format!(
        "[tools]\ncharon = {{ path = \"{}\" }}\naeneas = {{ path = \"{}\" }}\n",
        bin.join("charon").display(),
        bin.join("aeneas").display(),
    )
}

/// Stub executables for the whole pipeline in `bin`: marker-recording
/// charon and charon-driver stubs, and `aeneas_stub` as aeneas.
pub fn stub_pipeline_tools(bin: &Path, aeneas_stub: &str) {
    write_executable(&bin.join("charon"), &stub("charon-invoked"));
    write_executable(&bin.join("charon-driver"), &stub("driver-invoked"));
    write_executable(&bin.join("aeneas"), aeneas_stub);
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
