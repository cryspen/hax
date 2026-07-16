//! End-to-end tests for the lean backend's tool resolution: path
//! overrides with the sibling rule, and on-demand installs from `hax.toml`
//! pins, exercised through the real binary with stub charon/aeneas
//! executables.

use std::collections::HashMap;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use sha2::Digest;

/// A shell-script stub that records its invocation in the working
/// directory and exits successfully.
fn stub(marker: &str) -> String {
    format!("#!/bin/sh\necho \"$@\" > {marker}\nexit 0\n")
}

fn write_executable(path: &Path, contents: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, contents).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
}

fn write_crate(dir: &Path) {
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    std::fs::write(dir.join("src/lib.rs"), "").unwrap();
}

fn run_backend(crate_dir: &Path, envs: &[(&str, &str)]) -> (String, bool) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-hax"));
    cmd.args(["into", "lean"]).current_dir(crate_dir);
    for var in [
        "HAX_AENEAS_BINARY",
        "HAX_CHARON_BINARY",
        "HAX_TOOLS_MANIFEST",
    ] {
        cmd.env_remove(var);
    }
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

#[test]
fn path_override_runs_the_supplied_binaries_with_a_notice() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = dir.path().join("crate");
    write_crate(&crate_dir);
    let bin = dir.path().join("bin");
    write_executable(&bin.join("charon"), &stub("charon-invoked"));
    write_executable(&bin.join("charon-driver"), &stub("driver-invoked"));
    write_executable(&bin.join("aeneas"), &stub("aeneas-invoked"));

    let (output, success) = run_backend(
        &crate_dir,
        &[
            ("HAX_CHARON_BINARY", bin.join("charon").to_str().unwrap()),
            ("HAX_AENEAS_BINARY", bin.join("aeneas").to_str().unwrap()),
        ],
    );
    assert!(success, "{output}");
    // The stubs ran (charon records in the crate dir, aeneas too).
    assert!(crate_dir.join("charon-invoked").is_file(), "{output}");
    assert!(crate_dir.join("aeneas-invoked").is_file(), "{output}");
    // The non-default notice names both paths.
    assert!(output.contains("was tested with"), "{output}");
    assert!(
        output.contains(bin.join("charon").to_str().unwrap()),
        "{output}"
    );
}

#[test]
fn missing_sibling_executable_is_a_clear_error() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = dir.path().join("crate");
    write_crate(&crate_dir);
    let bin = dir.path().join("bin");
    // charon without charon-driver next to it.
    write_executable(&bin.join("charon"), &stub("charon-invoked"));
    write_executable(&bin.join("aeneas"), &stub("aeneas-invoked"));

    let (output, success) = run_backend(
        &crate_dir,
        &[
            ("HAX_CHARON_BINARY", bin.join("charon").to_str().unwrap()),
            ("HAX_AENEAS_BINARY", bin.join("aeneas").to_str().unwrap()),
        ],
    );
    assert!(!success);
    assert!(output.contains("charon-driver"), "{output}");
    assert!(output.contains("was not found next to"), "{output}");
}

#[test]
fn hax_toml_pin_installs_on_demand_and_runs_from_the_cache() {
    // Fixture archives holding executable stubs.
    let make_archive = |files: &[(&str, &str)]| -> Vec<u8> {
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
    };
    let charon = make_archive(&[
        ("charon", &stub("charon-invoked")),
        ("charon-driver", &stub("driver-invoked")),
    ]);
    let aeneas = make_archive(&[("aeneas", &stub("aeneas-invoked"))]);
    let (charon_sha, aeneas_sha) = (
        hex::encode(sha2::Sha256::digest(&charon)),
        hex::encode(sha2::Sha256::digest(&aeneas)),
    );

    let server = tiny_http::Server::http("127.0.0.1:0").unwrap();
    let port = server.server_addr().to_ip().unwrap().port();
    let files = Arc::new(HashMap::from([
        ("/charon.tar.gz".to_string(), charon),
        ("/aeneas.tar.gz".to_string(), aeneas),
    ]));
    std::thread::spawn(move || {
        for request in server.incoming_requests() {
            match files.get(request.url()) {
                Some(data) => request
                    .respond(tiny_http::Response::from_data(data.clone()))
                    .unwrap(),
                None => request.respond(tiny_http::Response::empty(404)).unwrap(),
            }
        }
    });

    let platform = format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH);
    let dir = tempfile::tempdir().unwrap();
    let manifest_path: PathBuf = dir.path().join("manifest.toml");
    std::fs::write(
        &manifest_path,
        format!(
            r#"[tools.charon."stub-v1".{platform}]
url = "http://127.0.0.1:{port}/charon.tar.gz"
sha256 = "{charon_sha}"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}

[tools.aeneas."stub-v1".{platform}]
url = "http://127.0.0.1:{port}/aeneas.tar.gz"
sha256 = "{aeneas_sha}"
entry_points = {{ aeneas = "aeneas" }}
"#
        ),
    )
    .unwrap();
    let cache = dir.path().join("cache");
    std::fs::create_dir(&cache).unwrap();

    let crate_dir = dir.path().join("crate");
    write_crate(&crate_dir);
    std::fs::write(
        crate_dir.join("hax.toml"),
        "[tools]\ncharon = \"stub-v1\"\naeneas = \"stub-v1\"\n",
    )
    .unwrap();

    let (output, success) = run_backend(
        &crate_dir,
        &[
            ("HAX_TOOLS_MANIFEST", manifest_path.to_str().unwrap()),
            ("XDG_CACHE_HOME", cache.to_str().unwrap()),
        ],
    );
    assert!(success, "{output}");
    // Downloaded on demand, with the note and the non-default notice.
    assert!(output.contains("Downloading charon stub-v1"), "{output}");
    assert!(output.contains("was tested with"), "{output}");
    // The cached stubs actually ran.
    assert!(crate_dir.join("charon-invoked").is_file(), "{output}");
    assert!(crate_dir.join("aeneas-invoked").is_file(), "{output}");
    // The cache holds both tools.
    assert!(cache.join("hax/tools/charon/stub-v1/charon").is_file());
    assert!(cache.join("hax/tools/aeneas/stub-v1/aeneas").is_file());

    // A second run is a pure cache hit: no download note.
    std::fs::remove_file(crate_dir.join("charon-invoked")).unwrap();
    let (output, success) = run_backend(
        &crate_dir,
        &[
            ("HAX_TOOLS_MANIFEST", manifest_path.to_str().unwrap()),
            ("XDG_CACHE_HOME", cache.to_str().unwrap()),
        ],
    );
    assert!(success, "{output}");
    assert!(!output.contains("Downloading"), "{output}");
    assert!(crate_dir.join("charon-invoked").is_file());
}

#[test]
fn lakefile_pins_come_from_the_resolved_versions() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = dir.path().join("crate");
    write_crate(&crate_dir);
    std::fs::write(
        crate_dir.join("hax.toml"),
        r#"[versions]
lean = "leanprover/lean4:v9.9.9-test"
hax-lean-lib = "v9.9.9"
"#,
    )
    .unwrap();
    let bin = dir.path().join("bin");
    write_executable(&bin.join("charon"), &stub("charon-invoked"));
    write_executable(&bin.join("charon-driver"), &stub("driver-invoked"));
    write_executable(&bin.join("aeneas"), &stub("aeneas-invoked"));

    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-hax"));
    cmd.args(["into", "lean", "--lakefile"])
        .current_dir(&crate_dir)
        .env("HAX_CHARON_BINARY", bin.join("charon"))
        .env("HAX_AENEAS_BINARY", bin.join("aeneas"))
        .env_remove("HAX_TOOLS_MANIFEST");
    let output = cmd.output().unwrap();
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "{all}");

    let lean_dir = crate_dir.join("proofs/lean");
    let toolchain = std::fs::read_to_string(lean_dir.join("lean-toolchain")).unwrap();
    assert_eq!(toolchain.trim(), "leanprover/lean4:v9.9.9-test");
    let lakefile = std::fs::read_to_string(lean_dir.join("lakefile.toml")).unwrap();
    assert!(lakefile.contains("rev = \"v9.9.9\""), "{lakefile}");
    // aeneas resolves to a path: the lakefile pins the default rev, with
    // a warning naming the substitution.
    assert!(all.contains("pinning the aeneas Lean library"), "{all}");
}
