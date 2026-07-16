//! End-to-end tests for `cargo hax tools install` and `list`: the
//! download-verify-extract-cache pipeline, exercised through the real
//! binary against a local HTTP server serving fixture archives, with the
//! manifest injected via the internal `HAX_TOOLS_MANIFEST` override and
//! the cache redirected via `XDG_CACHE_HOME`.

use std::collections::HashMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use sha2::Digest;

fn platform() -> String {
    format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH)
}

/// Build a gzipped tar archive holding the given (path, contents) files.
fn make_archive(files: &[(&str, &str)]) -> Vec<u8> {
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

fn sha256_hex(data: &[u8]) -> String {
    hex::encode(sha2::Sha256::digest(data))
}

/// A fixture HTTP server serving a fixed set of paths.
struct Server {
    base_url: String,
    _handle: std::thread::JoinHandle<()>,
}

fn serve(files: HashMap<String, Vec<u8>>) -> Server {
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

/// A test environment: manifest file, cache dir, and helpers to run the
/// binary with the right overrides.
struct Env {
    dir: tempfile::TempDir,
}

impl Env {
    fn new(manifest: &str) -> Self {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("manifest.toml"), manifest).unwrap();
        std::fs::create_dir(dir.path().join("cache")).unwrap();
        Env { dir }
    }

    fn cache(&self) -> PathBuf {
        self.dir.path().join("cache")
    }

    fn command(&self, args: &[&str], current_dir: Option<&Path>) -> Command {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-hax"));
        cmd.args(args)
            .env("HAX_TOOLS_MANIFEST", self.dir.path().join("manifest.toml"))
            .env("XDG_CACHE_HOME", self.cache())
            .current_dir(current_dir.unwrap_or(self.dir.path()));
        for var in ["HAX_AENEAS_BINARY", "HAX_CHARON_BINARY"] {
            cmd.env_remove(var);
        }
        cmd
    }

    fn run(&self, args: &[&str]) -> (String, bool) {
        let output = self.command(args, None).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        (format!("{stdout}{stderr}"), output.status.success())
    }

    fn version_dir(&self, tool: &str, version: &str) -> PathBuf {
        self.cache().join("hax/tools").join(tool).join(version)
    }
}

#[test]
fn install_downloads_verifies_and_caches() {
    let archive = make_archive(&[("charon", "#!/bin/sh\n"), ("charon-driver", "#!/bin/sh\n")]);
    let sha = sha256_hex(&archive);
    let server = serve(HashMap::from([("/charon-v1.tar.gz".to_string(), archive)]));
    let env = Env::new(&format!(
        r#"[tools.charon."v1".{platform}]
url = "{base}/charon-v1.tar.gz"
sha256 = "{sha}"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}
"#,
        platform = platform(),
        base = server.base_url,
    ));

    let (output, success) = env.run(&["tools", "install", "charon@v1"]);
    assert!(success, "{output}");
    assert!(output.contains("Installed charon v1"), "{output}");

    let dir = env.version_dir("charon", "v1");
    assert!(dir.join("charon").is_file());
    assert!(dir.join("charon-driver").is_file());
    let metadata = std::fs::read_to_string(dir.join("hax-metadata.toml")).unwrap();
    assert!(metadata.contains("checksum_verified = true"), "{metadata}");
    assert!(metadata.contains("source_url"), "{metadata}");

    // A second install is a cache hit, without touching the server.
    let (output, success) = env.run(&["tools", "install", "charon@v1"]);
    assert!(success);
    assert!(output.contains("Cached charon v1"), "{output}");

    // And `list` marks it as installed, without an `unverified` note since
    // the checksum was verified.
    let (output, success) = env.run(&["tools", "list", "charon"]);
    assert!(success);
    assert!(output.contains("v1  (installed)"), "{output}");
    assert!(!output.contains("unverified"), "{output}");
}

#[test]
fn force_reinstalls_a_cached_version() {
    let archive = make_archive(&[("charon", ""), ("charon-driver", "")]);
    let server = serve(HashMap::from([(
        "/charon-v1.tar.gz".to_string(),
        archive.clone(),
    )]));
    let env = Env::new(&format!(
        r#"[tools.charon."v1".{platform}]
url = "{base}/charon-v1.tar.gz"
sha256 = "{sha}"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}
"#,
        platform = platform(),
        base = server.base_url,
        sha = sha256_hex(&archive),
    ));

    let (output, success) = env.run(&["tools", "install", "charon@v1"]);
    assert!(success, "{output}");
    assert!(output.contains("Installed charon v1"), "{output}");

    // Without --force, a second install is a cache hit.
    let (output, _) = env.run(&["tools", "install", "charon@v1"]);
    assert!(output.contains("Cached charon v1"), "{output}");

    // With --force, it re-downloads and verifies again, and the install
    // is intact after the swap.
    let (output, success) = env.run(&["tools", "install", "charon@v1", "--force"]);
    assert!(success, "{output}");
    assert!(output.contains("Installed charon v1"), "{output}");
    assert!(!output.contains("Cached charon v1"), "{output}");
    assert!(
        env.version_dir("charon", "v1").join("charon").is_file(),
        "{output}"
    );
    assert!(
        env.version_dir("charon", "v1")
            .join("charon-driver")
            .is_file(),
        "{output}"
    );
}

#[test]
fn checksum_mismatch_aborts_without_caching() {
    let archive = make_archive(&[("charon", ""), ("charon-driver", "")]);
    let server = serve(HashMap::from([("/charon-v1.tar.gz".to_string(), archive)]));
    let env = Env::new(&format!(
        r#"[tools.charon."v1".{platform}]
url = "{base}/charon-v1.tar.gz"
sha256 = "{bad}"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}
"#,
        platform = platform(),
        base = server.base_url,
        bad = "0".repeat(64),
    ));

    let (output, success) = env.run(&["tools", "install", "charon@v1"]);
    assert!(!success);
    assert!(output.contains("checksum mismatch"), "{output}");
    assert!(!env.version_dir("charon", "v1").exists());
    // No partial or temporary directories survive.
    let tool_dir = env.cache().join("hax/tools/charon");
    let leftovers: Vec<_> = std::fs::read_dir(&tool_dir)
        .map(|entries| entries.flatten().collect())
        .unwrap_or_default();
    assert!(leftovers.is_empty(), "{leftovers:?}");
}

#[test]
fn unknown_version_goes_through_the_warned_fallback() {
    let archive = make_archive(&[("charon", ""), ("charon-driver", "")]);
    let server = serve(HashMap::from([(
        "/nightly-9/charon-nightly-9.tar.gz".to_string(),
        archive,
    )]));
    let env = Env::new(&format!(
        r#"[fallback.charon.{platform}]
url = "{base}/{{version}}/charon-{{version}}.tar.gz"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}
"#,
        platform = platform(),
        base = server.base_url,
    ));

    let (output, success) = env.run(&["tools", "install", "charon@nightly-9"]);
    assert!(success, "{output}");
    assert!(
        output.contains("not known to this cargo-hax release"),
        "{output}"
    );
    assert!(output.contains("without checksum verification"), "{output}");
    assert!(
        output.contains("Installed charon nightly-9 (unverified)"),
        "{output}"
    );
    let metadata = std::fs::read_to_string(
        env.version_dir("charon", "nightly-9")
            .join("hax-metadata.toml"),
    )
    .unwrap();
    assert!(metadata.contains("checksum_verified = false"), "{metadata}");

    // `list` flags the cached fallback version as outside the manifest.
    let (output, _) = env.run(&["tools", "list", "charon"]);
    assert!(
        output.contains("nightly-9  (installed, unverified, not in manifest)"),
        "{output}"
    );

    // A version the server does not have: a 404 naming the URL.
    let (output, success) = env.run(&["tools", "install", "charon@nightly-10"]);
    assert!(!success);
    assert!(output.contains("404"), "{output}");
    assert!(output.contains("charon-nightly-10.tar.gz"), "{output}");
}

#[test]
fn platform_without_artifact_names_the_escape_hatch() {
    let env = Env::new("");
    let (output, success) = env.run(&["tools", "install", "charon@v1"]);
    assert!(!success);
    assert!(output.contains("HAX_CHARON_BINARY"), "{output}");
}

#[test]
fn bin_convention_needs_no_entry_points() {
    let archive = make_archive(&[("bin/aeneas", "")]);
    let sha = sha256_hex(&archive);
    let server = serve(HashMap::from([("/aeneas.tar.gz".to_string(), archive)]));
    let env = Env::new(&format!(
        r#"[tools.aeneas."v1".{platform}]
url = "{base}/aeneas.tar.gz"
sha256 = "{sha}"
"#,
        platform = platform(),
        base = server.base_url,
    ));
    let (output, success) = env.run(&["tools", "install", "aeneas@v1"]);
    assert!(success, "{output}");
    assert!(env.version_dir("aeneas", "v1").join("bin/aeneas").is_file());
}

#[test]
fn archive_missing_an_executable_fails_cleanly() {
    // The archive lacks charon-driver: entry-point validation must reject
    // the install and leave no cache entry.
    let archive = make_archive(&[("charon", "")]);
    let sha = sha256_hex(&archive);
    let server = serve(HashMap::from([("/charon.tar.gz".to_string(), archive)]));
    let env = Env::new(&format!(
        r#"[tools.charon."v1".{platform}]
url = "{base}/charon.tar.gz"
sha256 = "{sha}"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}
"#,
        platform = platform(),
        base = server.base_url,
    ));
    let (output, success) = env.run(&["tools", "install", "charon@v1"]);
    assert!(!success);
    assert!(output.contains("charon-driver"), "{output}");
    assert!(!env.version_dir("charon", "v1").exists());
}

#[test]
fn concurrent_installs_of_the_same_version_both_succeed() {
    let archive = make_archive(&[("charon", ""), ("charon-driver", "")]);
    let sha = sha256_hex(&archive);
    let server = serve(HashMap::from([("/charon.tar.gz".to_string(), archive)]));
    let env = Env::new(&format!(
        r#"[tools.charon."v1".{platform}]
url = "{base}/charon.tar.gz"
sha256 = "{sha}"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}
"#,
        platform = platform(),
        base = server.base_url,
    ));
    let children: Vec<_> = (0..2)
        .map(|_| {
            env.command(&["tools", "install", "charon@v1"], None)
                .spawn()
                .unwrap()
        })
        .collect();
    for child in children {
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success());
    }
    assert!(env.version_dir("charon", "v1").join("charon").is_file());
}

#[test]
fn project_install_covers_the_union_and_skips_path_pins() {
    // Workspace: root pins charon v1, member `b` overrides to v2 and pins
    // aeneas to a path. The default aeneas version must also be covered.
    let default_aeneas = {
        // Read the default the binary was built with, from `tools show`.
        let env = Env::new("");
        let dir = tempfile::tempdir().unwrap();
        write_crate(dir.path(), "probe");
        let output = env
            .command(
                &["--message-format", "json", "tools", "show"],
                Some(dir.path()),
            )
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let json: serde_json::Value = serde_json::from_str(stdout.lines().last().unwrap()).unwrap();
        json["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["name"] == "aeneas")
            .unwrap()["version"]
            .as_str()
            .unwrap()
            .to_string()
    };

    let charon_v1 = make_archive(&[("charon", "1"), ("charon-driver", "1")]);
    let charon_v2 = make_archive(&[("charon", "2"), ("charon-driver", "2")]);
    let aeneas = make_archive(&[("aeneas", "")]);
    let (sha1, sha2_, sha_a) = (
        sha256_hex(&charon_v1),
        sha256_hex(&charon_v2),
        sha256_hex(&aeneas),
    );
    let server = serve(HashMap::from([
        ("/charon-v1.tar.gz".to_string(), charon_v1),
        ("/charon-v2.tar.gz".to_string(), charon_v2),
        ("/aeneas.tar.gz".to_string(), aeneas),
    ]));
    let charon_entry_points =
        r#"entry_points = { charon = "charon", charon-driver = "charon-driver" }"#;
    let env = Env::new(&format!(
        r#"[tools.charon."v1".{platform}]
url = "{base}/charon-v1.tar.gz"
sha256 = "{sha1}"
{charon_entry_points}

[tools.charon."v2".{platform}]
url = "{base}/charon-v2.tar.gz"
sha256 = "{sha2_}"
{charon_entry_points}

[tools.aeneas."{default_aeneas}".{platform}]
url = "{base}/aeneas.tar.gz"
sha256 = "{sha_a}"
entry_points = {{ aeneas = "aeneas" }}
"#,
        platform = platform(),
        base = server.base_url,
    ));

    let project = tempfile::tempdir().unwrap();
    std::fs::write(
        project.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"a\", \"b\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    write_crate(&project.path().join("a"), "a");
    write_crate(&project.path().join("b"), "b");
    std::fs::write(
        project.path().join("hax.toml"),
        "[tools]\ncharon = \"v1\"\n",
    )
    .unwrap();
    std::fs::write(
        project.path().join("b/hax.toml"),
        "[tools]\ncharon = \"v2\"\naeneas = { path = \"/opt/aeneas\" }\n",
    )
    .unwrap();

    let output = env
        .command(&["tools", "install"], Some(project.path()))
        .output()
        .unwrap();
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "{all}");
    // Union: both charon versions and the default aeneas.
    assert!(env.version_dir("charon", "v1").is_dir(), "{all}");
    assert!(env.version_dir("charon", "v2").is_dir(), "{all}");
    assert!(env.version_dir("aeneas", &default_aeneas).is_dir(), "{all}");
    // The member's path pin is skipped with a note.
    assert!(all.contains("nothing to install"), "{all}");
}

#[test]
fn list_truncates_and_filters() {
    let mut manifest = String::new();
    for i in 0..12 {
        manifest.push_str(&format!(
            "[tools.charon.\"nightly-2026.01.{i:02}\".{}]\nurl = \"https://example.com/{i}.tar.gz\"\nsha256 = \"{}\"\n",
            platform(),
            "0".repeat(64),
        ));
    }
    let env = Env::new(&manifest);

    let (output, success) = env.run(&["tools", "list", "charon"]);
    assert!(success);
    assert!(
        output.contains("2 older versions omitted (use --all)"),
        "{output}"
    );
    assert!(!output.contains("nightly-2026.01.00"), "{output}");
    assert!(output.contains("nightly-2026.01.11"), "{output}");

    let (output, _) = env.run(&["tools", "list", "charon", "--all"]);
    assert!(output.contains("nightly-2026.01.00"), "{output}");
    assert!(!output.contains("omitted"), "{output}");

    let (output, _) = env.run(&["tools", "list", "charon", "--installed"]);
    assert!(!output.contains("nightly-2026.01.11"), "{output}");

    let (output, success) = env.run(&["tools", "list", "unknown-tool"]);
    assert!(!success);
    assert!(output.contains("not a managed tool"), "{output}");
}

#[test]
fn malformed_install_specs_are_rejected() {
    let env = Env::new("");
    let (output, success) = env.run(&["tools", "install", "charon"]);
    assert!(!success);
    assert!(output.contains("<tool>@<version>"), "{output}");
    let (output, success) = env.run(&["tools", "install", "unknown@v1"]);
    assert!(!success);
    assert!(output.contains("not a managed tool"), "{output}");
    let (output, success) = env.run(&["tools", "install", "charon@../escape"]);
    assert!(!success);
    assert!(
        output.contains("not a valid version identifier"),
        "{output}"
    );
}

fn write_crate(dir: &Path, name: &str) {
    std::fs::create_dir_all(dir.join("src")).unwrap();
    let mut manifest = std::fs::File::create(dir.join("Cargo.toml")).unwrap();
    writeln!(
        manifest,
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"",
    )
    .unwrap();
    std::fs::write(dir.join("src/lib.rs"), "").unwrap();
}

/// A server that accepts connections and reads requests but never sends a
/// response, so a client stalls waiting for bytes. Returns its base URL.
fn serve_stalling() -> String {
    let server = tiny_http::Server::http("127.0.0.1:0").unwrap();
    let port = server.server_addr().to_ip().unwrap().port();
    std::thread::spawn(move || {
        // Hold every request open, never responding, so the connection
        // stays alive with no data forthcoming.
        let mut held = Vec::new();
        for request in server.incoming_requests() {
            held.push(request);
        }
    });
    format!("http://127.0.0.1:{port}")
}

/// Run a command under a wall-clock deadline, killing it if it exceeds
/// the deadline. Returns the combined output and success flag, or `None`
/// if the deadline forced a kill (which is a test failure: the download
/// hung instead of timing out).
fn run_with_deadline(
    mut command: Command,
    deadline: std::time::Duration,
) -> Option<(String, bool)> {
    use std::io::Read;
    let mut child = command
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = child.stdout.take().unwrap();
    let mut stderr = child.stderr.take().unwrap();
    let out = std::thread::spawn(move || {
        let mut buf = String::new();
        let _ = stdout.read_to_string(&mut buf);
        buf
    });
    let err = std::thread::spawn(move || {
        let mut buf = String::new();
        let _ = stderr.read_to_string(&mut buf);
        buf
    });

    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break Some(status);
        }
        if start.elapsed() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    };
    let combined = format!("{}{}", out.join().unwrap(), err.join().unwrap());
    status.map(|status| (combined, status.success()))
}

#[test]
fn download_read_timeout_aborts_a_stalled_download() {
    // The manifest points at a server that never responds; the per-read
    // timeout must abort the download instead of hanging.
    let base = serve_stalling();
    let env = Env::new(&format!(
        r#"[tools.charon."v1".{platform}]
url = "{base}/charon-v1.tar.gz"
sha256 = "{sha}"
entry_points = {{ charon = "charon", charon-driver = "charon-driver" }}
"#,
        platform = platform(),
        sha = "0".repeat(64),
    ));

    // A one-second read timeout keeps the test fast; a generous wall-clock
    // deadline turns a dropped timeout (a regression) into a clean failure
    // rather than a hang.
    let mut command = env.command(&["tools", "install", "charon@v1"], None);
    command.env("HAX_TOOLS_READ_TIMEOUT_SECS", "1");
    let (output, success) = run_with_deadline(command, std::time::Duration::from_secs(30))
        .expect("the download must time out, not hang");

    assert!(!success, "{output}");
    assert!(output.contains("download failed"), "{output}");
    assert!(!env.version_dir("charon", "v1").exists(), "{output}");
}
