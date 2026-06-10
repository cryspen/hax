fn rustc_version_env_var() {
    let (_version, channel, date) = version_check::triple().unwrap();
    println!("cargo:rustc-env=HAX_RUSTC_VERSION={channel}-{date}");

    let rust_toolchain_file = include_str!("rust-toolchain.toml")
        .parse::<toml::Table>()
        .unwrap();
    println!(
        "cargo:rustc-env=HAX_TOOLCHAIN={}",
        rust_toolchain_file["toolchain"]["channel"]
            .as_str()
            .expect("Could not find key [toolchain.channel] in [rust-toolchain.toml]")
    );
}

fn json_schema_static_asset() {
    let mut schema = schemars::schema_for!((
        hax_frontend_exporter::Item<hax_frontend_exporter::ThirBody>,
        hax_types::cli_options::Options,
        hax_types::diagnostics::Diagnostics,
        hax_types::engine_api::EngineOptions,
        hax_types::engine_api::Output,
        hax_types::engine_api::WithDefIds<hax_frontend_exporter::ThirBody>,
        hax_types::engine_api::protocol::FromEngine,
        hax_types::engine_api::protocol::ToEngine,
        hax_lib_macros_types::AttrPayload,
        hax_rust_engine::ocaml_engine::Query,
        hax_rust_engine::ocaml_engine::Response,
    ));
    schema.schema.metadata.get_or_insert_default().id = Some(hax_types::HAX_VERSION.into());
    serde_json::to_writer(
        std::fs::File::create(format!("{}/schema.json", std::env::var("OUT_DIR").unwrap()))
            .unwrap(),
        &schema,
    )
    .unwrap();
}

fn git_dirty_env_var() {
    println!("cargo:rurun-if-env-changed=HAX_GIT_IS_DIRTY");
    let dirty = {
        use std::process::Command;
        let _ = Command::new("git")
            .args(["update-index", "-q", "--refresh"])
            .status();
        !Command::new("git")
            .args(["diff-index", "--quiet", "HEAD", "--"])
            .status()
            .map(|status| status.success())
            .unwrap_or(true)
    };
    println!("cargo:rustc-env=HAX_GIT_IS_DIRTY={}", dirty);
}

/// Embed the pinned aeneas commit and charon version at compile time for the
/// runtime version checks.
fn pin_env_vars() {
    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");

    // aeneas-pin: read the "commit <sha>" line (compared against `aeneas -version`)
    let aeneas_pin_path = workspace_root.join("aeneas-pin");
    println!("cargo:rerun-if-changed={}", aeneas_pin_path.display());
    let aeneas_pin = std::fs::read_to_string(&aeneas_pin_path).unwrap_or_default();
    let aeneas_commit = aeneas_pin
        .lines()
        .find_map(|l| l.strip_prefix("commit "))
        .unwrap_or("")
        .trim();
    println!("cargo:rustc-env=HAX_EXPECTED_AENEAS_VERSION={aeneas_commit}");

    // charon-pin: read the "version X.Y.Z" line
    let charon_pin_path = workspace_root.join("charon-pin");
    println!("cargo:rerun-if-changed={}", charon_pin_path.display());
    let charon_pin = std::fs::read_to_string(&charon_pin_path).unwrap_or_default();
    let charon_version = charon_pin
        .lines()
        .find(|l| l.starts_with("version "))
        .and_then(|l| l.strip_prefix("version "))
        .unwrap_or("");
    println!("cargo:rustc-env=HAX_EXPECTED_CHARON_VERSION={charon_version}");
}

fn main() {
    rustc_version_env_var();
    json_schema_static_asset();
    git_dirty_env_var();
    pin_env_vars();
}
