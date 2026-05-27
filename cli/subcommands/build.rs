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

/// Read a pin file and extract values for compile-time embedding.
fn aeneas_pin_env_vars() {
    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");

    // aeneas-pin: extract the commit SHA from the release tag
    let aeneas_pin_path = workspace_root.join("aeneas-pin");
    println!("cargo:rerun-if-changed={}", aeneas_pin_path.display());
    let aeneas_pin = std::fs::read_to_string(&aeneas_pin_path).unwrap_or_default();
    let aeneas_tag = aeneas_pin
        .lines()
        .find(|l| !l.starts_with('#') && !l.is_empty())
        .unwrap_or("");
    // Tag format: build-YYYY.MM.DD.HHMMSS-<full-sha>  →  extract the SHA prefix
    let aeneas_sha = aeneas_tag.rsplit('-').next().unwrap_or("");
    let aeneas_sha_prefix = &aeneas_sha[..aeneas_sha.len().min(8)];
    println!("cargo:rustc-env=HAX_EXPECTED_AENEAS_VERSION={aeneas_sha_prefix}");

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
    aeneas_pin_env_vars();
}
