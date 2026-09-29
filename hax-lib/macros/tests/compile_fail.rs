//! The errors raised by `#[hax_lib::attributes]`, with and without
//! `--cfg hax`. Run with `TRYBUILD=overwrite` to update the expected outputs.

#[test]
fn compile_fail() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/common/*.rs");
    if cfg!(hax) {
        // trybuild builds with `--target` and its own flags, dropping those of
        // `.cargo/config.toml`: pass `--cfg hax` to the target and the host
        // (for the proc-macros) explicitly.
        let flags = [
            "--cfg",
            "hax",
            "--cfg",
            "trybuild",
            "--verbose",
            "--diagnostic-width=140",
            "-A",
            "dead_code",
            "-A",
            "unexpected_cfgs",
        ];
        std::env::set_var("CARGO_ENCODED_RUSTFLAGS", flags.join("\x1f"));
        std::env::set_var("CARGO_UNSTABLE_HOST_CONFIG", "true");
        std::env::set_var("CARGO_UNSTABLE_TARGET_APPLIES_TO_HOST", "true");
        std::env::set_var("CARGO_TARGET_APPLIES_TO_HOST", "false");
        std::env::set_var("CARGO_HOST_RUSTFLAGS", "--cfg hax");
        t.compile_fail("tests/ui/hax/*.rs");
    }
}
