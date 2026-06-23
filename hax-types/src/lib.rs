#![cfg_attr(feature = "rustc", feature(rustc_private))]
//! This crate contains the type definitions that are used to communicate between:
//!  - the command line (the `cargo-hax` binary);
//!  - the custom rustc driver;
//!  - the hax engine (the `hax-engine` binary).
//!  
//! Those three component send and receive messages in JSON or CBOR on
//! stdin and stdout.

pub(crate) mod prelude;

/// The CLI options for `cargo-hax`. The types defines in this module
/// are also used by the driver and the engine.
pub mod cli_options;

/// Type to represent errors, mainly in `hax-engine`. The engine
/// doesn't do any reporting itself: it only sends JSON to its stdout,
/// and `cargo-hax` takes care of reporting everything in a rustc
/// style.
pub mod diagnostics;

/// The types used to communicate between `cargo-hax` and the custom
/// driver.
pub mod driver_api;

/// The types used to communicate between `cargo-hax` and
/// `hax-engine`.
pub mod engine_api;

/// Compile-time version of hax
pub const HAX_VERSION: &str = env!("HAX_VERSION");

/// Tool pins, baked in at build time from the workspace-root `pins.toml` (see
/// `build.rs`). Read here once so every consumer (`cargo-hax`'s aeneas-lean
/// backend, the `--help` text) shares a single source of truth. A value is empty
/// when its pin is missing/malformed (e.g. a packaged build without `pins.toml`).
pub mod pins {
    /// Short commit SHA `aeneas -version` is expected to report.
    pub const AENEAS_VERSION: &str = env!("HAX_AENEAS_PIN_VERSION");
    /// Source repository of the pinned aeneas.
    pub const AENEAS_REPO: &str = env!("HAX_AENEAS_PIN_REPO");
    /// Version `charon version` is expected to report.
    pub const CHARON_VERSION: &str = env!("HAX_CHARON_PIN_VERSION");
    /// Lean toolchain written to generated `lean-toolchain` files.
    pub const LEAN_TOOLCHAIN: &str = env!("HAX_LEAN_PIN_TOOLCHAIN");
    /// Source repository of the Hax aeneas-lean proof library.
    pub const LEAN_LIB_REPO: &str = env!("HAX_LEAN_LIB_PIN_REPO");
    /// Commit of the Hax aeneas-lean proof library.
    pub const LEAN_LIB_COMMIT: &str = env!("HAX_LEAN_LIB_PIN_COMMIT");
}
