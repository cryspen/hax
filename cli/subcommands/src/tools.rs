//! Version management for hax's external tools.
//!
//! Projects declare the tool versions they require in a `hax.toml` at the
//! workspace root (with optional per-member-crate overrides). Resolution
//! follows, from highest to lowest precedence: the `HAX_<TOOL>_BINARY`
//! environment variable, the member crate's `hax.toml`, the workspace-root
//! `hax.toml`, and the built-in defaults embedded in this binary.

use hax_types::cli_options::{MessageFormat, ToolsCommand};

pub mod config;
pub mod defaults;
pub mod project;
pub mod resolve;
mod subcommands;

/// The tools whose installation hax manages. A `[tools]` entry naming
/// anything else is warned about and skipped.
pub const MANAGED_TOOLS: &[&str] = &["aeneas", "charon"];

/// The declared-only `[versions]` keys: versions hax must know without
/// managing an installation.
pub const DECLARED_VERSION_KEYS: &[&str] = &["lean", "hax-lean-lib"];

/// Entry point for `cargo hax tools <subcommand>`. Returns the process
/// exit code.
pub fn run(command: &ToolsCommand, message_format: MessageFormat) -> i32 {
    match command {
        ToolsCommand::Show => subcommands::show(message_format),
        ToolsCommand::Install { .. } | ToolsCommand::List { .. } => {
            hax_types::diagnostics::message::HaxMessage::GenericError {
                message: "this subcommand is not implemented yet; \
                          only `cargo hax tools show` is available in this release"
                    .into(),
            }
            .report(message_format, None);
            2
        }
    }
}
