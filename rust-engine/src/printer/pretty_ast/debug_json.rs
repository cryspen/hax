use std::fmt::{Debug, Display};

use crate::printer::pretty_ast::ToDocument;

/// This type is primarily useful inside printer implementations when you want a
/// low-friction way to inspect an AST fragment.
///
/// # What it does
/// - Appends a JSON representation of the wrapped value to
///   `"/tmp/hax-ast-debug.json"` (one JSON document per line).
/// - Implements [`std::fmt::Display`] to print a `just` invocation you can paste in a shell
///   to re-open that same JSON by line number:
///   `just debug-json <line-id>`
///
/// # Example
/// ```rust
/// # use hax_rust_engine::printer::pretty_ast::DebugJSON;
/// # #[derive(serde::Serialize)]
/// # struct Small { x: u32 }
/// let s = Small { x: 42 };
/// // Prints something like: `just debug-json 17`.
/// println!("{}", DebugJSON(&s));
/// // Running `just debug-json 17` will print `{"x":42}`
/// ```
///
/// # Notes
/// - This is a **debugging convenience** and intentionally has a side-effect (file write).
///   Avoid keeping it in user-facing output paths.
/// - The file grows over time; occasionally delete it if you no longer need historical entries.
pub struct DebugJSON<T: serde::Serialize>(pub T);

impl<T: serde::Serialize> Display for DebugJSON<T> {
    #[cfg(not(unix))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<unknown, DebugJSON supported on unix plateforms only>")
    }
    #[cfg(unix)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const PATH: &str = "/tmp/hax-ast-debug.json";
        /// Write a new JSON as a line at the end of `PATH`
        fn append_line_json(value: &serde_json::Value) -> std::io::Result<usize> {
            use std::io::{BufRead, BufReader, Write};
            cleanup();
            let file = std::fs::OpenOptions::new()
                .read(true)
                .append(true)
                .create(true)
                .open(PATH)?;
            let count = BufReader::new(&file).lines().count();
            writeln!(&file, "{value}")?;
            Ok(count)
        }

        /// Drop the file at `PATH` when we first write
        fn cleanup() {
            static DID_RUN: AtomicBool = AtomicBool::new(false);
            use std::sync::atomic::{AtomicBool, Ordering};
            if DID_RUN
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                let _ignored = std::fs::remove_file(PATH);
            }
        }

        if let Ok(id) = append_line_json(&serde_json::to_value(&self.0).unwrap()) {
            write!(f, "`just debug-json {id}`")
        } else {
            write!(f, "<DebugJSON failed>")
        }
    }
}

impl<A: 'static + Clone, P, T: serde::Serialize + Debug> ToDocument<P, A> for DebugJSON<T> {
    fn to_document(&self, _: &P) -> super::DocBuilder<A> {
        pretty::DocAllocator::as_string(
            &pretty::BoxAllocator,
            &serde_json::to_string_pretty(&self.0).unwrap_or_else(|_| format!("{:#?}", &self.0)),
        )
    }
}
