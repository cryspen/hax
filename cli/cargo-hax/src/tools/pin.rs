//! Format-preserving editing of `hax.toml` for `cargo hax tools pin`.
//!
//! Pins are written with `toml_edit`, so comments, formatting, and entries
//! the command does not own survive: entries pinned to a `path` alone are
//! skipped, unknown tools and keys are left alone, and an existing
//! `{ version = "..." }` table keeps its shape with only the `version` key
//! updated. New tables are appended at the end of the document, so a
//! comment at the end of the file stays last and ends up below them.

use hax_types::diagnostics::message::PinChange;

/// The `hax.toml` table a pin is written to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Table {
    Tools,
    Versions,
}

impl Table {
    fn name(self) -> &'static str {
        match self {
            Table::Tools => "tools",
            Table::Versions => "versions",
        }
    }
}

/// One entry to write: its table, name, and version.
pub struct Pin {
    pub table: Table,
    pub name: String,
    pub version: String,
}

/// The result of applying pins to a `hax.toml`'s contents.
pub struct Outcome {
    /// The edited contents. Unchanged when `changes` is empty.
    pub contents: String,
    /// The entries that were written, in input order.
    pub changes: Vec<PinChange>,
    /// Names of path-pinned tools that were left untouched.
    pub skipped_paths: Vec<String>,
}

/// Apply `pins` to the contents of a `hax.toml` (empty for a new file).
/// The contents are arbitrary: nothing on the `pin` path loads the
/// configuration, so a file that is not valid TOML reaches this and is
/// reported as an error here.
pub fn apply(contents: &str, pins: &[Pin]) -> Result<Outcome, String> {
    let mut doc: toml_edit::DocumentMut =
        contents.parse().map_err(|e| format!("invalid TOML: {e}"))?;
    let mut changes = Vec::new();
    let mut skipped_paths = Vec::new();

    for pin in pins {
        let table = doc
            .entry(pin.table.name())
            .or_insert(toml_edit::Item::Table(toml_edit::Table::new()));
        let Some(table) = table.as_table_like_mut() else {
            return Err(format!("`[{}]` is not a table", pin.table.name()));
        };
        // An entry declaring both `version` and `path` is invalid, so it is
        // not a statement about how the binary is provided: pinning repairs
        // it by writing the version and dropping `path`.
        let mut drop_path = false;
        let previous = match table.get(&pin.name) {
            None => None,
            // A plain version string.
            Some(item) if item.as_str().is_some() => item.as_str().map(String::from),
            Some(item) => match item.as_table_like() {
                // A `{ path = "..." }` entry is the user's statement that
                // the binary is provided outside version management.
                Some(entry) if entry.contains_key("path") => {
                    if !entry.contains_key("version") {
                        skipped_paths.push(pin.name.clone());
                        continue;
                    }
                    drop_path = true;
                    entry
                        .get("version")
                        .and_then(|v| v.as_str())
                        .map(String::from)
                }
                Some(entry) => entry
                    .get("version")
                    .and_then(|v| v.as_str())
                    .map(String::from),
                None => None,
            },
        };
        if previous.as_deref() == Some(&pin.version) && !drop_path {
            continue;
        }
        // Update an existing entry's value in place, keeping its decor
        // (attached comments and spacing) and, for a `{ version = "..." }`
        // table, its shape; a new entry, and an entry being repaired, is a
        // plain string.
        let updated_in_place = match table.get_mut(&pin.name).filter(|_| !drop_path) {
            None => false,
            Some(item) => {
                let slot = match item.as_table_like_mut() {
                    Some(entry) => entry.get_mut("version").and_then(|v| v.as_value_mut()),
                    None => item.as_value_mut(),
                };
                match slot {
                    Some(value) => {
                        let decor = value.decor().clone();
                        *value = pin.version.as_str().into();
                        *value.decor_mut() = decor;
                        true
                    }
                    None => false,
                }
            }
        };
        if !updated_in_place {
            table.insert(&pin.name, toml_edit::value(&pin.version));
        }
        changes.push(PinChange {
            name: pin.name.clone(),
            version: pin.version.clone(),
            previous,
        });
    }

    Ok(Outcome {
        contents: doc.to_string(),
        changes,
        skipped_paths,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tools(name: &str, version: &str) -> Pin {
        Pin {
            table: Table::Tools,
            name: name.into(),
            version: version.into(),
        }
    }

    fn versions(name: &str, version: &str) -> Pin {
        Pin {
            table: Table::Versions,
            name: name.into(),
            version: version.into(),
        }
    }

    #[test]
    fn creates_both_tables_in_an_empty_file() {
        let outcome = apply(
            "",
            &[
                tools("aeneas", "v1"),
                tools("charon", "v2"),
                versions("lean", "leanprover/lean4:v4.31.0"),
            ],
        )
        .unwrap();
        assert_eq!(
            outcome.contents,
            "[tools]\naeneas = \"v1\"\ncharon = \"v2\"\n\n\
             [versions]\nlean = \"leanprover/lean4:v4.31.0\"\n"
        );
        assert_eq!(outcome.changes.len(), 3);
        assert!(outcome.changes.iter().all(|c| c.previous.is_none()));
    }

    #[test]
    fn rewrites_only_differing_entries_and_reports_the_previous_version() {
        let outcome = apply(
            "[tools]\naeneas = \"old\"\ncharon = \"v2\"\n",
            &[tools("aeneas", "new"), tools("charon", "v2")],
        )
        .unwrap();
        assert_eq!(
            outcome.contents,
            "[tools]\naeneas = \"new\"\ncharon = \"v2\"\n"
        );
        assert_eq!(outcome.changes.len(), 1);
        assert_eq!(outcome.changes[0].name, "aeneas");
        assert_eq!(outcome.changes[0].previous.as_deref(), Some("old"));
    }

    #[test]
    fn preserves_comments_formatting_and_foreign_entries() {
        let contents = "# project pins\n[tools]\n# why this one\naeneas = \"old\"  # inline\n\
                        future-tool = \"x\"\n\n[other]\nkey = 1\n";
        let outcome = apply(contents, &[tools("aeneas", "new")]).unwrap();
        assert_eq!(
            outcome.contents,
            "# project pins\n[tools]\n# why this one\naeneas = \"new\"  # inline\n\
             future-tool = \"x\"\n\n[other]\nkey = 1\n"
        );
    }

    #[test]
    fn table_shaped_entries_keep_their_shape() {
        let outcome = apply(
            "[tools]\naeneas = { version = \"old\" }\n",
            &[tools("aeneas", "new")],
        )
        .unwrap();
        assert_eq!(
            outcome.contents,
            "[tools]\naeneas = { version = \"new\" }\n"
        );
        assert_eq!(outcome.changes[0].previous.as_deref(), Some("old"));
    }

    #[test]
    fn path_entries_are_skipped() {
        let contents = "[tools]\naeneas = { path = \"/opt/aeneas\" }\n";
        let outcome = apply(contents, &[tools("aeneas", "new")]).unwrap();
        assert_eq!(outcome.contents, contents);
        assert!(outcome.changes.is_empty());
        assert_eq!(outcome.skipped_paths, ["aeneas"]);
    }

    #[test]
    fn an_entry_declaring_both_version_and_path_is_repaired() {
        for previous_version in ["old", "new"] {
            let contents = format!(
                "[tools]\naeneas = {{ version = \"{previous_version}\", path = \"/opt/a\" }}\n"
            );
            let outcome = apply(&contents, &[tools("aeneas", "new")]).unwrap();
            assert_eq!(outcome.contents, "[tools]\naeneas = \"new\"\n");
            assert_eq!(outcome.changes.len(), 1);
            assert!(outcome.skipped_paths.is_empty());
        }
    }

    #[test]
    fn a_trailing_comment_stays_at_the_end_of_the_file() {
        let outcome = apply(
            "[versions]\nlean = \"v1\"\n# end of file\n",
            &[tools("aeneas", "v1")],
        )
        .unwrap();
        assert_eq!(
            outcome.contents,
            "[versions]\nlean = \"v1\"\n\n[tools]\naeneas = \"v1\"\n# end of file\n"
        );
    }

    #[test]
    fn identical_pins_change_nothing() {
        let contents = "[tools]\naeneas = \"v1\"\n";
        let outcome = apply(contents, &[tools("aeneas", "v1")]).unwrap();
        assert_eq!(outcome.contents, contents);
        assert!(outcome.changes.is_empty());
        assert!(outcome.skipped_paths.is_empty());
    }
}
