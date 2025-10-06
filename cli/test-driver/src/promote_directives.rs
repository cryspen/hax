//! Collects directives that should be promoted back into source files.

use std::{
    collections::HashMap,
    fmt::Display,
    path::{Path, PathBuf},
    sync::LazyLock,
};
use std::{fs::read_to_string, sync::Mutex};

use crate::directives::Directive;
use anyhow::Result;

static RUST_FILES: LazyLock<Mutex<HashMap<PathBuf, Vec<Line>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Flushes the queued directives to disk.
pub fn save() -> Result<()> {
    let files = RUST_FILES.lock().unwrap();
    use std::fs::write;

    for (path, lines) in files.iter() {
        let mut lines = lines.clone();

        lines.extend_from_slice(
            &read_to_string(path)?
                .lines()
                .enumerate()
                .map(|(line, contents)| Line {
                    line: line + 1,
                    kind: LineKind::String(contents.to_string()),
                })
                .collect::<Vec<_>>(),
        );

        lines.sort();

        let mut contents = lines
            .into_iter()
            .map(|line| line.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        if !contents.ends_with("\n") {
            contents += "\n";
        }
        write(path, contents)?;
    }

    Ok(())
}

/// Adds a directive or preserved line that should be written to the file.
pub fn push_line(path: &Path, line: Line) -> Result<()> {
    let mut files = RUST_FILES.lock().unwrap();
    let lines = files.entry(path.to_path_buf()).or_default();
    for existing_line in lines {
        if existing_line.line == line.line
            && let LineKind::Directive { directive, .. } = &line.kind
            && let LineKind::Directive {
                directive: existing_directive,
                ..
            } = &mut existing_line.kind
            && existing_directive.merge(directive)
        {
            return Ok(());
        }
    }
    let lines = files.entry(path.to_path_buf()).or_default();
    lines.push(line);
    Ok(())
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
/// Representation of a single line that will eventually be printed.
pub struct Line {
    pub line: usize,
    pub kind: LineKind,
}

#[derive(Debug, Clone, Eq, PartialEq)]
/// Classification of the line contents.
pub enum LineKind {
    String(String),
    Directive { directive: Directive, bang: bool },
}

impl Display for Line {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl Display for LineKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LineKind::String(s) => write!(f, "{s}"),
            LineKind::Directive { directive, bang } => {
                write!(f, "//{} {directive}", if *bang { "!" } else { "/" })
            }
        }
    }
}

impl PartialOrd for LineKind {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LineKind {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (LineKind::String { .. }, LineKind::Directive { .. }) => std::cmp::Ordering::Greater,
            (LineKind::Directive { .. }, LineKind::String { .. }) => std::cmp::Ordering::Less,
            _ => std::cmp::Ordering::Equal,
        }
    }
}
