//! Provides lightweight span hints used to promote directives into source
//! files.

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::OnceLock,
};

use anyhow::{Context, Result};
use hax_frontend_exporter::{Attribute, AttributeKind, DefId, Item, ItemKind, Span};

#[derive(Debug)]
/// Captures the best location to display diagnostics for a given definition.
pub struct SpanHint {
    pub span: Span,
    pub module_file: Option<PathBuf>,
}

fn test_module_path(item: &Item<()>) -> Option<PathBuf> {
    let path = item.span.filename.to_path()?;
    let dir = path.parent()?;
    let ItemKind::Mod(_, _) = item.kind else {
        return None;
    };
    item.attributes
        .attributes
        .iter()
        .find_map(|attr| match attr {
            Attribute::Parsed(AttributeKind::Path(relative_path, _span)) => {
                Some(dir.join(relative_path).to_path_buf())
            }
            _ => None,
        })
}

impl SpanHint {
    fn new(item: &Item<()>) -> Self {
        Self {
            span: item.span.clone(),
            module_file: test_module_path(item),
        }
    }

    /// Returns the file and line that should be used when materialising the
    /// directive.
    pub fn get_file_and_line(&self) -> (Option<&Path>, usize, bool) {
        if let Some(module_path) = &self.module_file {
            (Some(module_path.as_path()), 1, true)
        } else {
            (self.span.filename.to_path(), self.span.lo.line, false)
        }
    }
}

static SPAN_HINTS: OnceLock<HashMap<DefId, SpanHint>> = OnceLock::new();

/// Looks up a stored span hint for the provided definition.
pub async fn span_hint(owner_id: &DefId) -> Result<Option<&'static SpanHint>> {
    Ok(SPAN_HINTS
        .get()
        .context("span_hint: no hints found, was the `collect` function run?")?
        .get(owner_id))
}

/// Builds the in-memory lookup table for span hints.
pub fn init(items: &[Item<()>]) -> Result<()> {
    SPAN_HINTS
        .set(
            items
                .iter()
                .map(|item| (item.owner_id.clone(), SpanHint::new(item)))
                .collect(),
        )
        .map_err(|_| anyhow::Error::msg("`collect` was called more than once"))
}
