//! Provides lightweight span hints used to promote directives into source
//! files.

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::OnceLock,
};

use anyhow::{Context, Result};
use hax_frontend_exporter::{Attribute, AttributeKind, DefId, FullDefKind, ItemKind, Span};

#[derive(Debug)]
/// Captures the best location to display diagnostics for a given definition.
pub struct SpanHint {
    pub span: Span,
    pub module_file: Option<PathBuf>,
}

fn test_module_path(span: &Span, attributes: &Vec<Attribute>) -> Option<PathBuf> {
    let path = span.filename.to_path()?;
    let dir = path.parent()?;
    attributes.iter().find_map(|attr| match attr {
        Attribute::Parsed(AttributeKind::Path(relative_path, _span)) => {
            Some(dir.join(relative_path).to_path_buf())
        }
        _ => None,
    })
}

impl SpanHint {
    fn new(span: &Span, attributes: Option<&Vec<Attribute>>) -> Self {
        let module_file = attributes.and_then(|attributes| test_module_path(span, attributes));
        Self {
            span: span.clone(),
            module_file,
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
pub fn init(items: &hax_types::driver_api::Items<()>) -> Result<()> {
    let v = match items {
        hax_types::driver_api::Items::FullDef(full_defs) => full_defs
            .iter()
            .map(|item| {
                let attributes = if let FullDefKind::Mod { .. } = item.kind {
                    Some(&item.attributes)
                } else {
                    None
                };
                (
                    item.this.def_id.clone(),
                    SpanHint::new(&item.span, attributes),
                )
            })
            .collect(),
        hax_types::driver_api::Items::Legacy(items) => items
            .iter()
            .map(|item| {
                let attributes = if let ItemKind::Mod(_, _) = item.kind {
                    Some(&item.attributes.attributes)
                } else {
                    None
                };
                (item.owner_id.clone(), SpanHint::new(&item.span, attributes))
            })
            .collect(),
    };
    SPAN_HINTS
        .set(v)
        .map_err(|_| anyhow::Error::msg("`collect` was called more than once"))
}
