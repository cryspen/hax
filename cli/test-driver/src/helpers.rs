//! Helper functions that implement small bits of logic used across modules.

use std::path::Path;

use hax_frontend_exporter::{DefId, DefPathItem, DisambiguatedDefPathItem};
use hax_types::cli_options::BackendName;

use crate::log::{BackendJobKind, JobKind};

/// Returns `true` if `child` is defined within the item `parent`.
pub fn def_id_under(parent: &DefId, child: &DefId) -> bool {
    let parent_path = &parent.path;
    let child_path = &child.path;

    if parent_path.len() > child_path.len() {
        return false;
    }

    parent_path
        .iter()
        .enumerate()
        .all(|(i, chunk)| &child_path[i] == chunk)
}

/// Converts a [`DefId`] into a human readable string.
pub fn string_of_def_id(def_id: &DefId) -> String {
    def_id
        .path
        .iter()
        .map(|path| match &path.data {
            DefPathItem::Impl => "impl",
            DefPathItem::TypeNs(s)
            | DefPathItem::ValueNs(s)
            | DefPathItem::MacroNs(s)
            | DefPathItem::LifetimeNs(s) => s.as_str(),
            DefPathItem::Closure => "|_|",
            _ => "_",
        })
        .collect::<Vec<_>>()
        .join("::")
}

/// Returns the module name encoded in the first component of the [`DefId`].
pub fn module_name(def_id: &DefId) -> Option<String> {
    match def_id.path.first() {
        Some(DisambiguatedDefPathItem {
            data: DefPathItem::TypeNs(module_name),
            disambiguator: 0,
        }) => Some(module_name.clone()),
        _ => None,
    }
}

#[extension_traits::extension(pub trait BackendNameExt)]
impl BackendName {
    /// Convenience helper that wires a backend to a job kind.
    fn job_kind(self, kind: BackendJobKind) -> JobKind {
        JobKind::BackendJob {
            kind,
            backend: self,
        }
    }
}
