use crate::ast::*;
use crate::phase::Phase;

/// Phase to filter unprintable items
///
/// This phase filters out items that are not printable (Error, NotImplementedYet, Use).
#[derive(Default, Debug)]
pub struct FilterUnprintableItems;

impl Phase for FilterUnprintableItems {
    fn apply(&self, items: &mut Vec<Item>) {
        items.retain(|item| match &item.kind {
            // Items to remove:
            ItemKind::Error(_) | ItemKind::NotImplementedYet | ItemKind::Use { .. } => false,
            // Items to keep:
            ItemKind::Fn { .. }
            | ItemKind::TyAlias { .. }
            | ItemKind::Type { .. }
            | ItemKind::Trait { .. }
            | ItemKind::Impl { .. }
            | ItemKind::Alias { .. }
            | ItemKind::Resugared(_)
            | ItemKind::Quote { .. } => true,
        });
    }
}
