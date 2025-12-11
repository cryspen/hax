//! Work with hax attributes.

use std::collections::HashMap;

use hax_lib_macros_types::{AssociationRole, AttrPayload, ItemUid};

use crate::ast::diagnostics::{Context, DiagnosticInfo, DiagnosticInfoKind};

use super::ast::*;
use visitors::AstVisitorMut;

/// A graph of items connected via the hax attribute [`AttrPayload::AssociatedItem`] and UUIDs.
#[derive(Clone, Debug)]
pub struct LinkedItemGraph {
    items: HashMap<ItemUid, Item>,
    context: Context,
}

impl Default for LinkedItemGraph {
    fn default() -> Self {
        Self {
            items: Default::default(),
            context: Context::Unknown,
        }
    }
}

fn hax_attributes(attrs: &Attributes) -> impl Iterator<Item = &AttrPayload> {
    attrs.iter().flat_map(|attr| match &attr.kind {
        AttributeKind::Hax(attr_payload) => Some(attr_payload),
        _ => None,
    })
}

fn uuid(context: Context, item: &Item) -> Option<ItemUid> {
    let mut uuids = hax_attributes(&item.meta.attributes).flat_map(|attr| match attr {
        AttrPayload::Uid(item_uid) => Some(item_uid),
        _ => None,
    });
    let uuid = uuids.next()?;
    if let Some(other) = uuids.next() {
        emit_assertion_failure(
            context,
            item.span(),
            format!(
                "Found more than one UUID hax attribute on this item. The two first UUIDs are {uuid} and {other}."
            ),
        );
        None
    } else {
        Some(uuid.clone())
    }
}

fn emit_assertion_failure(context: Context, span: span::Span, message: impl Into<String>) {
    DiagnosticInfo {
        context,
        span,
        kind: DiagnosticInfoKind::AssertionFailure {
            details: message.into(),
        },
    }
    .emit();
}

impl LinkedItemGraph {
    /// Drains items marked with UUIDs attributes to build a graph of linked items.
    /// This graph owns the items that represent linked items: e.g. pre and post conditions.
    pub fn new(items: &mut Vec<Item>, context: Context) -> Self {
        pub fn extract_where<T, U>(
            v: &mut Vec<T>,
            mut f: impl FnMut(&T) -> Option<U>,
        ) -> Vec<(U, T)> {
            let mut extracted: Vec<(U, T)> = Vec::new();
            let mut kept: Vec<T> = Vec::with_capacity(v.len());

            for item in v.drain(..) {
                if let Some(u) = f(&item) {
                    extracted.push((u, item));
                } else {
                    kept.push(item);
                }
            }

            *v = kept;
            extracted
        }
        Self {
            items: HashMap::from_iter(
                extract_where(items, |item| uuid(context.clone(), item)).into_iter(),
            ),
            context,
        }
    }

    fn emit_assertion_failure(&self, span: span::Span, message: impl Into<String>) {
        emit_assertion_failure(self.context.clone(), span, message)
    }

    fn emit_unimplemented(&self, span: span::Span, issue_id: u32, message: impl Into<String>) {
        DiagnosticInfo {
            context: self.context.clone(),
            span,
            kind: DiagnosticInfoKind::Unimplemented {
                issue_id: Some(issue_id),
                details: Some(message.into()),
            },
        }
        .emit();
    }

    /// Given a graph and an item `item`, returns an iterator of the various items that are linked with `item`.
    pub fn linked_items_iter(
        &self,
        item: &impl HasMetadata,
    ) -> impl Iterator<Item = (AssociationRole, &Item)> {
        let item_attributes = &item.metadata().attributes;
        hax_attributes(item_attributes).flat_map(|attr| match attr {
            AttrPayload::AssociatedItem { role, item: target } => {
                let Some(target) = self.items.get(target) else {
                    self.emit_assertion_failure(item.span(), format!("An item linked via hax attributes could not be found. The UUID is {target:?}."));
                    return None;
                };
                Some((*role, target))
            }
            _ => None,
        })
    }

    /// Returns the items linked to a given item.
    pub fn linked_items(&self, item: &impl HasMetadata) -> HashMap<AssociationRole, Vec<&Item>> {
        let mut map: HashMap<AssociationRole, Vec<_>> = HashMap::new();
        for (role, item) in self.linked_items_iter(item) {
            map.entry(role).or_default().push(item);
        }
        map
    }

    /// Returns the precondition, postcondition and decreases clause, if any, for a given item.
    /// When operating on a linked function, `self_id` is the local identifier of `self`.
    pub fn fn_like_linked_expressions(
        &self,
        item: &impl HasMetadata,
        self_id: Option<&identifiers::LocalId>,
    ) -> FnLikeAssocatedExpressions {
        let assoc_items = self.linked_items(item);
        let get = |role| {
            assoc_items
                .get(&role)
                .iter()
                .flat_map(|vec| vec.iter().copied())
                .map(|item| extract_expr(&self.context, item, self_id))
                .collect::<Vec<_>>()
        };
        let precondition = {
            let mut preconditions = get(AssociationRole::Requires).into_iter();
            preconditions.next().map(|(e, _)| {
                for extra in preconditions {
                    self.emit_unimplemented(extra.0.span(), 1270, "multiple pre-conditions");
                }
                e
            })
        };
        let decreases = {
            let mut decreases = get(AssociationRole::Decreases).into_iter();
            decreases.next().map(|(e, _)| {
                for extra in decreases {
                    self.emit_unimplemented(extra.0.span(), 1270, "multiple decreases");
                }
                e
            })
        };
        let postcondition = {
            let mut postconditions = get(AssociationRole::Ensures).into_iter();
            postconditions.next().and_then(|(e, params)| {
                for extra in postconditions {
                    self.emit_unimplemented(extra.0.span(), 1270, "multiple post-conditions");
                }
                if let Some(last_param) = params.last() {
                    Some(Postcondition {
                        result_binder: last_param.pat.clone(),
                        body: e.clone(),
                    })
                } else {
                    self.emit_assertion_failure(
                        e.span(),
                        "hax ensures attribute: could not find output binder",
                    );
                    None
                }
            })
        };
        FnLikeAssocatedExpressions {
            decreases,
            precondition,
            postcondition,
        }
    }
}

fn extract_expr<'a>(
    context: &Context,
    item: &'a Item,
    self_id: Option<&identifiers::LocalId>,
) -> (Expr, Vec<&'a Param>) {
    let ItemKind::Fn { body, params, .. } = item.kind() else {
        return (
            ExprKind::Error(ErrorNode::assertion_failure(
                item.clone(),
                context.clone(),
                "Expected an function",
            ))
            .into_expr(item.span(), Ty::prop(), vec![]),
            vec![],
        );
    };
    let mut body = body.clone();
    if let Some(self_id) = self_id
        && let [maybe_self, ..] = params.as_slice()
        && let PatKind::Binding {
            var, sub_pat: None, ..
        } = &*maybe_self.pat.kind
    {
        // Here, we expect `self_id` is `self`, thus we cannot have any shadowing.
        utils::mappers::SubstLocalIds::one(var.clone(), self_id.clone()).visit(&mut body)
    }
    (body, params.iter().collect())
}

/// A postcondition.
///
/// ## Example
/// The expression `result != x` in the following is a postcondition.
/// Note that `result` is an extra binder that represent the result of `f`, whose type is `u8` in this case: the return type of `f`.
///
/// ```rust
/// #[hax_lib::ensures(|result| result != x)]
/// fn f(x: u8) -> u8 { x.wrapping_add(1) }
/// ```
pub struct Postcondition {
    /// In the example, this is `|result|`.
    pub result_binder: Pat,
    /// The formula of the postcondition, `result != x` in the example.
    pub body: Expr,
}

/// The various linked expressions one can usually find on a (linked or not) function.
pub struct FnLikeAssocatedExpressions {
    /// A decreases clause, see [`hax_lib::decreases`]
    pub decreases: Option<Expr>,
    /// A decreases clause, see [`hax_lib::decreases`]
    pub precondition: Option<Expr>,
    /// A decreases clause, see [`hax_lib::decreases`]
    pub postcondition: Option<Postcondition>,
}
