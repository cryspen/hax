//! ProVerif-backend phase: expand struct-update constructors into full
//! positional constructors.
//!
//! ProVerif constructors are positional and must list *every* field, and the
//! language has no record-update (`{ base with f = x }`) syntax. Two AST shapes
//! reach the printer as a `Construct` carrying a `base: Some(..)`:
//!
//!  - `S { f: x, ..base }` from source — `constructor` is the variant id;
//!  - `self.f = x` mutation through `&mut self`, which the legacy
//!    `TrivializeAssignLhs` phase rewrites to
//!    `self = Construct { constructor = <type id>, fields = [(f, x)],
//!    base = Some(self) }` — here `constructor` is the *type* id, not the
//!    variant constructor id.
//!
//! In both cases the printer would otherwise (a) render only the explicitly-set
//! fields, silently dropping the base, and (b) for the mutation case use the
//! bare type name (`ClientState`) instead of the constructor (`ClientState__
//! ClientState`). Both make the model unsound — the rebuilt struct loses every
//! unchanged field and its projectors no longer match.
//!
//! This phase looks up the struct definition (by either the type id or the
//! variant id), then rewrites the node into a `base: None` constructor whose
//! fields are, in declaration order, the explicitly-set expression where one is
//! given and otherwise the field projected from the base (`field_id(base)` —
//! the same `App` shape a plain `self.field` read uses).

use std::collections::HashMap;

use crate::ast::identifiers::GlobalId;
use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::phase::Phase;

/// Phase that expands `Construct { base: Some(..) }` nodes into full positional
/// constructors for the ProVerif printer.
#[derive(Default, Debug)]
pub struct ProverifExpandStructUpdate;

/// The ordered field list and constructor id of a struct, indexed (in the
/// visitor) by both the type id and the variant id.
#[derive(Clone)]
struct StructInfo {
    /// The variant constructor id (e.g. `ClientState__ClientState`).
    constructor: GlobalId,
    /// Whether the fields are named.
    is_record: bool,
    /// The fields in declaration order: `(field id, field type)`.
    fields: Vec<(GlobalId, Ty)>,
}

#[setup_error_handling_struct]
#[derive(Default)]
struct ExpandStructUpdateVisitor {
    /// Lookup keyed by both the struct's type id and its variant id.
    structs: HashMap<GlobalId, StructInfo>,
}

impl VisitorWithContext for ExpandStructUpdateVisitor {
    fn context(&self) -> Context {
        Context::Phase(stringify!(ProverifExpandStructUpdate).to_string())
    }
}

impl AstVisitorMut for ExpandStructUpdateVisitor {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, expr: &mut Expr) {
        // Recurse first so a base expression that is itself a struct update is
        // already expanded before we project fields out of it.
        self.visit_inner(expr);

        // Pull the base-update data out, ending the borrow on `expr.kind`.
        let (constructor, explicit, base, is_struct) = match &*expr.kind {
            ExprKind::Construct {
                constructor,
                fields,
                base: Some(base),
                is_struct,
                ..
            } => (*constructor, fields.clone(), base.clone(), *is_struct),
            _ => return,
        };

        // Only structs we found a definition for can be expanded; anything else
        // (e.g. a tuple) is left untouched.
        let Some(info) = self.structs.get(&constructor).cloned() else {
            return;
        };

        let span = expr.meta.span;
        let ty = expr.ty.clone();
        let new_fields: Vec<(GlobalId, Expr)> = info
            .fields
            .iter()
            .map(|(field_id, field_ty)| {
                match explicit.iter().find(|(g, _)| g == field_id) {
                    // Explicitly set in the update.
                    Some((_, value)) => (*field_id, value.clone()),
                    // Otherwise project it from the base: `field_id(base)`.
                    None => (
                        *field_id,
                        Expr::standalone_fn_app(
                            *field_id,
                            vec![],
                            vec![base.clone()],
                            field_ty.clone(),
                            span,
                        ),
                    ),
                }
            })
            .collect();

        *expr = ExprKind::Construct {
            constructor: info.constructor,
            is_record: info.is_record,
            is_struct,
            fields: new_fields,
            base: None,
        }
        .promote(ty, span);
    }
}

impl Phase for ProverifExpandStructUpdate {
    fn apply(&self, items: &mut Vec<Item>) {
        // First pass: index every struct by both its type id and variant id.
        let mut structs: HashMap<GlobalId, StructInfo> = HashMap::new();
        for item in items.iter() {
            let ItemKind::Type {
                name,
                variants,
                is_struct: true,
                ..
            } = &item.kind
            else {
                continue;
            };
            let Some(variant) = variants.first() else {
                continue;
            };
            let info = StructInfo {
                constructor: variant.name,
                is_record: variant.is_record,
                fields: variant
                    .arguments
                    .iter()
                    .map(|(id, ty, _)| (*id, ty.clone()))
                    .collect(),
            };
            structs.insert(*name, info.clone());
            structs.insert(variant.name, info);
        }

        ExpandStructUpdateVisitor {
            structs,
            ..Default::default()
        }
        .visit(items)
    }
}
