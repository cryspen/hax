//! ProVerif-backend phase: normalize record construction to full positional
//! constructors in declaration order, and expand struct-update constructors.
//!
//! ProVerif constructors are positional and have no record-update syntax. This
//! phase rewrites each record `Construct` into a `base: None` constructor that
//! lists every field in declaration order, taking each field either from its
//! explicit expression or by projecting it from the base (`field_id(base)`).
//! It handles `S { f: x, ..base }`, the `self = Construct { constructor: <type
//! id>, base: Some(self), .. }` shape that `TrivializeAssignLhs` produces for
//! `self.f = x`, and record literals whose fields are written out of
//! declaration order. Positional constructors with no base are left untouched.

use std::collections::HashMap;

use crate::ast::identifiers::GlobalId;
use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::phase::Phase;

/// Phase that rewrites record `Construct` nodes into full positional
/// constructors in declaration order, expanding any struct-update base.
#[derive(Default, Debug)]
pub struct ProverifExpandStructUpdate;

/// The ordered field list and constructor id of a struct, indexed (in the
/// visitor) by both the type id and the variant id.
#[derive(Clone)]
struct StructInfo {
    /// The variant constructor id (e.g. `S__S`).
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

        // Pull the construction data out, ending the borrow on `expr.kind`.
        let (constructor, explicit, base, is_struct, is_record) = match &*expr.kind {
            ExprKind::Construct {
                constructor,
                fields,
                base,
                is_struct,
                is_record,
            } => (
                *constructor,
                fields.clone(),
                base.clone(),
                *is_struct,
                *is_record,
            ),
            _ => return,
        };

        // A positional (tuple-like) constructor with no base is already in
        // declaration order — leave it untouched. Everything else (any base
        // update, or a named-record literal that may be mis-ordered) is rebuilt
        // below.
        if base.is_none() && !is_record {
            return;
        }

        // Only structs/variants we found a definition for can be normalized;
        // anything else (e.g. a tuple) is left untouched.
        let Some(info) = self.structs.get(&constructor).cloned() else {
            return;
        };

        let span = expr.meta.span;
        let ty = expr.ty.clone();
        let mut new_fields: Vec<(GlobalId, Expr)> = Vec::with_capacity(info.fields.len());
        for (field_id, field_ty) in &info.fields {
            match explicit.iter().find(|(g, _)| g == field_id) {
                // Explicitly set in the literal/update.
                Some((_, value)) => new_fields.push((*field_id, value.clone())),
                // Otherwise project it from the base: `field_id(base)`.
                None => match &base {
                    Some(base) => new_fields.push((
                        *field_id,
                        Expr::standalone_fn_app(
                            *field_id,
                            vec![],
                            vec![base.clone()],
                            field_ty.clone(),
                            span,
                        ),
                    )),
                    // A complete literal sets every field; if one is missing
                    // with no base to recover it from, this is not a shape we
                    // can safely rebuild — leave the node untouched.
                    None => return,
                },
            }
        }

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
        // First pass: index every variant (struct or enum) by its variant id,
        // and every single-variant struct additionally by its type id (the
        // `&mut self` mutation rewrite uses the type id as the constructor).
        let mut structs: HashMap<GlobalId, StructInfo> = HashMap::new();
        for item in items.iter() {
            let ItemKind::Type {
                name,
                variants,
                is_struct,
                ..
            } = &item.kind
            else {
                continue;
            };
            for variant in variants {
                let info = StructInfo {
                    constructor: variant.name,
                    is_record: variant.is_record,
                    fields: variant
                        .arguments
                        .iter()
                        .map(|(id, ty, _)| (*id, ty.clone()))
                        .collect(),
                };
                structs.insert(variant.name, info.clone());
                if *is_struct {
                    structs.insert(*name, info);
                }
            }
        }

        ExpandStructUpdateVisitor {
            structs,
            ..Default::default()
        }
        .visit(items)
    }
}
