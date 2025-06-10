use crate::ast as dst;

pub fn simple_app(
    fn_id: super::identifiers::GlobalId,
    args: Vec<dst::Expr>,
    ty: dst::Ty,
    span: dst::Span,
) -> dst::ExprKind {
    let head = dst::Expr {
        kind: Box::new(dst::ExprKind::GlobalId(fn_id)),
        ty,
        meta: dst::Metadata {
            span,
            attributes: vec![],
        },
    };
    dst::ExprKind::App {
        head,
        args,
        generic_args: Vec::new(),
        bounds_impls: Vec::new(),
        trait_: None,
    }
}
