val import_ty : Types.span -> Types.ty -> Ast.Rust.ty
val import_trait_ref : Types.span -> Types.trait_ref -> Ast.Rust.trait_goal
val import_clause : Types.span -> Types.clause -> Ast.Rust.impl_ident option

val import_item :
  drop_body:bool ->
  drop_impl_bodies:bool ->
  Types.item_for__decorated_for__expr_kind ->
  Concrete_ident.t * (Ast.Rust.item list * Diagnostics.t list)
