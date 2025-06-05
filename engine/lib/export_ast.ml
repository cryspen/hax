open! Prelude

let todo () = failwith "todo"

type missing_type = unit

module B = Rust_printer_types

module Make (FA : Features.T) (FB : Features.T) = struct
  open Ast
  module A = Ast.Make (FA)

  let dsafety_kind (safety : A.safety_kind) : B.safety_kind =
    match safety with Safe -> todo () | Unsafe _ -> todo ()

  let dmutability (type a b) (s : Span.t -> a -> b) (mutability : a mutability)
      : b mutability =
    match mutability with Mutable _ -> todo () | Immutable -> todo ()

  let dty (ty : A.ty) : B.ty =
    match ty with
    | TBool -> todo ()
    | TChar -> todo ()
    | TInt k -> todo ()
    | TFloat k -> todo ()
    | TStr -> todo ()
    | TApp { ident; args } -> todo ()
    | TArray { typ; length } -> todo ()
    | TSlice { witness = _; ty } -> todo ()
    | TRef { witness = _; typ; mut; region } -> todo ()
    | TParam local_ident -> todo ()
    | TArrow (inputs, output) -> todo ()
    | TAssociatedType { impl; item } -> todo ()
    | TOpaque ident -> todo ()
    | TRawPointer { witness = _ } -> todo ()
    | TDyn { witness = _; goals } -> todo ()

  and ddyn_trait_goal (r : A.dyn_trait_goal) : B.dyn_trait_goal = todo ()
  and dtrait_goal (r : A.trait_goal) : B.trait_goal = todo ()
  and dimpl_ident (r : A.impl_ident) : B.impl_ident = todo ()

  and dprojection_predicate (r : A.projection_predicate) :
      B.projection_predicate =
    todo ()

  and dimpl_expr (i : A.impl_expr) : B.impl_expr = todo ()

  and dimpl_expr_kind (i : A.impl_expr_kind) : B.impl_expr_kind =
    match i with
    | Self -> todo ()
    | Concrete tr -> todo ()
    | LocalBound { id } -> todo ()
    | Parent { impl; ident } -> todo ()
    | Projection { impl; item; ident } -> todo ()
    | ImplApp { impl; args } -> todo ()
    | Dyn -> todo ()
    | Builtin tr -> todo ()

  and dgeneric_value (generic_value : A.generic_value) : B.generic_value =
    match generic_value with
    | GLifetime { lt; witness = _ } -> todo ()
    | GType t -> todo ()
    | GConst e -> todo ()

  and dborrow_kind (borrow_kind : A.borrow_kind) : B.borrow_kind =
    match borrow_kind with
    | Shared -> todo ()
    | Unique -> todo ()
    | Mut _witness -> todo ()

  and dpat (p : A.pat) : B.pat = todo ()

  and dpat' (pat : A.pat') : B.pat_kind =
    match pat with
    | PWild -> todo ()
    | PAscription { typ; typ_span; pat } -> todo ()
    | PConstruct { constructor; is_record; is_struct; fields } -> todo ()
    | POr { subpats } -> todo ()
    | PArray { args } -> todo ()
    | PConstant { lit } -> todo ()
    | PBinding { mut; mode; var : Local_ident.t; typ; subpat } -> todo ()
    | PDeref { subpat; witness = _ } -> todo ()

  and dfield_pat (_span : span) (p : A.field_pat) : missing_type = todo ()

  and dbinding_mode (binding_mode : A.binding_mode) : B.binding_mode =
    match binding_mode with
    | ByValue -> todo ()
    | ByRef (kind, _witness) -> todo ()

  and dsupported_monads (m : A.supported_monads) : missing_type =
    match m with
    | MException t -> todo ()
    | MResult t -> todo ()
    | MOption -> todo ()

  and dexpr (e : A.expr) : B.expr = todo ()

  and dexpr' (expr : A.expr') : B.expr_kind =
    match expr with
    | If { cond; then_; else_ } -> todo ()
    | App { f; args; generic_args; bounds_impls; trait } -> todo ()
    | Literal lit -> todo ()
    | Array l -> todo ()
    | Construct { constructor; is_record; is_struct; fields; base } -> todo ()
    | Match { scrutinee; arms } -> todo ()
    | Let { monadic; lhs; rhs; body } -> todo ()
    | Block { e; safety_mode; witness = _ } -> todo ()
    | LocalVar local_ident -> todo ()
    | GlobalVar global_ident -> todo ()
    | Ascription { e; typ } -> todo ()
    | MacroInvokation { macro; args; witness = _ } -> todo ()
    | Assign { lhs; e; witness = _ } -> todo ()
    | Loop { body; kind; state; label; witness = _; control_flow } -> todo ()
    | Break { e; acc; label; witness = _ } -> todo ()
    | Return { e; witness = _ } -> todo ()
    | QuestionMark { e; return_typ; witness = _ } -> todo ()
    | Continue { acc; label; witness = _ } -> todo ()
    | Borrow { kind; e; witness = _ } -> todo ()
    | EffectAction { action; argument } -> todo ()
    | AddressOf { mut; e; witness = _ } -> todo ()
    | Closure { params; body; captures } -> todo ()
    | Quote quote -> todo ()

  and dquote ({ contents; witness } : A.quote) : B.quote =
    let f = function
      | A.Verbatim code -> todo ()
      | Expr e -> todo ()
      | Pattern p -> todo ()
      | Typ p -> todo ()
    in
    todo ()

  and dloop_kind (k : A.loop_kind) : B.loop_kind =
    match k with
    | UnconditionalLoop -> todo ()
    | WhileLoop { condition; witness = _ } -> todo ()
    | ForLoop { it; pat; witness = _ } -> todo ()
    | ForIndexLoop { start; end_; var; var_typ; witness = _ } -> todo ()

  and dloop_state (s : A.loop_state) : B.loop_state = todo ()
  and darm (a : A.arm) : B.arm = todo ()
  and dguard (a : A.guard) : B.guard = todo ()

  and dguard' (guard : A.guard') : B.guard_kind =
    match guard with IfLet { lhs; rhs; witness = _ } -> todo ()

  and dlhs (lhs : A.lhs) : B.lhs =
    match lhs with
    | LhsFieldAccessor { e; field; typ; witness = _ } -> todo ()
    | LhsArrayAccessor { e; index; typ; witness = _ } -> todo ()
    | LhsLocalVar { var; typ } -> todo ()
    | LhsArbitraryExpr { e; witness = _ } -> todo ()

  let dgeneric_param _span ({ ident; span; attrs; kind } : A.generic_param) :
      B.generic_param =
    let kind =
      match kind with
      | GPLifetime { witness = _ } -> todo ()
      | GPType -> todo ()
      | GPConst { typ } -> todo ()
    in
    todo ()

  let dgeneric_constraint (generic_constraint : A.generic_constraint) :
      B.generic_constraint =
    match generic_constraint with
    | GCLifetime (lf, _witness) -> todo ()
    | GCType impl_ident -> todo ()
    | GCProjection projection -> todo ()

  let dgenerics (g : A.generics) : B.generics = todo ()
  let dparam (p : A.param) : B.param = todo ()
  let dvariant (v : A.variant) : B.variant = todo ()

  let dtrait_item' (ti : A.trait_item') : B.trait_item_kind =
    match ti with
    | TIType idents -> todo ()
    | TIFn t -> todo ()
    | TIDefault { params; body; witness = _ } -> todo ()

  and dtrait_item (ti : A.trait_item) : B.trait_item = todo ()

  let dimpl_item' (ii : A.impl_item') : B.impl_item_kind =
    match ii with
    | IIType { typ; parent_bounds } -> todo ()
    | IIFn { body; params } -> todo ()

  and dimpl_item (ii : A.impl_item) : B.impl_item = todo ()

  let ditem (i : A.item) : B.item list = todo ()

  and ditem' (item : A.item') : B.item_kind =
    match item with
    | Fn { name; generics; body; params; safety } -> todo ()
    | Type { name; generics; variants; is_struct } -> todo ()
    | TyAlias { name; generics; ty } -> todo ()
    | IMacroInvokation { macro; argument; span; witness = _ } -> todo ()
    | Trait { name; generics; items; safety } -> todo ()
    | Impl
        {
          generics;
          self_ty;
          of_trait = trait_id, trait_generics;
          items;
          parent_bounds;
          safety;
        } ->
        todo ()
    | Alias { name; item } -> todo ()
    | Use { path; is_external; rename } -> todo ()
    | Quote { quote; origin } -> todo ()
    | HaxError e -> todo ()
    | NotImplementedYet -> todo ()
end [@warnerror "-27-26"]
