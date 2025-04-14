open Prelude
module Dst = Rust_printer_types

module Make (F : Features.T) = struct
  module Src = struct
    include Ast
    include Ast.Make (F)
  end

  let c_span (_i : Span.t) : Dst.span = EmptyStructspan
  let c_attr (_i : Src.attr) : Dst.attribute = EmptyStructattribute
  let c_generics (_i : Src.generics) : Dst.generics = EmptyStructgenerics

  let c_safety_kind : Src.safety_kind -> Dst.safety_kind = function
    | Safe -> Safe
    | Unsafe _ -> Unsafe

  let c_concrete_ident (_ : Src.concrete_ident) : Dst.global_id =
    { name = "mycrate::todo::def" }

  let c_global_ident (_ : Src.global_ident) : Dst.global_id =
    { name = "mycrate::todo::def" }

  let c_local_ident (local_id : Src.local_ident) : Dst.local_id =
    Newtypelocal_id (Newtypesymbol local_id.name)

  let c_int_size : Src.size -> Dst.int_size = function
    | S8 -> S8
    | S16 -> S16
    | S32 -> S32
    | S64 -> S64
    | S128 -> S128
    | SSize -> SSize

  let c_signedness : Src.signedness -> Dst.signedness = function
    | Signed -> Signed
    | Unsigned -> Unsigned

  let c_int_kind (ik : Src.int_kind) : Dst.int_kind =
    let size = c_int_size ik.size in
    let signedness = c_signedness ik.signedness in
    { size; signedness }

  let c_attrs = List.map ~f:c_attr

  let c_binding_mode : Src.binding_mode -> Dst.binding_mode = function
    | ByValue -> ByValue
    | ByRef (Shared, _) -> ByRef Shared
    | ByRef (Unique, _) -> ByRef Unique
    | ByRef (Mut _, _) -> ByRef Mut

  let c_metadata span attrs : Dst.metadata =
    { span = c_span span; attrs = c_attrs attrs }

  let c_literal (lit : Src.literal) : Dst.literal =
    match lit with
    | String s -> String (Newtypesymbol s)
    | Int { value; negative; kind } ->
        let kind = c_int_kind kind in
        Int { value; negative; kind }
    | Bool b -> Bool b
    | _ -> failwith "todo"

  let rec c_expr_kind (expr_kind : Src.expr') : Dst.expr_kind =
    match expr_kind with
    | GlobalVar v -> GlobalId (c_global_ident v)
    | If { cond; then_; else_ } ->
        let condition = c_expr cond in
        let then_ = c_expr then_ in
        let else_ = Option.map ~f:c_expr else_ in
        If { condition; then_; else_ }
    | Literal lit -> Literal (c_literal lit)
    | Array values -> Array (List.map ~f:c_expr values)
    | Let { monadic = None; lhs; rhs; body } ->
        let lhs = c_pat lhs in
        let rhs = c_expr rhs in
        let body = c_expr body in
        Let { lhs; rhs; body }
    (* | Tuple values -> Tuple (List.map ~f:c_expr values) *)
    | _ -> failwith "todo"

  and c_expr (expr : Src.expr) : Dst.expr =
    let meta = c_metadata expr.span [] in
    let kind = c_expr_kind expr.e in
    let ty = c_ty expr.typ in
    { meta; kind; ty }

  and c_ty (ty : Src.ty) : Dst.ty =
    match ty with
    | TBool -> Primitive Bool
    | TInt int_kind -> Primitive (Int (c_int_kind int_kind))
    | TApp { ident; args } ->
        let head = c_global_ident ident in
        let args = c_generic_values args in
        App { head; args }
    | _ -> failwith "todo"

  and c_generic_values : Src.generic_value list -> Dst.generic_value list =
    List.filter_map ~f:c_generic_value

  and c_generic_value (gv : Src.generic_value) : Dst.generic_value option =
    match gv with
    | GType ty -> Some (Ty (c_ty ty))
    | GConst e -> Some (Expr (c_expr e))
    | _ -> None

  and c_pat_kind : Src.pat' -> Dst.pat_kind = function
    | PWild -> Wild
    | PBinding { mut; mode; var; typ = _; subpat = None } ->
        let var = c_local_ident var in
        let mode = c_binding_mode mode in
        Binding
          {
            var;
            mode;
            mutable' = (match mut with Mutable _ -> true | _ -> false);
          }
    | _ -> failwith "todo pat"

  and c_pat (pat : Src.pat) : Dst.pat =
    let kind = c_pat_kind pat.p in
    let ty = c_ty pat.typ in
    let meta = c_metadata pat.span [] in
    { kind; ty; meta }

  and c_param span (param : Src.param) : Dst.param =
    let pat = c_pat param.pat in
    let ty : Dst.spanned_ty =
      let ty = c_ty param.typ in
      let span =
        Option.map ~f:c_span param.typ_span |> Option.value ~default:span
      in
      { span; ty }
    in
    let attributes = c_attrs param.attrs in
    { pat; ty; attributes }

  and c_params span = List.map ~f:(c_param span)

  let c_item_kind span (item_kind : Src.item') : Dst.item_kind =
    match item_kind with
    | Fn { name; generics; body; params; safety } ->
        let name = c_concrete_ident name in
        let generics = c_generics generics in
        let body = c_expr body in
        let params = c_params span params in
        let safety = c_safety_kind safety in
        Fn { name; generics; body; params; safety }
    | _ -> failwith "unsupported"

  let c_item (i : Src.item) : Dst.item =
    let meta = c_metadata i.span i.attrs in
    let ident = c_concrete_ident i.ident in
    let kind = c_item_kind meta.span i.v in
    { meta; ident; kind }
end

module Full = Make (Features.Full)
