open! Prelude

let refute_resugared s =
  failwith
    ("Got a resugared node at " ^ s
   ^ ". The AST is never supposed to be sent to the OCaml engine with \
      resugared nodes.")

let broken_invariant s = failwith s

type missing_type = unit

module A = Rust_engine_types
module F = Features.Full

module B = struct
  include Ast
  include Ast.Make (F)
end

module U = Ast_utils.Make (F)
module Build = Ast_builder.Make (F)

module SpecialNames = struct
  let rec map_strings (f : string -> string)
      ({ kind; krate; parent; path } : Types.def_id2) : Types.def_id2 =
    let path =
      List.map
        ~f:(fun { data; disambiguator } ->
          let data =
            match data with
            | Types.CrateRoot { name } -> Types.CrateRoot { name = f name }
            | Types.TypeNs s -> Types.TypeNs (f s)
            | Types.ValueNs s -> Types.ValueNs (f s)
            | Types.MacroNs s -> Types.MacroNs (f s)
            | Types.LifetimeNs s -> Types.LifetimeNs (f s)
            | other -> other
          in
          Types.{ data; disambiguator })
        path
    in
    let parent = Option.map ~f:(map_strings f) parent in
    Types.{ kind; krate; parent; path }

  let g len nth s =
    match String.chop_prefix ~prefix:"Tuple" s with
    | Some n -> (
        let n = Int.of_string_opt n in
        match n with
        | Some n ->
            len := Some n;
            "Tuple2"
        | _ -> s)
    | None -> (
        let n = Int.of_string_opt s in
        match n with
        | Some n ->
            nth := Some n;
            "1"
        | _ -> s)

  let destruct_compare name (did : A.concrete_id) =
    let len, nth = (ref None, ref None) in
    let patched = map_strings (g len nth) did.def_id.def_id in
    let nth = !nth in
    let* len = !len in
    let name = Concrete_ident_generated.def_id_of name in
    let name = Explicit_def_id.def_id_to_rust_ast name.contents.value in
    if [%eq: Types.def_id2] name patched then Some (len, nth) else None

  let tuple_type (did : A.concrete_id) : int option =
    let* len, _ = destruct_compare Rust_primitives__hax__Tuple2 did in
    Some len

  let tuple_cons (did : A.concrete_id) : int option =
    let* len, _ = destruct_compare Rust_primitives__hax__Tuple2__Ctor did in
    Some len

  let tuple_field (did : A.concrete_id) : (int * int) option =
    let* len, nth = destruct_compare Rust_primitives__hax__Tuple2__1 did in
    let* nth = nth in
    Some (len, nth)

  let expect_tuple_global_id (did : A.concrete_id) : Ast.Global_ident.t option =
    match tuple_type did with
    | Some len -> Some (`TupleType len)
    | None -> (
        match tuple_cons did with
        | Some len -> Some (`TupleCons len)
        | None -> (
            match tuple_field did with
            | Some (len, nth) -> Some (`TupleField (nth, len))
            | None -> None))

  let conv (did : A.concrete_id) =
    match expect_tuple_global_id did with
    | Some id -> id
    | None ->
        let id = Concrete_ident.from_rust_ast did in
        let eq n = Concrete_ident.eq_name n id in
        if eq Rust_primitives__hax__deref_op then `Primitive Deref
        else if eq Rust_primitives__hax__cast_op then `Primitive Cast
        else if eq Rust_primitives__hax__logical_op_and then
          `Primitive (LogicalOp And)
        else if eq Rust_primitives__hax__logical_op_or then
          `Primitive (LogicalOp Or)
        else `Concrete id
end

let from_error_node (error_node : Types.error_node) : string =
  match (error_node.fragment, error_node.diagnostics) with
  | ( Unknown "OCamlEngineError",
      [
        {
          node = Unknown "OCamlEngineError";
          info = { kind = OcamlEngineErrorPayload payload; _ };
          _;
        };
      ] ) ->
      payload
  | _ -> [%yojson_of: Types.error_node] error_node |> Yojson.Safe.to_string

let dsafety_kind (safety : A.safety_kind) : B.safety_kind =
  match safety with Safe -> B.Safe | Unsafe -> B.Unsafe F.unsafe

let rec dty (Newtypety ty : A.ty) : B.ty =
  match ty with
  | Primitive Bool -> TBool
  | Primitive Char -> TChar
  | Primitive (Int k) -> TInt (dint_kind k)
  | Primitive (Float k) -> TFloat (dfloat_kind k)
  | Primitive Str -> TStr
  | App { head; args } ->
      TApp
        { ident = dglobal_ident head; args = List.map ~f:dgeneric_value args }
  | Array { ty; length } -> TArray { typ = dty ty; length = dexpr length }
  | Slice ty -> TSlice { ty = dty ty; witness = F.slice }
  | Ref { inner; mutable'; region = _ } ->
      TRef
        {
          witness = F.reference;
          typ = dty inner;
          mut = (if mutable' then Mutable F.mutable_reference else Immutable);
          region = "unknown";
        }
  | Param local_ident -> TParam (dlocal_ident local_ident)
  | Arrow { inputs; output } -> TArrow (List.map ~f:dty inputs, dty output)
  | AssociatedType { impl_; item } ->
      TAssociatedType { impl = dimpl_expr impl_; item = dconcrete_ident item }
  | Opaque ident -> TOpaque (dconcrete_ident ident)
  | RawPointer -> TRawPointer { witness = F.raw_pointer }
  | Dyn goals ->
      TDyn { witness = F.dyn; goals = List.map ~f:ddyn_trait_goal goals }
  | Resugared _ -> refute_resugared "ty"
  | Error s -> U.HaxFailure.Build.ty (from_error_node s)

and dint_kind (ik : A.int_kind) : B.int_kind =
  let size : B.size =
    match ik.size with
    | S8 -> S8
    | S16 -> S16
    | S32 -> S32
    | S64 -> S64
    | S128 -> S128
    | SSize -> SSize
  in
  {
    size;
    signedness =
      (match ik.signedness with Signed -> Signed | Unsigned -> Unsigned);
  }

and dfloat_kind (fk : A.float_kind) : B.float_kind =
  match fk with F16 -> F16 | F32 -> F32 | F64 -> F64 | F128 -> F128

and dglobal_ident (gi : A.global_id) : B.global_ident =
  match gi with
  | Types.Concrete c -> SpecialNames.conv c
  | Types.Projector c ->
      let c = SpecialNames.conv c in
      `Projector
        (match c with
        | `Concrete id -> `Concrete id
        | `TupleField f -> `TupleField f
        | _ -> broken_invariant "incorrect projector")

and dlocal_ident (Newtypelocal_id (Newtypesymbol li) : A.local_id) :
    B.local_ident =
  { id = (Expr, 0); name = li }

and dconcrete_ident (gi : A.global_id) : B.concrete_ident =
  match dglobal_ident gi with
  | `Concrete id -> id
  | _ ->
      broken_invariant
        "dconcrete_ident: got something else than a [`Concrete _]"

and ddyn_trait_goal (r : A.dyn_trait_goal) : B.dyn_trait_goal =
  {
    non_self_args = List.map ~f:dgeneric_value r.non_self_args;
    trait = dconcrete_ident r.trait_;
  }

and dtrait_goal (r : A.trait_goal) : B.trait_goal =
  { args = List.map ~f:dgeneric_value r.args; trait = dconcrete_ident r.trait_ }

and dimpl_ident (r : A.impl_ident) : B.impl_ident =
  {
    goal = dtrait_goal r.goal;
    name = (match r.name with Newtypesymbol name -> name);
  }

and dprojection_predicate (r : A.projection_predicate) : B.projection_predicate
    =
  {
    assoc_item = dconcrete_ident r.assoc_item;
    impl = dimpl_expr r.impl_;
    typ = dty r.ty;
  }

and dimpl_expr (i : A.impl_expr) : B.impl_expr =
  { goal = dtrait_goal i.goal; kind = dimpl_expr_kind i.kind }

and dimpl_expr_kind (i : A.impl_expr_kind) : B.impl_expr_kind =
  match i with
  | A.Self_ -> B.Self
  | A.Concrete tr -> B.Concrete (dtrait_goal tr)
  | A.LocalBound { id = A.Newtypesymbol id } -> B.LocalBound { id }
  | A.Parent { impl_; ident } ->
      B.Parent { impl = dimpl_expr impl_; ident = dimpl_ident ident }
  | A.Projection { impl_; item; ident } ->
      B.Projection
        {
          impl = dimpl_expr impl_;
          item = dconcrete_ident item;
          ident = dimpl_ident ident;
        }
  | A.ImplApp { impl_; args } ->
      B.ImplApp { impl = dimpl_expr impl_; args = List.map ~f:dimpl_expr args }
  | A.Dyn -> B.Dyn
  | A.Builtin tr -> B.Builtin (dtrait_goal tr)

and dgeneric_value (generic_value : A.generic_value) : B.generic_value =
  match generic_value with
  | Lifetime -> B.GLifetime { lt = ""; witness = F.lifetime }
  | Ty t -> B.GType (dty t)
  | Expr e -> B.GConst (dexpr e)

and dborrow_kind (borrow_kind : A.borrow_kind) : B.borrow_kind =
  match borrow_kind with
  | Shared -> B.Shared
  | Unique -> B.Unique
  | Mut -> B.Mut F.mutable_reference

and dattributes (m : A.attribute2 list) : B.attrs = List.map ~f:dattr m
and dspan = Span.from_rust_ast_span

and dattr (a : A.attribute) : B.attr =
  let kind : B.attr_kind =
    match a.kind with
    | Tool { path; tokens } -> B.Tool { path; tokens }
    | DocComment { kind; body } ->
        let kind = match kind with Line -> B.DCKLine | Block -> DCKBlock in
        B.DocComment { kind; body }
  in
  { kind; span = dspan a.span }

and dpat (p : A.pat) : B.pat =
  let typ = dty p.ty in
  let span = dspan p.meta.span in
  { p = dpat' span typ p.kind; span; typ }

and dpat' span parent_ty (pat : A.pat_kind) : B.pat' =
  match pat with
  | Wild -> PWild
  | Ascription { pat; ty = { ty; span } } ->
      PAscription { pat = dpat pat; typ_span = dspan span; typ = dty ty }
  | Construct { constructor; is_record; is_struct; fields } ->
      PConstruct
        {
          constructor = dglobal_ident constructor;
          is_record;
          is_struct;
          fields =
            List.map
              ~f:(fun (field, pat) ->
                B.{ field = dglobal_ident field; pat = dpat pat })
              fields;
        }
  | Or { sub_pats } -> POr { subpats = List.map ~f:dpat sub_pats }
  | Array { args } -> PArray { args = List.map ~f:dpat args }
  | Deref { sub_pat } -> PDeref { subpat = dpat sub_pat; witness = F.reference }
  | Constant { lit } -> PConstant { lit = dliteral lit }
  | Binding { mutable'; mode; var; sub_pat } ->
      let mut = if mutable' then B.Mutable F.mutable_variable else Immutable in
      PBinding
        {
          mut;
          mode = dbinding_mode mode;
          var = dlocal_ident var;
          subpat = Option.map ~f:(fun p -> (dpat p, F.as_pattern)) sub_pat;
          typ = parent_ty;
        }
  | Resugared _ -> refute_resugared "ty"
  | Error diag ->
      let s = from_error_node diag in
      (U.HaxFailure.Build.pat span parent_ty s).p

and dbinding_mode (binding_mode : A.binding_mode) : B.binding_mode =
  match binding_mode with
  | ByValue -> B.ByValue
  | ByRef kind -> B.ByRef (dborrow_kind kind, F.reference)

and dexpr (e : A.expr) : B.expr =
  let typ = dty e.ty in
  let span = dspan e.meta.span in
  { e = dexpr' span typ e.kind; typ; span }

and dexpr' span typ (expr : A.expr_kind) : B.expr' =
  match expr with
  | If { condition; then'; else_ } ->
      If
        {
          cond = dexpr condition;
          then_ = dexpr then';
          else_ = Option.map ~f:dexpr else_;
        }
  | App { head; args; generic_args; bounds_impls; trait_ } ->
      App
        {
          f = dexpr head;
          args = List.map ~f:dexpr args;
          generic_args = List.map ~f:dgeneric_value generic_args;
          bounds_impls = List.map ~f:dimpl_expr bounds_impls;
          trait =
            Option.map
              ~f:(fun (impl, args) ->
                (dimpl_expr impl, List.map ~f:dgeneric_value args))
              trait_;
        }
  | Literal lit -> Literal (dliteral lit)
  | Array exprs -> Array (List.map ~f:dexpr exprs)
  | Construct { constructor; is_record; is_struct; fields; base } ->
      Construct
        {
          constructor = dglobal_ident constructor;
          fields =
            List.map ~f:(fun (id, e) -> (dglobal_ident id, dexpr e)) fields;
          base = Option.map ~f:(fun e -> (dexpr e, F.construct_base)) base;
          is_record;
          is_struct;
        }
  | Match { scrutinee; arms } ->
      Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms }
  | Let { lhs; rhs; body } ->
      Let { lhs = dpat lhs; rhs = dexpr rhs; body = dexpr body; monadic = None }
  | Block { body; safety_mode } ->
      Block
        {
          e = dexpr body;
          safety_mode = dsafety_kind safety_mode;
          witness = F.block;
        }
  | LocalId id -> LocalVar (dlocal_ident id)
  | GlobalId id -> GlobalVar (dglobal_ident id)
  | Ascription { e; ty } -> Ascription { e = dexpr e; typ = dty ty }
  | Assign { lhs; value } ->
      Assign { lhs = dlhs lhs; e = dexpr value; witness = F.mutable_variable }
  | Loop { body; kind; state; control_flow; label } ->
      Loop
        {
          body = dexpr body;
          kind = dloop_kind kind;
          state = Option.map ~f:dloop_state state;
          control_flow =
            Option.map
              ~f:(fun k -> (dcontrol_flow_kind k, F.fold_like_loop))
              control_flow;
          label = Option.map ~f:(fun (A.Newtypesymbol s) -> s) label;
          witness = F.loop;
        }
  | Break { value; label; state } ->
      Break
        {
          e = dexpr value;
          label = Option.map ~f:(fun (A.Newtypesymbol s) -> s) label;
          acc = Option.map ~f:(fun e -> (dexpr e, F.state_passing_loop)) state;
          witness = (F.break, F.loop);
        }
  | Return { value } -> Return { e = dexpr value; witness = F.early_exit }
  | Continue { label; state } ->
      Continue
        {
          label = Option.map ~f:(fun (Newtypesymbol s) -> s) label;
          acc = Option.map ~f:(fun e -> (dexpr e, F.state_passing_loop)) state;
          witness = (F.continue, F.loop);
        }
  | Borrow { mutable'; inner } ->
      Borrow
        {
          e = dexpr inner;
          kind = (if mutable' then Mut F.mutable_reference else B.Shared);
          witness = F.reference;
        }
  | AddressOf { mutable'; inner } ->
      AddressOf
        {
          e = dexpr inner;
          mut = (if mutable' then Mutable F.mutable_pointer else Immutable);
          witness = F.raw_pointer;
        }
  | Closure { params; body; captures } ->
      Closure
        {
          params = List.map ~f:dpat params;
          body = dexpr body;
          captures = List.map ~f:dexpr captures;
        }
  | Quote { contents } -> Quote (dquote contents)
  | Resugared _ -> refute_resugared "expr"
  | Error diag -> (U.HaxFailure.Build.expr span typ (from_error_node diag) "").e

and dcontrol_flow_kind (cfk : A.control_flow_kind) : B.cf_kind =
  match cfk with BreakOnly -> B.BreakOnly | BreakOrReturn -> B.BreakOrReturn

and dliteral (l : A.literal) : B.literal =
  match l with
  | String (Newtypesymbol s) -> B.String s
  | Char c -> B.Char c
  | Int { value = Newtypesymbol value; negative; kind } ->
      B.Int { value; negative; kind = dint_kind kind }
  | Float { value = Newtypesymbol value; negative; kind } ->
      B.Float { value; negative; kind = dfloat_kind kind }
  | Bool b -> B.Bool b

and dquote (Newtypequote contents : A.quote) : B.quote =
  let f = function
    | A.Verbatim code -> B.Verbatim code
    | A.Expr e -> B.Expr (dexpr e)
    | A.Pattern p -> B.Pattern (dpat p)
    | A.Ty t -> B.Typ (dty t)
  in
  { contents = List.map ~f contents; witness = F.quote }

and ditem_quote_origin (iqo : A.item_quote_origin) : B.item_quote_origin =
  {
    item_ident = dconcrete_ident iqo.item_ident;
    item_kind =
      (match iqo.item_kind with
      | A.Fn -> `Fn
      | A.TyAlias -> `TyAlias
      | A.Type -> `Type
      | A.MacroInvocation -> `IMacroInvokation
      | A.Trait -> `Trait
      | A.Impl -> `Impl
      | A.Alias -> `Alias
      | A.Use -> `Use
      | A.Quote -> `Quote
      | A.HaxError -> `HaxError
      | A.NotImplementedYet -> `NotImplementedYet);
    position =
      (match iqo.position with
      | A.Before -> `Before
      | A.After -> `After
      | A.Replace -> `Replace);
  }

and dloop_kind (k : A.loop_kind) : B.loop_kind =
  match k with
  | A.UnconditionalLoop -> B.UnconditionalLoop
  | A.WhileLoop { condition } ->
      B.WhileLoop { condition = dexpr condition; witness = F.while_loop }
  | A.ForLoop { iterator; pat } ->
      B.ForLoop { it = dexpr iterator; pat = dpat pat; witness = F.for_loop }
  | A.ForIndexLoop { start; end'; var; var_ty } ->
      B.ForIndexLoop
        {
          start = dexpr start;
          end_ = dexpr end';
          var = dlocal_ident var;
          var_typ = dty var_ty;
          witness = F.for_index_loop;
        }

and dloop_state (s : A.loop_state) : B.loop_state =
  {
    bpat = dpat s.body_pat;
    init = dexpr s.init;
    witness = F.state_passing_loop;
  }

and darm (a : A.arm) : B.arm =
  {
    arm =
      {
        body = dexpr a.body;
        guard = Option.map ~f:dguard a.guard;
        arm_pat = dpat a.pat;
      };
    span = dspan a.meta.span;
  }

and dguard (a : A.guard) : B.guard =
  { guard = dguard' a.kind; span = dspan a.meta.span }

and dguard' (guard : A.guard_kind) : B.guard' =
  match guard with
  | IfLet { lhs; rhs } ->
      B.IfLet { lhs = dpat lhs; rhs = dexpr rhs; witness = F.match_guard }

and dlhs (lhs : A.lhs) : B.lhs =
  match lhs with
  | A.LocalVar { var; ty } ->
      B.LhsLocalVar { var = dlocal_ident var; typ = dty ty }
  | A.ArbitraryExpr e ->
      B.LhsArbitraryExpr { e = dexpr e; witness = F.arbitrary_lhs }
  | A.FieldAccessor { e; field; ty } ->
      B.LhsFieldAccessor
        {
          e = dlhs e;
          field = dglobal_ident field;
          typ = dty ty;
          witness = F.nontrivial_lhs;
        }
  | A.ArrayAccessor { e; index; ty } ->
      B.LhsArrayAccessor
        {
          e = dlhs e;
          index = dexpr index;
          typ = dty ty;
          witness = F.nontrivial_lhs;
        }

let dgeneric_param ({ ident; meta; kind } : A.generic_param) : B.generic_param =
  let kind : B.generic_param_kind =
    match kind with
    | Lifetime -> GPLifetime { witness = F.lifetime }
    | Type -> GPType
    | Const { ty } -> GPConst { typ = dty ty }
  in
  {
    ident = dlocal_ident ident;
    span = dspan meta.span;
    attrs = dattributes meta.attributes;
    kind;
  }

let dgeneric_constraint (generic_constraint : A.generic_constraint) :
    B.generic_constraint =
  match generic_constraint with
  | Lifetime lf -> GCLifetime (lf, F.lifetime)
  | Type impl_ident -> GCType (dimpl_ident impl_ident)
  | Projection projection -> GCProjection (dprojection_predicate projection)

let dgenerics (g : A.generics) : B.generics =
  {
    constraints = List.map ~f:dgeneric_constraint g.constraints;
    params = List.map ~f:dgeneric_param g.params;
  }

let dparam (p : A.param) : B.param =
  {
    attrs = dattributes p.attributes;
    pat = dpat p.pat;
    typ = dty p.ty;
    typ_span = Option.map ~f:dspan p.ty_span;
  }

let dvariant (v : A.variant) : B.variant =
  {
    arguments =
      List.map
        ~f:(fun (id, t, a) -> (dconcrete_ident id, dty t, dattributes a))
        v.arguments;
    attrs = dattributes v.attributes;
    is_record = v.is_record;
    name = dconcrete_ident v.name;
  }

let dtrait_item' (ti : A.trait_item_kind) : B.trait_item' =
  match ti with
  | Type idents -> TIType (List.map ~f:dimpl_ident idents)
  | Fn t -> TIFn (dty t)
  | Default { params; body } ->
      TIDefault
        {
          params = List.map ~f:dparam params;
          body = dexpr body;
          witness = F.trait_item_default;
        }
  | Resugared _ -> refute_resugared "trait_item"

let dtrait_item (ti : A.trait_item) : B.trait_item =
  {
    ti_generics = dgenerics ti.generics;
    ti_ident = dconcrete_ident ti.ident;
    ti_v = dtrait_item' ti.kind;
    ti_span = dspan ti.meta.span;
    ti_attrs = dattributes ti.meta.attributes;
  }

let dimpl_item' (ii : A.impl_item_kind) : B.impl_item' =
  match ii with
  | Type { ty; parent_bounds } ->
      IIType
        {
          typ = dty ty;
          parent_bounds = List.map ~f:(dimpl_expr *** dimpl_ident) parent_bounds;
        }
  | Fn { body; params } ->
      IIFn { body = dexpr body; params = List.map ~f:dparam params }
  | Resugared _ -> refute_resugared "impl_item"

let dimpl_item (ii : A.impl_item) : B.impl_item =
  {
    ii_generics = dgenerics ii.generics;
    ii_ident = dconcrete_ident ii.ident;
    ii_v = dimpl_item' ii.kind;
    ii_span = dspan ii.meta.span;
    ii_attrs = dattributes ii.meta.attributes;
  }

let ditem' (item : A.item_kind) : B.item' =
  match item with
  | A.Fn { name; generics; body; params; safety } ->
      B.Fn
        {
          name = dconcrete_ident name;
          generics = dgenerics generics;
          body = dexpr body;
          params = List.map ~f:dparam params;
          safety = dsafety_kind safety;
        }
  | A.Type { name; generics; variants; is_struct } ->
      B.Type
        {
          name = dconcrete_ident name;
          generics = dgenerics generics;
          variants = List.map ~f:dvariant variants;
          is_struct;
        }
  | A.TyAlias { name; generics; ty } ->
      B.TyAlias
        {
          name = dconcrete_ident name;
          generics = dgenerics generics;
          ty = dty ty;
        }
  | A.Trait { name; generics; items } ->
      B.Trait
        {
          name = dconcrete_ident name;
          generics = dgenerics generics;
          items = List.map ~f:dtrait_item items;
          safety = failwith "TODO";
        }
  | A.Impl
      {
        generics;
        self_ty;
        of_trait = trait_id, trait_generics;
        items;
        parent_bounds;
        safety;
      } ->
      B.Impl
        {
          generics = dgenerics generics;
          self_ty = dty self_ty;
          of_trait =
            (dconcrete_ident trait_id, List.map ~f:dgeneric_value trait_generics);
          items = List.map ~f:dimpl_item items;
          parent_bounds =
            List.map
              ~f:(fun (impl, ident) -> (dimpl_expr impl, dimpl_ident ident))
              parent_bounds;
          safety = dsafety_kind safety;
        }
  | A.Alias { name; item } ->
      B.Alias { name = dconcrete_ident name; item = dconcrete_ident item }
  | A.Use { path; is_external; rename } -> B.Use { path; is_external; rename }
  | A.Quote { quote; origin } ->
      B.Quote { quote = dquote quote; origin = ditem_quote_origin origin }
  | A.Error diag -> HaxError (from_error_node diag)
  | A.NotImplementedYet -> B.NotImplementedYet
  | Resugared _ -> refute_resugared "item_kind"

let ditem (i : A.item) : B.item list =
  [
    {
      ident = dconcrete_ident i.ident;
      v = ditem' i.kind;
      span = dspan i.meta.span;
      attrs = dattributes i.meta.attributes;
    };
  ]
