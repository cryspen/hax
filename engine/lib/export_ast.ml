open! Prelude

let deprecated_node s = failwith ("Deprecated AST node:" ^ s)

type missing_type = unit

module B = Rust_engine_types

module SpecialNames = struct
  let rec map_strings (f : string -> string)
      ({ contents = { id; value } } : Types.def_id) =
    let id = Int64.neg id in
    let value =
      match value with
      | { index; is_local; kind; krate; parent; path } ->
          let path =
            List.map
              ~f:(fun { data; disambiguator } ->
                let data =
                  match data with
                  | Types.CrateRoot { name } ->
                      Types.CrateRoot { name = f name }
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
          Types.{ index; is_local; kind; krate; parent; path }
    in
    let contents : Types.node_for__def_id_contents = { id; value } in
    { contents }

  let mk value f =
    Concrete_ident_generated.def_id_of >> map_strings f
    >> Concrete_ident.of_def_id ~value

  let f len nth = function
    | "Tuple2" -> "Tuple" ^ Int.to_string len
    | "1" -> "Tuple" ^ Int.to_string nth
    | s -> s

  let tuple_type len = mk false (f len 0) Rust_primitives__hax__Tuple2
  let tuple_cons len = mk true (f len 0) Rust_primitives__hax__Tuple2__Ctor
  let tuple_field len nth = mk false (f len nth) Rust_primitives__hax__Tuple2__1
end

module Make (FA : Features.T) = struct
  open Ast
  module A = Ast.Make (FA)

  let dsafety_kind (safety : A.safety_kind) : B.safety_kind =
    match safety with Safe -> B.Safe | Unsafe _ -> B.Unsafe

  let rec dty (ty : A.ty) : B.ty =
    match ty with
    | TBool -> Newtypety (Primitive Bool)
    | TChar -> Newtypety (Primitive Char)
    | TInt k -> Newtypety (Primitive (Int (dint_kind k)))
    | TFloat k -> Newtypety (Primitive (Float (dfloat_kind k)))
    | TStr -> Newtypety (Primitive Str)
    | TApp { ident; args } ->
        Newtypety
          (B.App
             {
               head = dglobal_ident ident;
               args = List.map ~f:dgeneric_value args;
             })
    | TArray { typ; length } ->
        Newtypety (Array { ty = dty typ; length = dexpr length })
    | TSlice { witness = _; ty } -> Newtypety (Slice (dty ty))
    | TRef { witness = _; typ; mut; region = _ } ->
        Newtypety
          (Ref
             {
               inner = dty typ;
               mutable' = (match mut with Mutable _ -> true | _ -> false);
               region = B.EmptyStructregion2;
             })
    | TParam local_ident -> Newtypety (Param (dlocal_ident local_ident))
    | TArrow (inputs, output) ->
        Newtypety
          (Arrow { inputs = List.map ~f:dty inputs; output = dty output })
    | TAssociatedType { impl; item } ->
        Newtypety
          (AssociatedType
             { impl_ = dimpl_expr impl; item = dconcrete_ident item })
    | TOpaque ident -> Newtypety (Opaque (dconcrete_ident ident))
    | TRawPointer { witness = _ } -> Newtypety RawPointer
    | TDyn { witness = _; goals } ->
        Newtypety (Dyn (List.map ~f:ddyn_trait_goal goals))

  and dint_kind (ik : int_kind) : B.int_kind =
    let size : B.int_size =
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

  and dfloat_kind (fk : float_kind) : B.float_kind =
    match fk with F16 -> F16 | F32 -> F32 | F64 -> F64 | F128 -> F128

  and dglobal_ident (gi : global_ident) : B.global_id =
    let concrete c : B.global_id = B.Concrete (Concrete_ident.to_rust_ast c) in
    let of_name n = concrete (Concrete_ident.of_name ~value:true n) in
    match gi with
    | `Concrete c -> concrete c
    | `TupleType len -> SpecialNames.tuple_type len |> concrete
    | `TupleCons len -> SpecialNames.tuple_cons len |> concrete
    | `TupleField (nth, len) -> SpecialNames.tuple_field len nth |> concrete
    | `Primitive Deref -> of_name Rust_primitives__hax__deref_op
    | `Primitive Cast -> of_name Rust_primitives__hax__cast_op
    | `Primitive (LogicalOp And) -> of_name Rust_primitives__hax__logical_op_and
    | `Primitive (LogicalOp Or) -> of_name Rust_primitives__hax__logical_op_or
    | `Projector (`Concrete c) -> Projector (Concrete_ident.to_rust_ast c)
    | `Projector (`TupleField (nth, len)) ->
        let c = SpecialNames.tuple_field len nth in
        Projector (Concrete_ident.to_rust_ast c)

  and dlocal_ident (li : local_ident) : B.local_id =
    Newtypelocal_id (Newtypesymbol li.name)

  and dconcrete_ident (gi : concrete_ident) : B.global_id =
    dglobal_ident (`Concrete gi)

  and ddyn_trait_goal (r : A.dyn_trait_goal) : B.dyn_trait_goal =
    {
      non_self_args = List.map ~f:dgeneric_value r.non_self_args;
      trait_ = dconcrete_ident r.trait;
    }

  and dtrait_goal (r : A.trait_goal) : B.trait_goal =
    {
      args = List.map ~f:dgeneric_value r.args;
      trait_ = dconcrete_ident r.trait;
    }

  and dimpl_ident (r : A.impl_ident) : B.impl_ident =
    { goal = dtrait_goal r.goal; name = Newtypesymbol r.name }

  and dprojection_predicate (r : A.projection_predicate) :
      B.projection_predicate =
    {
      assoc_item = dconcrete_ident r.assoc_item;
      impl_ = dimpl_expr r.impl;
      ty = dty r.typ;
    }

  and dimpl_expr (i : A.impl_expr) : B.impl_expr =
    { goal = dtrait_goal i.goal; kind = dimpl_expr_kind i.kind }

  and dimpl_expr_kind (i : A.impl_expr_kind) : B.impl_expr_kind =
    match i with
    | A.Self -> B.Self_
    | A.Concrete tr -> B.Concrete (dtrait_goal tr)
    | A.LocalBound { id } -> B.LocalBound { id = B.Newtypesymbol id }
    | A.Parent { impl; ident } ->
        B.Parent { impl_ = dimpl_expr impl; ident = dimpl_ident ident }
    | A.Projection { impl; item; ident } ->
        B.Projection
          {
            impl_ = dimpl_expr impl;
            item = dconcrete_ident item;
            ident = dimpl_ident ident;
          }
    | A.ImplApp { impl; args } ->
        B.ImplApp
          { impl_ = dimpl_expr impl; args = List.map ~f:dimpl_expr args }
    | A.Dyn -> B.Dyn
    | A.Builtin tr -> B.Builtin (dtrait_goal tr)

  and dgeneric_value (generic_value : A.generic_value) : B.generic_value =
    match generic_value with
    | GLifetime _ -> B.Lifetime
    | GType t -> B.Ty (dty t)
    | GConst e -> B.Expr (dexpr e)

  and dborrow_kind (borrow_kind : A.borrow_kind) : B.borrow_kind =
    match borrow_kind with
    | Shared -> B.Shared
    | Unique -> B.Unique
    | Mut _witness -> B.Mut

  and dmetadata ?(attrs = []) (span : span) : B.metadata =
    { attributes = List.map ~f:dattr attrs; span = dspan span }

  and dattr (a : attr) : B.attribute =
    let kind : B.attribute_kind =
      match a.kind with
      | Tool { path; tokens } -> B.Tool { path; tokens }
      | DocComment { kind; body } ->
          let kind = match kind with DCKLine -> B.Line | DCKBlock -> Block in
          B.DocComment { kind; body }
    in
    { kind; span = dspan a.span }

  and dpat (p : A.pat) : B.pat =
    { kind = dpat' p.p; meta = dmetadata p.span; ty = dty p.typ }

  and dpat' (pat : A.pat') : B.pat_kind =
    match pat with
    | PWild -> Wild
    | PAscription { typ; typ_span; pat } ->
        Ascription
          { pat = dpat pat; ty = { span = dspan typ_span; ty = dty typ } }
    | PConstruct { constructor; is_record; is_struct; fields } ->
        Construct
          {
            constructor = dglobal_ident constructor;
            is_record;
            is_struct;
            fields =
              List.map
                ~f:(fun { field; pat } -> (dglobal_ident field, dpat pat))
                fields;
          }
    | POr { subpats } -> Or { sub_pats = List.map ~f:dpat subpats }
    | PArray { args } -> Array { args = List.map ~f:dpat args }
    | PDeref { subpat; witness = _ } -> Deref { sub_pat = dpat subpat }
    | PConstant { lit } -> Constant { lit = dliteral lit }
    | PBinding { mut; mode; var; typ = _; subpat } ->
        let mutable' : bool = match mut with Mutable _ -> true | _ -> false in
        Binding
          {
            mutable';
            mode = dbinding_mode mode;
            var = dlocal_ident var;
            sub_pat = Option.map ~f:(fun (p, _) -> dpat p) subpat;
          }

  and dspan : span -> B.span = Span.to_span2

  and dbinding_mode (binding_mode : A.binding_mode) : B.binding_mode =
    match binding_mode with
    | ByValue -> B.ByValue
    | ByRef (kind, _witness) -> B.ByRef (dborrow_kind kind)

  and dexpr (e : A.expr) : B.expr =
    { kind = dexpr' e.e; ty = dty e.typ; meta = dmetadata e.span }

  and dexpr' (expr : A.expr') : B.expr_kind =
    match expr with
    | If { cond; then_; else_ } ->
        If
          {
            condition = dexpr cond;
            then' = dexpr then_;
            else_ = Option.map ~f:dexpr else_;
          }
    | App { f; args; generic_args; bounds_impls; trait } ->
        App
          {
            head = dexpr f;
            args = List.map ~f:dexpr args;
            generic_args = List.map ~f:dgeneric_value generic_args;
            bounds_impls = List.map ~f:dimpl_expr bounds_impls;
            trait_ =
              Option.map
                ~f:(fun (impl, args) ->
                  (dimpl_expr impl, List.map ~f:dgeneric_value args))
                trait;
          }
    | Literal lit -> Literal (dliteral lit)
    | Array exprs -> Array (List.map ~f:dexpr exprs)
    | Construct { constructor; is_record; is_struct; fields; base } ->
        Construct
          {
            constructor = dglobal_ident constructor;
            fields =
              List.map ~f:(fun (id, e) -> (dglobal_ident id, dexpr e)) fields;
            base = Option.map ~f:(fun (e, _) -> dexpr e) base;
            is_record;
            is_struct;
          }
    | Match { scrutinee; arms } ->
        Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms }
    | Let { monadic = _; lhs; rhs; body } ->
        Let { lhs = dpat lhs; rhs = dexpr rhs; body = dexpr body }
    | Block { e; safety_mode; witness = _ } ->
        Block { body = dexpr e; safety_mode = dsafety_kind safety_mode }
    | LocalVar id -> LocalId (dlocal_ident id)
    | GlobalVar id -> GlobalId (dglobal_ident id)
    | Ascription { e; typ } -> Ascription { e = dexpr e; ty = dty typ }
    | MacroInvokation _ -> deprecated_node "MacroInvokation"
    | Assign { lhs; e; witness = _ } ->
        Assign { lhs = dlhs lhs; value = dexpr e }
    | Loop { body; kind; state; control_flow; label; witness = _ } ->
        Loop
          {
            body = dexpr body;
            kind = dloop_kind kind;
            state = Option.map ~f:dloop_state state;
            control_flow =
              Option.map ~f:(fun (k, _) -> dcontrol_flow_kind k) control_flow;
            label = Option.map ~f:(fun s -> B.Newtypesymbol s) label;
          }
    | Break { e; acc = _; label; witness = _ } ->
        Break
          {
            value = dexpr e;
            label = Option.map ~f:(fun s -> B.Newtypesymbol s) label;
          }
    | Return { e; witness = _ } -> Return { value = dexpr e }
    | QuestionMark _ -> deprecated_node "QuestionMark"
    | Continue { acc = _; label; witness = _ } ->
        Continue { label = Option.map ~f:(fun s -> B.Newtypesymbol s) label }
    | Borrow { kind; e; witness = _ } ->
        Borrow
          {
            inner = dexpr e;
            mutable' = (match kind with Mut _ -> true | _ -> false);
          }
    | AddressOf { mut; e; witness = _ } ->
        AddressOf
          {
            inner = dexpr e;
            mutable' = (match mut with Mutable _ -> true | _ -> false);
          }
    | Closure { params; body; captures } ->
        Closure
          {
            params = List.map ~f:dpat params;
            body = dexpr body;
            captures = List.map ~f:dexpr captures;
          }
    | EffectAction _ -> deprecated_node "EffectAction"
    | Quote q -> Quote { contents = dquote q }

  and dcontrol_flow_kind (cfk : A.cf_kind) : B.control_flow_kind =
    match cfk with BreakOnly -> B.BreakOnly | BreakOrReturn -> B.BreakOrReturn

  and dliteral (l : Ast.literal) : B.literal =
    match l with
    | String s -> B.String (Newtypesymbol s)
    | Char c -> B.Char c
    | Int { value; negative; kind } ->
        B.Int { value; negative; kind = dint_kind kind }
    | Float { value; negative; kind } ->
        B.Float
          { value = Newtypesymbol value; negative; kind = dfloat_kind kind }
    | Bool b -> B.Bool b

  and dquote ({ contents; _ } : A.quote) : B.quote =
    let f = function
      | A.Verbatim code -> B.Verbatim code
      | A.Expr e -> B.Expr (dexpr e)
      | A.Pattern p -> B.Pattern (dpat p)
      | A.Typ t -> B.Ty (dty t)
    in
    Newtypequote (List.map ~f contents)

  and ditem_quote_origin (iqo : item_quote_origin) : B.item_quote_origin =
    {
      item_ident = dconcrete_ident iqo.item_ident;
      item_kind =
        (match iqo.item_kind with
        | `Fn -> B.Fn
        | `TyAlias -> B.TyAlias
        | `Type -> B.Type
        | `IMacroInvokation -> B.MacroInvocation
        | `Trait -> B.Trait
        | `Impl -> B.Impl
        | `Alias -> B.Alias
        | `Use -> B.Use
        | `Quote -> B.Quote
        | `HaxError -> B.HaxError
        | `NotImplementedYet -> B.NotImplementedYet);
      position =
        (match iqo.position with
        | `Before -> B.Before
        | `After -> B.After
        | `Replace -> B.Replace);
    }

  and dloop_kind (k : A.loop_kind) : B.loop_kind =
    match k with
    | A.UnconditionalLoop -> B.UnconditionalLoop
    | A.WhileLoop { condition; witness = _ } ->
        B.WhileLoop { condition = dexpr condition }
    | A.ForLoop { it; pat; witness = _ } ->
        B.ForLoop { iterator = dexpr it; pat = dpat pat }
    | A.ForIndexLoop { start; end_; var; var_typ; witness = _ } ->
        B.ForIndexLoop
          {
            start = dexpr start;
            end' = dexpr end_;
            var = dlocal_ident var;
            var_ty = dty var_typ;
          }

  and dloop_state (s : A.loop_state) : B.loop_state =
    { body_pat = dpat s.bpat; init = dexpr s.init }

  and darm (a : A.arm) : B.arm =
    {
      body = dexpr a.arm.body;
      guard = Option.map ~f:dguard a.arm.guard;
      meta = dmetadata a.span;
      pat = dpat a.arm.arm_pat;
    }

  and dguard (a : A.guard) : B.guard =
    { kind = dguard' a.guard; meta = dmetadata a.span }

  and dguard' (guard : A.guard') : B.guard_kind =
    match guard with
    | IfLet { lhs; rhs; witness = _ } ->
        B.IfLet { lhs = dpat lhs; rhs = dexpr rhs }

  and dlhs (lhs : A.lhs) : B.lhs =
    match lhs with
    | A.LhsLocalVar { var; typ } ->
        B.LocalVar { var = dlocal_ident var; ty = dty typ }
    | A.LhsArbitraryExpr { e; witness = _ } -> B.ArbitraryExpr (dexpr e)
    | A.LhsFieldAccessor { e; field; typ; witness = _ } ->
        B.FieldAccessor
          { e = dlhs e; field = dglobal_ident field; ty = dty typ }
    | A.LhsArrayAccessor { e; index; typ; witness = _ } ->
        B.ArrayAccessor { e = dlhs e; index = dexpr index; ty = dty typ }

  let dgeneric_param ({ ident; span; attrs; kind } : A.generic_param) :
      B.generic_param =
    let kind : B.generic_param_kind =
      match kind with
      | GPLifetime { witness = _ } -> Lifetime
      | GPType -> Type
      | GPConst { typ } -> Const { ty = dty typ }
    in
    { ident = dlocal_ident ident; meta = dmetadata ~attrs span; kind }

  let dgeneric_constraint (generic_constraint : A.generic_constraint) :
      B.generic_constraint =
    match generic_constraint with
    | GCLifetime (lf, _witness) -> Lifetime lf
    | GCType impl_ident -> Type (dimpl_ident impl_ident)
    | GCProjection projection -> Projection (dprojection_predicate projection)

  let dgenerics (g : A.generics) : B.generics =
    {
      constraints = List.map ~f:dgeneric_constraint g.constraints;
      params = List.map ~f:dgeneric_param g.params;
    }

  let dparam (p : A.param) : B.param =
    {
      attributes = List.map ~f:dattr p.attrs;
      pat = dpat p.pat;
      ty = dty p.typ;
      ty_span = Option.map ~f:dspan p.typ_span;
    }

  let dvariant (v : A.variant) : B.variant =
    let dattrs = List.map ~f:dattr in
    {
      arguments =
        List.map
          ~f:(fun (id, t, a) -> (dconcrete_ident id, dty t, dattrs a))
          v.arguments;
      attributes = dattrs v.attrs;
      is_record = v.is_record;
      name = dconcrete_ident v.name;
    }

  let dtrait_item' (ti : A.trait_item') : B.trait_item_kind =
    match ti with
    | TIType idents -> Type (List.map ~f:dimpl_ident idents)
    | TIFn t -> Fn (dty t)
    | TIDefault { params; body; witness = _ } ->
        Default { params = List.map ~f:dparam params; body = dexpr body }

  let dtrait_item (ti : A.trait_item) : B.trait_item =
    {
      generics = dgenerics ti.ti_generics;
      ident = dconcrete_ident ti.ti_ident;
      kind = dtrait_item' ti.ti_v;
      meta = dmetadata ~attrs:ti.ti_attrs ti.ti_span;
    }

  let dimpl_item' (ii : A.impl_item') : B.impl_item_kind =
    match ii with
    | IIType { typ; parent_bounds } ->
        Type
          {
            ty = dty typ;
            parent_bounds =
              List.map ~f:(dimpl_expr *** dimpl_ident) parent_bounds;
          }
    | IIFn { body; params } ->
        Fn { body = dexpr body; params = List.map ~f:dparam params }

  let dimpl_item (ii : A.impl_item) : B.impl_item =
    {
      generics = dgenerics ii.ii_generics;
      ident = dconcrete_ident ii.ii_ident;
      kind = dimpl_item' ii.ii_v;
      meta = dmetadata ~attrs:ii.ii_attrs ii.ii_span;
    }

  let ditem' (item : A.item') (span : Types.span2) : B.item_kind =
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
    | A.IMacroInvokation _ -> deprecated_node "IMacroInvokation"
    | A.Trait { name; generics; items; safety = _ } ->
        B.Trait
          {
            name = dconcrete_ident name;
            generics = dgenerics generics;
            items = List.map ~f:dtrait_item items;
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
              ( dconcrete_ident trait_id,
                List.map ~f:dgeneric_value trait_generics );
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
    | A.HaxError s ->
        let node : Types.fragment = Unknown "HaxError" in
        let info : B.diagnostic_info =
          { context = Import; kind = Custom s; span }
        in
        Error { node; info }
    | A.NotImplementedYet -> B.NotImplementedYet

  let ditem (i : A.item) : B.item list =
    [
      {
        ident = dconcrete_ident i.ident;
        kind = ditem' i.v (dspan i.span);
        meta = dmetadata ~attrs:i.attrs i.span;
      };
    ]
end
