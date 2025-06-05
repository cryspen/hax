open! Prelude

let todo () = failwith "todo"

type missing_type = unit

module B = Rust_printer_types

module Make (FA : Features.T) = struct
  open Ast
  module A = Ast.Make (FA)

  let dsafety_kind (safety : A.safety_kind) : B.safety_kind =
    match safety with Safe -> B.Safe | Unsafe _ -> B.Unsafe

  let dmutability (type a b) (s : Span.t -> a -> b) (mutability : a mutability)
      : b mutability =
    match mutability with Mutable _ -> todo () | Immutable -> todo ()

  let rec dty (ty : A.ty) : B.ty =
    match ty with
    | TBool -> Primitive Bool
    | TChar -> Primitive Char
    | TInt k -> Primitive (Int (dint_kind k))
    | TFloat k -> Primitive (Float (dfloat_kind k))
    | TStr -> Primitive Str
    | TApp { ident; args } ->
        B.App
          { head = dglobal_ident ident; args = List.map ~f:dgeneric_value args }
    | TArray { typ; length } -> Array { ty = dty typ; length = dexpr length }
    | TSlice { witness = _; ty } -> Slice (dty ty)
    | TRef { witness = _; typ; mut; region } ->
        Ref
          {
            inner = dty typ;
            mutable' = (match mut with Mutable _ -> true | _ -> false);
          }
    | TParam local_ident -> Param (dlocal_ident local_ident)
    | TArrow (inputs, output) ->
        Arrow { inputs = List.map ~f:dty inputs; output = dty output }
    | TAssociatedType { impl; item } ->
        AssociatedType { impl_ = dimpl_expr impl; item = dconcrete_ident item }
    | TOpaque ident -> Opaque (dconcrete_ident ident)
    | TRawPointer { witness = _ } -> RawPointer
    | TDyn { witness = _; goals } -> Dyn (List.map ~f:ddyn_trait_goal goals)

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
    { name = [%show: global_ident] gi }

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
        B.Parent
          { impl_ = dimpl_expr impl; item = todo () (* Rust AST needs fixing*) }
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
    | GLifetime { lt; witness = _ } -> B.Lifetime
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
    let kind =
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
        Ascription { pat = dpat pat; ty = dty typ; typ_span = dspan typ_span }
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

  and dspan (span : span) : B.span = EmptyStructspan
  and dfield_pat (_span : span) (p : A.field_pat) : missing_type = ()

  and dbinding_mode (binding_mode : A.binding_mode) : B.binding_mode =
    match binding_mode with
    | ByValue -> B.ByValue
    | ByRef (kind, _witness) -> B.ByRef (dborrow_kind kind)

  and dsupported_monads (m : A.supported_monads) : missing_type =
    match m with MException t -> () | MResult t -> () | MOption -> ()

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
    | Block { e; safety_mode = _; witness = _ } ->
        todo () (* Rust AST needs fixing *)
    | LocalVar id -> LocalId (dlocal_ident id)
    | GlobalVar id -> GlobalId (dglobal_ident id)
    | Ascription { e; typ } -> Ascription { e = dexpr e; ty = dty typ }
    | MacroInvokation _ -> todo ()
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
    | QuestionMark { e; return_typ = _; witness = _ } ->
        (* Rust AST needs fixing *)
        todo ()
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
            mutability = (match mut with Mutable _ -> true | _ -> false);
          }
    | Closure { params; body; captures } ->
        Closure
          {
            params = List.map ~f:dpat params;
            body = dexpr body;
            captures = List.map ~f:dexpr captures;
          }
    | EffectAction { action = _; argument } -> todo ()
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

  and dquote ({ contents; witness } : A.quote) : B.quote =
    let f = function
      | A.Verbatim code -> B.Verbatim code
      | A.Expr e -> B.Expr (dexpr e)
      | A.Pattern p -> B.Pattern (dpat p)
      | A.Typ t -> B.Typ (dty t)
    in
    Newtypequote (List.map ~f contents)

  and ditem_quote_origin (iqo : item_quote_origin) : B.item_quote_origin =
    {
      item_ident = dconcrete_ident iqo.item_ident;
      item_kind = todo ();
      (*Rust AST needs fixing*)
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
        B.ForLoop { it = dexpr it; pat = dpat pat }
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

  let dgeneric_param _span ({ ident; span; attrs; kind } : A.generic_param) :
      B.generic_param =
    let kind : B.generic_param_kind =
      match kind with
      | GPLifetime { witness = _ } -> Lifetime
      | GPType -> Type
      | GPConst { typ } -> Const { ty = dty typ }
    in
    (* { ident = local_ident; span; attrs; kind = A.generic_param_kind } *)
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
    | A.IMacroInvokation { macro; argument = _; span = _; witness = _ } ->
        todo ()
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
              [
                ( dconcrete_ident trait_id,
                  todo () (* List.map ~f:dgeneric_value trait_generics *) );
              ];
            (* Rust AST needs fixing*)
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
    | A.HaxError _ -> todo ()
    | A.NotImplementedYet -> B.NotImplementedYet
end [@warnerror "-27-26"]
