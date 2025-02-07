open Hax_engine
open Utils
open Base
open Coq_ast

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Slice
      include On.Monadic_binding
      include On.Macro
      include On.Construct_base
    end)
    (struct
      let backend = Diagnostics.Backend.Coq
    end)

module SubtypeToInputLanguage
    (FA : Features.T
            with type mutable_reference = Features.Off.mutable_reference
             and type continue = Features.Off.continue
             and type break = Features.Off.break
             and type mutable_reference = Features.Off.mutable_reference
             and type mutable_pointer = Features.Off.mutable_pointer
             and type mutable_variable = Features.Off.mutable_variable
             and type reference = Features.Off.reference
             and type raw_pointer = Features.Off.raw_pointer
             and type early_exit = Features.Off.early_exit
             and type question_mark = Features.Off.question_mark
             and type as_pattern = Features.Off.as_pattern
             and type lifetime = Features.Off.lifetime
             and type monadic_action = Features.Off.monadic_action
             and type arbitrary_lhs = Features.Off.arbitrary_lhs
             and type nontrivial_lhs = Features.Off.nontrivial_lhs
             and type block = Features.Off.block
             and type quote = Features.Off.quote
             and type dyn = Features.Off.dyn
             and type match_guard = Features.Off.match_guard
             and type trait_item_default = Features.Off.trait_item_default
             and type unsafe = Features.Off.unsafe
             and type loop = Features.Off.loop
             and type for_loop = Features.Off.for_loop
             and type while_loop = Features.Off.while_loop
             and type for_index_loop = Features.Off.for_index_loop
             and type state_passing_loop = Features.Off.state_passing_loop
             and type fold_like_loop = Features.Off.fold_like_loop) =
struct
  module FB = InputLanguage

  include
    Subtype.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Features.SUBTYPE.Id
        include Features.SUBTYPE.On.Monadic_binding
        include Features.SUBTYPE.On.Construct_base
        include Features.SUBTYPE.On.Slice
        include Features.SUBTYPE.On.Macro
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions
open Ast
module CoqNamePolicy = Concrete_ident.DefaultNamePolicy
module U = Ast_utils.Make (InputLanguage)
module RenderId = Concrete_ident.MakeRenderAPI (CoqNamePolicy)
open AST

let hardcoded_coq_headers =
  "(* File automatically generated by Hacspec *)\n\
   From Coq Require Import ZArith.\n\
   Require Import List.\n\
   Import List.ListNotations.\n\
   Open Scope Z_scope.\n\
   Open Scope bool_scope.\n\
   Require Import Ascii.\n\
   Require Import String.\n\
   Require Import Coq.Floats.Floats.\n\
   From RecordUpdate Require Import RecordSet.\n\
   Import RecordSetNotations.\n"

module BasePrinter = Generic_printer.Make (InputLanguage)

module Make
    (Default : sig
      val default : string -> string
    end)
    (Attrs : Attrs.WITH_ITEMS) =
struct
  open PPrint

  let default_string_for s = "TODO: please implement the method `" ^ s ^ "`"
  let default_document_for = default_string_for >> string

  module CoqNotation = struct
    let definition_struct keyword n name generics params typ body =
      keyword ^^ space ^^ name ^^ generics
      ^^ concat_map (fun x -> space ^^ x) params
      ^^ space ^^ colon ^^ space ^^ typ ^^ space ^^ string ":="
      ^^ nest n (break 1 ^^ body)
      ^^ dot

    let proof_struct keyword name generics params statement =
      keyword ^^ space ^^ name ^^ generics
      ^^ concat_map (fun x -> space ^^ x) params
      ^^ space ^^ colon
      ^^ nest 2 (break 1 ^^ statement ^^ dot)
      ^^ break 1 ^^ string "Proof" ^^ dot ^^ space ^^ string "Admitted" ^^ dot

    let definition = definition_struct (string "Definition") 2
    let fixpoint = definition_struct (string "Fixpoint") 2
    let inductive = definition_struct (string "Inductive") 0
    let record = definition_struct (string "Record") 2
    let instance = definition_struct (string "Instance") 2
    let class_ = definition_struct (string "Class") 2
    let lemma = proof_struct (string "Lemma")
  end

  type ('get_span_data, 'a) object_type =
    ('get_span_data, 'a) BasePrinter.Gen.object_type

  class printer =
    object (self)
      inherit BasePrinter.base

      method private primitive_to_string (id : primitive_ident) : document =
        match id with
        | Deref -> default_document_for "(TODO: Deref)"
        | Cast -> string "cast"
        | LogicalOp op -> (
            match op with And -> string "andb" | Or -> string "orb")

      method arm ~arm ~span:_ = arm#p

      method arm' ~super:_ ~arm_pat ~body ~guard:_ =
        arm_pat#p ^^ space ^^ string "=>" ^^ nest 2 (break 1 ^^ body#p)

      method attrs x1 = default_document_for "attrs"

      method binding_mode_ByRef _x1 _x2 =
        default_document_for "binding_mode_ByRef"

      method binding_mode_ByValue = default_document_for "binding_mode_ByValue"
      method borrow_kind_Mut _x1 = default_document_for "borrow_kind_Mut"
      method borrow_kind_Shared = default_document_for "borrow_kind_Shared"
      method borrow_kind_Unique = default_document_for "borrow_kind_Unique"
      method common_array x1 = brackets (separate (semi ^^ space) x1)

      method dyn_trait_goal ~trait:_ ~non_self_args:_ =
        default_document_for "dyn_trait_goal"

      method error_expr x1 = parens (string x1 ^^ string "(* ERROR_EXPR *)")
      method error_item x1 = parens (string x1 ^^ string "(* ERROR_ITEM *)")
      method error_pat x1 = parens (string x1 ^^ string "(* ERROR_PAT *)")
      method expr ~e ~span:_ ~typ = e#p

      method expr'_AddressOf ~super:_ ~mut:_ ~e:_ ~witness =
        match witness with _ -> .

      method expr'_App_application ~super:_ ~f ~args ~generics:_ =
        f#p ^^ concat_map (fun x -> space ^^ parens x#p) args

      method expr'_App_constant ~super:_ ~constant ~generics:_ = constant#p

      method expr'_App_field_projection ~super:_ ~field ~e =
        field#p ^^ space ^^ e#p

      method expr'_App_tuple_projection ~super:_ ~size:_ ~nth:_ ~e:_ =
        default_document_for "expr'_App_tuple_projection"

      method expr'_Ascription ~super:_ ~e ~typ =
        e#p ^^ space ^^ colon ^^ space ^^ typ#p

      method expr'_Assign ~super:_ ~lhs:_ ~e:_ ~witness =
        match witness with _ -> .

      method expr'_Block ~super:_ ~e:_ ~safety_mode:_ ~witness =
        match witness with _ -> .

      method expr'_Borrow ~super:_ ~kind:_ ~e:_ ~witness =
        match witness with _ -> .

      method expr'_Break ~super:_ ~e:_ ~acc:_ ~label:_ ~witness =
        match witness with _ -> .

      method expr'_Closure ~super:_ ~params ~body ~captures:_ =
        !^"fun"
        ^^ concat_map (fun x -> space ^^ x#p) params
        ^^ space ^^ !^"=>" ^^ space
        ^^ nest 2 (break 1 ^^ body#p)

      method expr'_Construct_inductive ~super:_ ~constructor ~is_record
          ~is_struct ~fields ~base =
        let fields_or_empty add_space =
          if List.is_empty fields then empty
          else
            add_space
            ^^ parens
                 (separate_map (comma ^^ space) (fun x -> (snd x)#p) fields)
        in
        if is_record && is_struct then
          match base with
          | Some x -> string "Build_" ^^ x#p ^^ fields_or_empty space
          | None -> string "Build_t_" ^^ constructor#p ^^ fields_or_empty space
        else if not is_record then
          if is_struct then
            string "Build_t_" ^^ constructor#p ^^ fields_or_empty space
          else constructor#p ^^ fields_or_empty space
        else
          default_document_for
            "expr'_Construct_inductive [is_record=true, is_struct = false] \
             todo record"

      method expr'_Construct_tuple ~super:_ ~components =
        if List.length components == 0 then !^"tt"
        else parens (separate_map comma (fun x -> x#p) components)

      method expr'_Continue ~super:_ ~acc:_ ~label:_ ~witness =
        match witness with _ -> .

      method expr'_EffectAction ~super:_ ~action:_ ~argument:_ =
        default_document_for "expr'_EffectAction"

      method expr'_GlobalVar_concrete ~super:_ x2 = x2#p
      method expr'_GlobalVar_primitive ~super:_ x2 = self#primitive_to_string x2

      method expr'_If ~super:_ ~cond ~then_ ~else_ =
        string "if"
        ^^ nest 2 (break 1 ^^ cond#p)
        ^^ break 1 ^^ string "then"
        ^^ nest 2 (break 1 ^^ then_#p)
        ^^ break 1 ^^ string "else"
        ^^ nest 2
             (break 1 ^^ match else_ with Some x -> x#p | None -> string "tt")

      method expr'_Let ~super:_ ~monadic:_ ~lhs ~rhs ~body =
        string "let" ^^ space ^^ lhs#p ^^ space ^^ string ":=" ^^ space ^^ rhs#p
        ^^ space ^^ string "in" ^^ break 1 ^^ body#p

      method expr'_Literal ~super:_ x2 = x2#p
      method expr'_LocalVar ~super:_ x2 = x2#p

      method expr'_Loop ~super:_ ~body ~kind ~state ~control_flow ~label:_
          ~witness:_ =
        kind#p ^^ space
        ^^ brackets
             (Option.value ~default:(string "is_none")
                (Option.map ~f:(fun x -> x#p) control_flow))
        ^^ Option.value ~default:(string "default")
             (Option.map ~f:(fun x -> x#p) state)
        ^^ space ^^ string "of" ^^ space
        ^^ parens (nest 2 (break 1 ^^ body#p))

      method expr'_MacroInvokation ~super:_ ~macro:_ ~args:_ ~witness:_ =
        default_document_for "expr'_MacroInvokation"

      method expr'_Match ~super:_ ~scrutinee ~arms =
        string "match" ^^ space ^^ scrutinee#p ^^ space ^^ string "with"
        ^^ break 1
        ^^ concat_map (fun x -> string "|" ^^ space ^^ x#p ^^ break 1) arms
        ^^ string "end"

      method expr'_QuestionMark ~super:_ ~e:_ ~return_typ:_ ~witness =
        match witness with _ -> .

      method expr'_Quote ~super:_ _x2 = default_document_for "expr'_Quote"
      method expr'_Return ~super:_ ~e:_ ~witness = match witness with _ -> .

      method cf_kind_BreakOrReturn =
        default_document_for "cf_kind_BreakOrReturn"

      method cf_kind_BreakOnly = default_document_for "cf_kind_BreakOnly"
      method field_pat ~field ~pat = pat#p

      method generic_constraint_GCLifetime _x1 _x2 =
        default_document_for "generic_constraint_GCLifetime"

      method generic_constraint_GCProjection x1 = string "`" ^^ braces x1#p
      method generic_constraint_GCType x1 = string "`" ^^ braces x1#p

      method generic_param ~ident ~span:_ ~attrs:_ ~kind =
        string "`" ^^ braces (ident#p ^^ space ^^ colon ^^ space ^^ kind#p)

      method generic_param_kind_GPConst ~typ = typ#p

      method generic_param_kind_GPLifetime ~witness =
        match witness with _ -> .

      method generic_param_kind_GPType = string "Type"
      method generic_value_GConst x1 = x1#p

      method generic_value_GLifetime ~lt:_ ~witness =
        match witness with _ -> .

      method generic_value_GType x1 = parens x1#p

      method generics ~params ~constraints =
        let params_document = concat_map (fun x -> space ^^ x#p) params in
        let constraints_document =
          concat_map (fun x -> space ^^ x#p) constraints
        in
        params_document ^^ constraints_document

      method guard ~guard:_ ~span:_ = default_document_for "guard"

      method guard'_IfLet ~super:_ ~lhs:_ ~rhs:_ ~witness =
        match witness with _ -> .

      method impl_expr ~kind:_ ~goal = goal#p

      method impl_expr_kind_Builtin _x1 =
        default_document_for "impl_expr_kind_Builtin"

      method impl_expr_kind_Concrete _x1 =
        default_document_for "impl_expr_kind_Concrete"

      method impl_expr_kind_Dyn = default_document_for "impl_expr_kind_Dyn"

      method impl_expr_kind_ImplApp ~impl:_ ~args:_ =
        default_document_for "impl_expr_kind_ImplApp"

      method impl_expr_kind_LocalBound ~id:_ =
        default_document_for "impl_expr_kind_LocalBound"

      method impl_expr_kind_Parent ~impl:_ ~ident:_ =
        default_document_for "impl_expr_kind_Parent"

      method impl_expr_kind_Projection ~impl:_ ~item:_ ~ident:_ =
        default_document_for "impl_expr_kind_Projection"

      method impl_expr_kind_Self = default_document_for "impl_expr_kind_Self"
      method impl_ident ~goal ~name:_ = goal#p

      method impl_item ~ii_span:_ ~ii_generics:_ ~ii_v ~ii_ident ~ii_attrs:_ =
        ii_ident#p ^^ space ^^ string ":=" ^^ space ^^ ii_v#p ^^ semi

      method impl_item'_IIFn ~body ~params =
        if List.length params == 0 then body#p
        else
          string "fun" ^^ space
          ^^ concat_map (fun x -> x#p ^^ space) params
          ^^ string "=>"
          ^^ nest 2 (break 1 ^^ body#p)

      method impl_item'_IIType ~typ ~parent_bounds:_ = typ#p
      method item ~v ~span:_ ~ident:_ ~attrs:_ = v#p ^^ break 1

      method item'_Alias ~super:_ ~name ~item =
        string "Notation" ^^ space ^^ string "\"'" ^^ name#p ^^ string "'\""
        ^^ space ^^ string ":=" ^^ space ^^ parens item#p ^^ dot

      method item'_Fn ~super ~name ~generics ~body ~params ~safety:_ =
        (* TODO: Why is type not available here ? *)
        let is_rec =
          Set.mem
            (U.Reducers.collect_concrete_idents#visit_expr () body#v)
            name#v
        in
        let typ =
          self#_do_not_override_lazy_of_ty AstPos_item'_Fn_body body#v.typ
        in

        let get_expr_of kind f : document option =
          Attrs.associated_expr kind super.attrs
          |> Option.map ~f:(self#entrypoint_expr >> f)
        in
        let requires =
          get_expr_of Requires (fun x ->
              x ^^ space ^^ string "=" ^^ space ^^ string "true")
        in
        let ensures =
          get_expr_of Ensures (fun x ->
              x ^^ space ^^ string "=" ^^ space ^^ string "true")
        in

        let is_lemma = Attrs.lemma super.attrs in
        if is_lemma then
          CoqNotation.lemma name#p generics#p
            (List.map ~f:(fun x -> x#p) params)
            (Option.value ~default:empty requires
            ^^ space ^^ !^"->" ^^ break 1
            ^^ Option.value ~default:empty ensures)
        else if is_rec then
          CoqNotation.fixpoint name#p generics#p
            (List.map ~f:(fun x -> x#p) params
            @ Option.value ~default:[]
                (Option.map ~f:(fun x -> [ string "`" ^^ braces x ]) requires))
            typ#p body#p (* ^^ TODO: ensures? *)
        else
          CoqNotation.definition name#p generics#p
            (List.map ~f:(fun x -> x#p) params
            @ Option.value ~default:[]
                (Option.map ~f:(fun x -> [ string "`" ^^ braces x ]) requires))
            typ#p body#p (* ^^ TODO: ensures? *)

      method item'_HaxError ~super:_ _x2 = default_document_for "item'_HaxError"

      method item'_IMacroInvokation ~super:_ ~macro:_ ~argument:_ ~span:_
          ~witness:_ =
        default_document_for "item'_IMacroInvokation"

      method item'_Impl ~super ~generics ~self_ty ~of_trait ~items
          ~parent_bounds:_ ~safety:_ =
        let name, args = of_trait#v in
        if Attrs.is_erased super.attrs then empty
        else
          CoqNotation.instance
            (name#p ^^ string "_"
            ^^ string (Int.to_string ([%hash: item] super)))
            generics#p []
            (name#p ^^ concat_map (fun x -> space ^^ parens x#p) args)
            (braces
               (nest 2
                  (concat_map
                     (fun x -> break 1 ^^ name#p ^^ !^"_" ^^ x#p)
                     items)
               ^^ break 1))

      method item'_NotImplementedYet = string "(* NotImplementedYet *)"

      method item'_Quote ~super:_ ~quote:_ ~origin:_ =
        default_document_for "item'_Quote"

      method item'_Trait ~super:_ ~name ~generics ~items ~safety:_ =
        let _, params, constraints = generics#v in
        CoqNotation.class_ name#p generics#p [] !^"Type"
          (braces
             (nest 2 (concat_map (fun x -> break 1 ^^ x#p) items) ^^ break 1))
        ^^ break 1 ^^ !^"Arguments" ^^ space ^^ name#p ^^ colon
        ^^ !^"clear implicits" ^^ dot ^^ break 1 ^^ !^"Arguments" ^^ space
        ^^ name#p
        ^^ concat_map (fun _ -> space ^^ !^"(_)") params
        ^^ concat_map (fun _ -> space ^^ !^"{_}") constraints
        ^^ dot

      method item'_TyAlias ~super:_ ~name ~generics:_ ~ty =
        string "Notation" ^^ space ^^ string "\"'" ^^ name#p ^^ string "'\""
        ^^ space ^^ string ":=" ^^ space ^^ ty#p ^^ dot

      method item'_Type_struct ~super:_ ~name ~generics ~tuple_struct:_
          ~arguments =
        CoqNotation.record name#p generics#p [] (string "Type")
          (braces
             (nest 2
                (concat_map
                   (fun (ident, typ, attr) ->
                     break 1 ^^ ident#p ^^ space ^^ colon ^^ space ^^ typ#p
                     ^^ semi)
                   arguments)
             ^^ break 1))
        ^^ break 1 ^^ !^"Arguments" ^^ space ^^ name#p ^^ colon
        ^^ !^"clear implicits" ^^ dot ^^ break 1 ^^ !^"Arguments" ^^ space
        ^^ name#p
        ^^ concat_map (fun _ -> space ^^ !^"(_)") generics#v.params
        ^^ concat_map (fun _ -> space ^^ !^"{_}") generics#v.constraints
        ^^ dot ^^ break 1 ^^ !^"Arguments" ^^ space ^^ !^"Build_" ^^ name#p
        ^^ concat_map (fun _ -> space ^^ !^"{_}") generics#v.params
        ^^ concat_map (fun _ -> space ^^ !^"{_}") generics#v.constraints
        ^^ dot ^^ break 1 ^^ !^"#[export]" ^^ space
        ^^ CoqNotation.instance
             (string "settable" ^^ string "_" ^^ name#p)
             generics#p []
             (!^"Settable" ^^ space ^^ !^"_")
             (string "settable!" ^^ space
             ^^ parens (!^"@" ^^ !^"Build_" ^^ name#p ^^ generics#p)
             ^^ space ^^ string "<"
             ^^ separate_map (semi ^^ space)
                  (fun (ident, typ, attr) -> ident#p)
                  arguments
             ^^ string ">")

      method item'_Type_enum ~super:_ ~name ~generics ~variants =
        CoqNotation.inductive name#p generics#p [] (string "Type")
          (separate_map (break 1)
             (fun x -> string "|" ^^ space ^^ x#p)
             variants)
        ^^ break 1 ^^ !^"Arguments" ^^ space ^^ name#p ^^ colon
        ^^ !^"clear implicits" ^^ dot ^^ break 1 ^^ !^"Arguments" ^^ space
        ^^ name#p
        ^^ concat_map (fun _ -> space ^^ !^"(_)") generics#v.params
        ^^ concat_map (fun _ -> space ^^ !^"{_}") generics#v.constraints
        ^^ dot

      method item'_Use ~super:_ ~path ~is_external ~rename:_ =
        if List.length path == 0 || is_external then empty
        else
          let crate =
            String.capitalize
              (Option.value ~default:"(TODO CRATE)"
                 (Option.bind ~f:List.hd current_namespace))
          in
          let concat_capitalize l =
            String.concat ~sep:"_" (List.map ~f:String.capitalize l)
          in
          let concat_capitalize_include l =
            concat_capitalize (List.drop_last_exn l)
            ^ " (t_" ^ List.last_exn l ^ ")"
          in
          let path_string =
            match path with
            | "crate" :: xs -> concat_capitalize_include (crate :: xs)
            | "super" :: xs ->
                concat_capitalize
                  (crate
                   :: List.drop_last_exn
                        (Option.value ~default:[]
                           (Option.bind ~f:List.tl current_namespace))
                  @ xs)
            | [ a ] -> a
            | xs -> concat_capitalize_include xs
          in
          if String.is_empty path_string then empty
          else
            string "From" ^^ space ^^ string crate ^^ space
            ^^ string "Require Import" ^^ space ^^ string path_string ^^ dot
            ^^ break 1 ^^ string "Export" ^^ space ^^ string path_string ^^ dot

      method item_quote_origin ~item_kind:_ ~item_ident:_ ~position:_ =
        default_document_for "item_quote_origin"

      method lhs_LhsArbitraryExpr ~e:_ ~witness = match witness with _ -> .

      method lhs_LhsArrayAccessor ~e:_ ~typ:_ ~index:_ ~witness =
        match witness with _ -> .

      method lhs_LhsFieldAccessor_field ~e:_ ~typ:_ ~field:_ ~witness =
        match witness with _ -> .

      method lhs_LhsFieldAccessor_tuple ~e:_ ~typ:_ ~nth:_ ~size:_ ~witness =
        match witness with _ -> .

      method lhs_LhsLocalVar ~var:_ ~typ:_ =
        default_document_for "lhs_LhsLocalVar"

      method literal_Bool x1 = string (if x1 then "true" else "false")

      method literal_Char x1 =
        string "\"" ^^ string (Char.escaped x1) ^^ string "\"" ^^ string "%char"

      method literal_Float ~value ~negative ~kind:_ =
        (if negative then !^"-" else empty) ^^ string value ^^ string "%float"

      method literal_Int ~value ~negative ~kind:_ =
        (if negative then !^"-" else empty) ^^ string value

      method literal_String x1 = string "\"" ^^ string x1 ^^ string "\"%string"

      method loop_kind_ForIndexLoop ~start:_ ~end_:_ ~var:_ ~var_typ:_ ~witness
          =
        default_document_for "loop_kind_ForIndexLoop"

      method loop_kind_ForLoop ~pat ~it ~witness =
        braces it#p ^^ space ^^ string "inP?" ^^ space ^^ brackets pat#p

      method loop_kind_UnconditionalLoop =
        default_document_for "loop_kind_UnconditionalLoop"

      method loop_kind_WhileLoop ~condition:_ ~witness:_ =
        default_document_for "loop_kind_WhileLoop"

      method loop_state ~init ~bpat ~witness:_ =
        parens (init#p ^^ space ^^ !^"state" ^^ space ^^ bpat#p)

      method modul x1 = separate_map (break 1) (fun x -> x#p) x1

      method param ~pat ~typ ~typ_span:_ ~attrs:_ =
        parens (pat#p ^^ space ^^ colon ^^ space ^^ typ#p)

      method pat ~p ~span:_ ~typ:_ = p#p

      method pat'_PAscription ~super:_ ~typ ~typ_span:_ ~pat =
        pat#p ^^ space ^^ colon ^^ space ^^ typ#p

      method pat'_PBinding ~super:_ ~mut:_ ~mode:_ ~var ~typ:_ ~subpat:_ = var#p
      method pat'_PConstant ~super:_ ~lit = lit#p

      method pat'_PConstruct_inductive ~super:_ ~constructor ~is_record
          ~is_struct ~fields =
        if is_record then
          constructor#p ^^ space
          ^^ parens
               (separate_map (comma ^^ space)
                  (fun field_pat -> (snd field_pat)#p)
                  fields)
        else
          (if is_struct then string "Build_t_" else empty)
          ^^ constructor#p
          ^^ concat_map (fun (ident, exp) -> space ^^ parens exp#p) fields

      method pat'_PConstruct_tuple ~super:_ ~components =
        (* TODO: Only add `'` if you are a top-level pattern *)
        (* string "'" ^^ *)
        parens (separate_map comma (fun x -> x#p) components)

      method pat'_PDeref ~super:_ ~subpat:_ ~witness:_ =
        default_document_for "pat'_PDeref"

      method pat'_PWild = string "_"
      method printer_name = "Coq printer"

      method projection_predicate ~impl:_ ~assoc_item ~typ =
        string "_" (* TODO: name of impl#p *) ^^ dot
        ^^ parens assoc_item#p ^^ space ^^ string "=" ^^ space ^^ typ#p

      method safety_kind_Safe = default_document_for "safety_kind_Safe"
      method safety_kind_Unsafe _x1 = default_document_for "safety_kind_Unsafe"

      method supported_monads_MException _x1 =
        default_document_for "supported_monads_MException"

      method supported_monads_MOption =
        default_document_for "supported_monads_MOption"

      method supported_monads_MResult _x1 =
        default_document_for "supported_monads_MResult"

      method trait_goal ~trait ~args =
        trait#p ^^ concat_map (fun x -> space ^^ x#p) args

      method trait_item ~ti_span:_ ~ti_generics ~ti_v ~ti_ident ~ti_attrs:_ =
        let _, params, constraints = ti_generics#v in
        let generic_params = concat_map (fun x -> space ^^ x#p) params in
        let filter_constraints = function
          | GCProjection { impl = { goal = { trait; _ }; _ }; _ } -> true
          | GCType
              {
                goal = { trait; args = [ GType (TAssociatedType { item; _ }) ] };
                _;
              } ->
              Concrete_ident.(item == ti_ident#v)
          | _ -> true
        in
        let generic_constraints_other =
          concat_map
            (fun x -> space ^^ self#entrypoint_generic_constraint x)
            (List.filter ~f:filter_constraints
               (List.map ~f:(fun x -> x#v) constraints))
        in
        let generic_constraints_self =
          concat_map
            (fun x ->
              break 1 ^^ string "_" ^^ space ^^ string "::" ^^ space
              ^^ self#entrypoint_generic_constraint x
              ^^ semi)
            (List.filter
               ~f:(fun x -> not (filter_constraints x))
               (List.map ~f:(fun x -> x#v) constraints))
        in
        ti_ident#p ^^ generic_params ^^ generic_constraints_other ^^ space
        ^^ (match ti_v#v with TIDefault _ -> string ":=" | _ -> colon)
        ^^ space ^^ ti_v#p ^^ semi ^^ generic_constraints_self

      method trait_item'_TIDefault ~params ~body ~witness:_ =
        (if List.is_empty params then empty
         else
           string "fun" ^^ space
           ^^ separate_map space (fun x -> x#p) params
           ^^ space ^^ string "=>")
        ^^ nest 2 (break 1 ^^ body#p)

      method trait_item'_TIFn x1 = x1#p
      method trait_item'_TIType x1 = string "Type"

      method ty_TApp_application ~typ ~generics =
        typ#p ^^ concat_map (fun x -> space ^^ parens x#p) generics

      method ty_TApp_tuple ~types =
        if List.length types == 0 then string "unit"
        else parens (separate_map star (fun x -> self#entrypoint_ty x) types)

      method ty_TArray ~typ ~length =
        string "t_Array" ^^ space ^^ parens typ#p ^^ space ^^ parens length#p

      method ty_TArrow x1 x2 =
        concat_map (fun x -> x#p ^^ space ^^ string "->" ^^ space) x1 ^^ x2#p

      method ty_TAssociatedType ~impl:_ ~item = item#p
      method ty_TBool = string "bool"
      method ty_TChar = string "ascii"
      method ty_TDyn ~witness:_ ~goals:_ = default_document_for "ty_TDyn"
      method ty_TFloat _x1 = string "float"

      method ty_TInt x1 =
        string "t_"
        ^^
        match x1 with
        | { size; signedness } -> (
            (match signedness with
            | Unsigned -> string "u"
            | Signed -> string "i")
            ^^
            match size with
            | S8 -> string "8"
            | S16 -> string "16"
            | S32 -> string "32"
            | S64 -> string "64"
            | S128 -> string "128"
            | SSize -> string "size")

      method ty_TOpaque x1 = x1#p
      method ty_TParam x1 = x1#p
      method ty_TRawPointer ~witness:_ = default_document_for "ty_TRawPointer"

      method ty_TRef ~witness:_ ~region:_ ~typ:_ ~mut:_ =
        default_document_for "ty_TRef"

      method ty_TSlice ~witness:_ ~ty = !^"t_Slice" ^^ space ^^ ty#p
      method ty_TStr = string "string"

      method item'_Enum_Variant ~name ~arguments ~is_record ~attrs:_ =
        if is_record then
          concat_map
            (fun (ident, typ, attr) ->
              ident#p ^^ space ^^ colon ^^ space ^^ typ#p)
            arguments
          ^^ semi
        else if List.length arguments == 0 then name#p
        else
          name#p ^^ space ^^ colon ^^ space
          ^^ separate_map
               (space ^^ string "->" ^^ space)
               (fun (ident, typ, attr) -> typ#p)
               arguments
          ^^ space ^^ string "->" ^^ space ^^ string "_"

      method module_path_separator = "."

      method concrete_ident ~local:_ id : document =
        string
          (match id.name with
          | "not" -> "negb"
          | "eq" -> "t_PartialEq_f_eq"
          | "lt" -> "t_PartialOrd_f_lt"
          | "gt" -> "t_PartialOrd_f_gt"
          | "le" -> "t_PartialOrd_f_le"
          | "ge" -> "t_PartialOrd_f_ge"
          | "rem" -> "t_Rem_f_rem"
          | "add" -> "t_Add_f_add"
          | "mul" -> "t_Mul_f_mul"
          | "div" -> "t_Div_f_div"
          | x -> x)
    end

  let new_printer : BasePrinter.finalized_printer =
    BasePrinter.finalize (fun () -> (new printer :> BasePrinter.printer))
end

module type S = sig
  val new_printer : BasePrinter.finalized_printer
end

let make (module M : Attrs.WITH_ITEMS) =
  let open (
    Make
      (struct
        let default x = x
      end)
      (M) :
      S) in
  new_printer

let translate m _ ~bundles:_ (items : AST.item list) : Types.file list =
  let my_printer = make m in
  U.group_items_by_namespace items
  |> Map.to_alist
  |> List.filter_map ~f:(fun (_, items) ->
         let* first_item = List.hd items in
         Some ((RenderId.render first_item.ident).path, items))
  |> List.map ~f:(fun (ns, items) ->
         let mod_name =
           String.concat ~sep:"_"
             (List.map ~f:(map_first_letter String.uppercase) ns)
         in
         let sourcemap, contents =
           let annotated = my_printer#entrypoint_modul items in
           let open Generic_printer.AnnotatedString in
           let header = pure (hardcoded_coq_headers ^ "\n") in
           let annotated = concat header annotated in
           (to_sourcemap annotated, to_string annotated)
         in
         let sourcemap = Some sourcemap in
         let path = mod_name ^ ".v" in
         Types.{ path; contents; sourcemap })

open Phase_utils

module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.Unsafe(Features.Rust)
  |> Phases.Reject.RawOrMutPointer
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_asserts
  |> Phases.Reconstruct_for_loops
  |> Phases.Direct_and_mut
  |> Phases.Reject.Arbitrary_lhs
  |> Phases.Drop_blocks
  |> Phases.Drop_match_guards
  |> Phases.Reject.Continue
  |> Phases.Drop_references
  |> Phases.Trivialize_assign_lhs
  |> Phases.Reconstruct_question_marks
  |> Side_effect_utils.Hoist
  |> Phases.Local_mutation
  |> Phases.Reject.Continue
  |> Phases.Cf_into_monads
  |> Phases.Reject.EarlyExit
  |> Phases.Functionalize_loops
  |> Phases.Reject.As_pattern
  |> Phases.Reject.Dyn
  |> Phases.Reject.Trait_item_default
  |> Phases.Bundle_cycles
  |> Phases.Sort_items
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]

let apply_phases (_bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems items
