(** This phase gets rid of the MetaSized bound. See https://github.com/cryspen/hax/pull/1534. *)

open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F
  module FB = FA

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  module UA = Ast_utils.Make (F)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    [%%inline_defs dmutability + dsafety_kind]

    let rec dimpl_expr (span : span) (i : A.impl_expr) : B.impl_expr option =
      let* kind = dimpl_expr_kind span i.kind in
      let* goal = dtrait_goal span i.goal in
      Some B.{ kind; goal }

    and dtrait_goal (span : span) (r : A.trait_goal) : B.trait_goal option =
      let*? _ = not (Concrete_ident.eq_name Core__marker__MetaSized r.trait) in
      Some
        B.{ trait = r.trait; args = List.map ~f:(dgeneric_value span) r.args }

    and dimpl_expr_exn message span i =
      match dimpl_expr span i with
      | None -> Error.assertion_failure span message
      | Some impl -> impl

    and dimpl_ident (span : span) (r : A.impl_ident) : B.impl_ident option =
      let* goal = dtrait_goal span r.goal in
      Some B.{ goal; name = r.name }

    and dty (span : span) (ty : A.ty) : B.ty =
      match ty with
      | TAssociatedType { impl; item } ->
          let impl =
            dimpl_expr_exn "MetaSized has no associated type" span impl
          in
          TAssociatedType { impl; item }
      | [%inline_arms "dty.*" - TAssociatedType] -> auto

    and dprojection_predicate (span : span) (r : A.projection_predicate) :
        B.projection_predicate =
      {
        impl = dimpl_expr_exn "MetaSized cannot be projected" span r.impl;
        assoc_item = r.assoc_item;
        typ = dty span r.typ;
      }

    and dimpl_expr_kind (span : span) (i : A.impl_expr_kind) :
        B.impl_expr_kind option =
      match i with
      | Parent { impl; ident } ->
          let* impl = dimpl_expr span impl in
          let* ident = dimpl_ident span ident in
          Some (B.Parent { impl; ident })
      | Projection { impl; item; ident } ->
          let impl = dimpl_expr_exn "MetaSized have no projection" span impl in
          let* ident = dimpl_ident span ident in
          Some (B.Projection { impl; item; ident })
      | ImplApp { impl; args } ->
          let* impl = dimpl_expr span impl in
          let args = List.filter_map ~f:(dimpl_expr span) args in
          Some (B.ImplApp { impl; args })
      | Builtin tr ->
          let* tr = dtrait_goal span tr in
          Some (B.Builtin tr)
      | Concrete tr ->
          let* tr = dtrait_goal span tr in
          Some (B.Concrete tr)
      | [%inline_arms
          "dimpl_expr_kind.*" - Parent - Projection - ImplApp - Builtin
          - Concrete] ->
          map (fun x ->
              Some
                (let result : B.impl_expr_kind = x in
                 result))

    and dexpr' (span : span) (expr : A.expr') : B.expr' =
      match expr with
      | App { f; args; generic_args; bounds_impls; trait } ->
          let dgeneric_values = List.map ~f:(dgeneric_value span) in
          App
            {
              f = dexpr f;
              args = List.map ~f:dexpr args;
              generic_args = dgeneric_values generic_args;
              bounds_impls = List.filter_map ~f:(dimpl_expr span) bounds_impls;
              trait =
                Option.map
                  ~f:
                    (dimpl_expr_exn "MetaSized have no method" span
                    *** dgeneric_values)
                  trait;
            }
      | [%inline_arms "dexpr'.*" - App] -> auto
    [@@inline_ands
      bindings_of dty - dimpl_expr - dexpr' - dprojection_predicate
      - dimpl_expr_kind - dty - dimpl_ident]

    let rec dimpl_item' (span : span) (ii : A.impl_item') : B.impl_item' =
      match ii with
      | IIType { typ; parent_bounds } ->
          IIType
            {
              typ = dty span typ;
              parent_bounds =
                List.filter_map
                  ~f:(fun (impl, ident) ->
                    let* impl = dimpl_expr span impl in
                    let* ident = dimpl_ident span ident in
                    Some (impl, ident))
                  parent_bounds;
            }
          (* | _ -> Obj.magic () *)
      | [%inline_arms "dimpl_item'.*" - IIType] -> auto

    and dtrait_item' (span : span) (ti : A.trait_item') : B.trait_item' =
      match ti with
      | TIType idents -> TIType (List.filter_map ~f:(dimpl_ident span) idents)
      | [%inline_arms "dtrait_item'.*" - TIType] -> auto

    and dgeneric_constraint (span : span)
        (generic_constraint : A.generic_constraint) :
        B.generic_constraint option =
      match generic_constraint with
      | GCLifetime (lf, witness) ->
          Some (B.GCLifetime (lf, S.lifetime span witness))
      | GCType impl_ident ->
          let* impl = dimpl_ident span impl_ident in
          Some (B.GCType impl)
      | GCProjection projection ->
          Some (B.GCProjection (dprojection_predicate span projection))

    and dgenerics (span : span) (g : A.generics) : B.generics =
      {
        params = List.map ~f:(dgeneric_param span) g.params;
        constraints =
          List.filter_map ~f:(dgeneric_constraint span) g.constraints;
      }

    and ditem' (span : span) (item : A.item') : B.item' =
      match item with
      | Impl
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
              generics = dgenerics span generics;
              self_ty = dty span self_ty;
              of_trait =
                (trait_id, List.map ~f:(dgeneric_value span) trait_generics);
              items = List.map ~f:dimpl_item items;
              parent_bounds =
                List.filter_map
                  ~f:(fun (impl, ident) ->
                    let* impl = dimpl_expr span impl in
                    let* ident = dimpl_ident span ident in
                    Some (impl, ident))
                  parent_bounds;
              safety = dsafety_kind span safety;
            }
      | [%inline_arms "ditem'.*" - Impl] -> auto
    [@@inline_ands
      "Item.*" - ditem' - dimpl_item' - dtrait_item' - dgeneric_constraint
      - dgenerics]

    [%%inline_defs ditems]
  end

  include Implem
end
[@@add "subtype.ml"]
