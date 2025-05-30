(** This phase re-order fields in structs according to the attribute [AttrPayload::Order] (if any). *)

open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module M = Ast_builder.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      module Attrs = Attr_payloads.MakeBase (Error)

      let order_of_argument = thd3 >> Attrs.order

      let ditems =
        List.map ~f:(fun item ->
            match item.v with
            | Type ({ variants; _ } as o) ->
                let variants =
                  let f (v : variant) =
                    let arguments =
                      List.mapi
                        ~f:(fun i ->
                          order_of_argument >> Option.value ~default:i &&& Fn.id)
                        v.arguments
                      |> List.stable_sort ~compare:(fun (i, _) (j, _) ->
                             Int.compare i j)
                      |> List.map ~f:snd
                    in
                    { v with arguments }
                  in
                  List.map ~f variants
                in
                { item with v = Type { o with variants } }
            | _ -> item)
    end)
