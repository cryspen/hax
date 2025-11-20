open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      open Ast.Make (F)
      module U = Ast_utils.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let ditem i =
        match i.v with
        | Trait ({ items; _ } as t) ->
            let items =
              List.map
                ~f:
                  ((object
                      inherit [_] U.Visitors.map as super

                      method! visit_impl_expr () ie =
                        match super#visit_impl_expr () ie with
                        | { kind = LocalBound { id }; _ }
                          when [%eq: string] id "i0" ->
                            { ie with kind = Self }
                        | ie -> ie
                   end)
                     #visit_trait_item
                     ())
                items
            in
            { i with v = Trait { t with items } }
        | _ -> i

      let ditems = List.map ~f:ditem
    end)
