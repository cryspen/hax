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
        | Trait { name; generics; _ } ->
            let generic_eq (param : generic_param) (value : generic_value) =
              (let* id =
                 match (param.kind, value) with
                 | GPConst _, GConst { e = LocalVar id; _ } -> Some id
                 | GPType, GType (TParam id) -> Some id
                 | GPLifetime _, GLifetime _ -> Some param.ident
                 | _ -> None
               in
               Some ([%eq: Ast.local_ident] id param.ident))
              |> Option.value ~default:false
            in
            let generics_eq params values =
              match List.for_all2 ~f:generic_eq params values with
              | List.Or_unequal_lengths.Ok v -> v
              | List.Or_unequal_lengths.Unequal_lengths -> false
            in
            (object
               inherit [_] U.Visitors.map as super

               method! visit_impl_expr () ie =
                 match super#visit_impl_expr () ie with
                 | { kind = LocalBound _; goal = { args; trait } }
                   when [%eq: Ast.concrete_ident] trait name
                        && generics_eq generics.params args ->
                     { ie with kind = Self }
                 | ie -> ie
            end)
              #visit_item
              () i
        | _ -> i

      let ditems = List.map ~f:ditem
    end)
