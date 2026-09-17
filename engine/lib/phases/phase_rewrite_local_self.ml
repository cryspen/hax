open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      open Ast
      open Ast.Make (F)
      module U = Ast_utils.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      module Attrs = Attr_payloads.Make (F) (Error)

      let in_trait_item =
        object
          inherit [_] U.Visitors.map as super

          method! visit_impl_expr () ie =
            match super#visit_impl_expr () ie with
            | { kind = LocalBound { id }; _ } when [%eq: string] id "i0" ->
                { ie with kind = Self }
            | ie -> ie
        end

      (* A `requires`/`ensures` clause is a standalone function taking the trait
         it constrains as an ordinary bound, so that bound is `Self` as well.
         Matching on the bound's goal rather than on its name keeps a method's
         own type parameters, which may be bounded by the same trait, apart. *)
      let in_clause (trait : concrete_ident) (generics : generics) =
        let dummy_self =
          List.find generics.params ~f:[%matches? { kind = GPType; _ }]
          |> Option.map ~f:(fun (p : generic_param) -> p.ident.name)
        in
        object
          inherit [_] U.Visitors.map as super

          method! visit_impl_expr () ie =
            match super#visit_impl_expr () ie with
            | {
                kind = LocalBound _;
                goal = { trait = trait'; args = GType (TParam p) :: _ };
              } as ie
              when [%eq: concrete_ident] trait' trait
                   && [%eq: string option] (Some p.name) dummy_self ->
                { ie with kind = Self }
            | ie -> ie
        end

      let ditems (l : item list) : item list =
        let (module Attrs) = Attrs.with_items l in
        (* A clause is a standalone item that its trait item points to through
           an attribute, so visiting the trait alone does not reach it. *)
        let clause_traits =
          List.concat_map l ~f:(fun i ->
              match i.v with
              | Trait { name; items; _ } ->
                  List.concat_map items ~f:(fun ti ->
                      Attr_payloads.AssocRole.[ Requires; Ensures ]
                      |> List.concat_map ~f:(fun role ->
                          Attrs.associated_items role ti.ti_attrs)
                      |> List.map ~f:(fun clause -> (clause.ident, name)))
              | _ -> [])
        in
        let trait_of (i : item) =
          List.Assoc.find clause_traits i.ident ~equal:[%eq: concrete_ident]
        in
        List.map l ~f:(fun i ->
            match (i.v, trait_of i) with
            | Trait ({ items; _ } as t), _ ->
                let items =
                  List.map ~f:(in_trait_item#visit_trait_item ()) items
                in
                { i with v = Trait { t with items } }
            | Fn { generics; _ }, Some trait ->
                (in_clause trait generics)#visit_item () i
            | _ -> i)
    end)
