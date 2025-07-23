open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let discard (trait : Ast.concrete_ident) =
        let hax_core_models_extraction =
          Sys.getenv "HAX_CORE_MODELS_EXTRACTION_MODE"
          |> [%equal: string option] (Some "on")
        in

        Concrete_ident.eq_name Core__marker__Sized trait
        || hax_core_models_extraction
           && (Concrete_ident.eq_name Core__clone__Clone trait
              || Concrete_ident.eq_name Core__ops__function__Fn trait
              || Concrete_ident.eq_name Core__marker__Copy trait
              || Concrete_ident.eq_name Core__marker__StructuralPartialEq trait
              || Concrete_ident.eq_name Core__cmp__PartialEq trait
              || Concrete_ident.eq_name Core__cmp__Eq trait
              || Concrete_ident.eq_name Core__cmp__PartialOrd trait
              || Concrete_ident.eq_name Core__cmp__Ord trait)

      let visitor =
        let keep (ii : impl_ident) = discard ii.goal.trait |> not in
        object
          inherit [_] Visitors.map as super

          method! visit_generics () generics =
            let generics = super#visit_generics () generics in
            {
              generics with
              constraints =
                List.filter
                  ~f:(function GCType ii -> keep ii | _ -> true)
                  generics.constraints;
            }

          method! visit_item' () item' =
            let item' = super#visit_item' () item' in
            match item' with
            | Impl payload ->
                Impl
                  {
                    payload with
                    parent_bounds =
                      List.filter ~f:(snd >> keep) payload.parent_bounds;
                  }
            | _ -> item'

          method! visit_trait_item' () ti' =
            let ti' = super#visit_trait_item' () ti' in
            match ti' with
            | TIType impl_idents -> TIType (List.filter ~f:keep impl_idents)
            | _ -> ti'

          method! visit_impl_item' () ii' =
            let ii' = super#visit_impl_item' () ii' in
            match ii' with
            | IIType payload ->
                IIType
                  {
                    payload with
                    parent_bounds =
                      List.filter ~f:(snd >> keep) payload.parent_bounds;
                  }
            | _ -> ii'
        end

      let ditems =
        List.filter ~f:(fun item ->
            match item.v with
            | Impl { of_trait = tr, _; _ } when discard tr -> false
            | _ -> true)
        >> List.map ~f:(visitor#visit_item ())
    end)
