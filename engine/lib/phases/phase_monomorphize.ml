open! Prelude

module%inlined_contents Make (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.Off.Trait_impls
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  module A = Ast.Make (FA)
  module B = Ast.Make (FB)
  module AVisitors = Ast_visitors.Make (FA)
  module BVisitors = Ast_visitors.Make (FB)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    let rename_trait_impl_calls (f : A.ty -> concrete_ident -> concrete_ident) =
      (object
         inherit [_] AVisitors.map as super
         method! visit_concrete_ident (typ : A.ty) ident = f typ ident

         method! visit_global_ident typ (x : Global_ident.t) =
           match x with
           | `Concrete x -> `Concrete (f typ x)
           | `Projector (`Concrete x) -> `Projector (`Concrete (f typ x))
           | _ -> super#visit_global_ident typ x

         method! visit_expr _ e = match e.e with _ -> super#visit_expr e.typ e
      end)
        #visit_item
        TBool (* Dummy value *)

    let ditems (items : A.item list) : B.item list =
      let items =
        List.map
          ~f:
            (rename_trait_impl_calls (fun _typ ident ->
                 ident (* change name here *)))
          items
      in
      List.bind items ~f:(fun x ->
          match x.v with
          | Impl _ -> []
          | Trait _ -> []
          | _ -> [ Stdlib.Obj.magic x ])

    let dexpr (_e : A.expr) : B.expr =
      Stdlib.failwith "Should not be called directly"
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

(* phase_and_mut_defsite.ml *)
