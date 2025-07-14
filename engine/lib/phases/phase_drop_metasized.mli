(** This phase gets rid of the MetaSized bound. See https://github.com/cryspen/hax/pull/1534. *)

open! Prelude

module Make (F : Features.T) : sig
  include module type of struct
    module FA = F
    module FB = FA
    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
