module Make (F : Features.T) : sig
  include module type of struct
    module FB = struct
      include F
      include Features.Off.Trait_impls
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
    module FA = F
  end

  include ImplemT.T
end
