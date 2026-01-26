(** This phase adds explicit conversions from Vec to slice, instead of
    conversions by taking references, which are erased by the phase
    DropReferences. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
