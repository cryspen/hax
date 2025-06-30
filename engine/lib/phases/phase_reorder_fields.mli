(** This phase re-order fields in structs according to the attribute [AttrPayload::Order] (if any). *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
