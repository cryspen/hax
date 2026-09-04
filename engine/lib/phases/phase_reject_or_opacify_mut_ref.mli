(** Handles mutable references that escape the functionalization subset, ahead of
    [Direct_and_mut] (whose analysis diverges on such bodies). A [&mut] in the
    return type leaves the signature un-stateable, so the item is excluded; a
    local bound to two or more aliased [&mut] values (as [split_at_mut] and
    friends produce) only affects the body, so the body is opacified (admitted,
    signature kept). This is a syntactic over-approximation: it admits bodies the
    engine may one day functionalize. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
