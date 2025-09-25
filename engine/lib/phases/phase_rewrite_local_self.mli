(** Rewrites, in traits and impls, local bounds refereing to `Self` into the
    impl expr of kind `Self`. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
