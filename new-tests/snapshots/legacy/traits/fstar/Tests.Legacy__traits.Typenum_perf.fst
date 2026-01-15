module Tests.Legacy__traits.Typenum_perf
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Typenum.Type_operators in
  ()

let e_f
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Typenum.Type_operators.t_IsLess v_T
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt
                                    (Typenum.Uint.t_UInt
                                        (Typenum.Uint.t_UInt
                                            (Typenum.Uint.t_UInt
                                                (Typenum.Uint.t_UInt
                                                    (Typenum.Uint.t_UInt
                                                        (Typenum.Uint.t_UInt
                                                            (Typenum.Uint.t_UInt
                                                                (Typenum.Uint.t_UInt
                                                                    (Typenum.Uint.t_UInt
                                                                        (Typenum.Uint.t_UInt
                                                                            (Typenum.Uint.t_UInt
                                                                                (Typenum.Uint.t_UInt
                                                                                    (Typenum.Uint.t_UInt
                                                                                        (Typenum.Uint.t_UInt
                                                                                            Typenum.Uint.t_UTerm
                                                                                            Typenum.Bit.t_B1
                                                                                        )
                                                                                        Typenum.Bit.t_B1
                                                                                    )
                                                                                    Typenum.Bit.t_B1
                                                                                ) Typenum.Bit.t_B1)
                                                                            Typenum.Bit.t_B1)
                                                                        Typenum.Bit.t_B1)
                                                                    Typenum.Bit.t_B1)
                                                                Typenum.Bit.t_B1) Typenum.Bit.t_B1)
                                                        Typenum.Bit.t_B1) Typenum.Bit.t_B1)
                                                Typenum.Bit.t_B1) Typenum.Bit.t_B1) Typenum.Bit.t_B1
                                    ) Typenum.Bit.t_B1) Typenum.Bit.t_B1) Typenum.Bit.t_B1)
                        Typenum.Bit.t_B1) Typenum.Bit.t_B1) Typenum.Bit.t_B1))
      (_: Prims.unit)
    : Prims.unit = ()
