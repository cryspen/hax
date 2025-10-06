module Tests.Legacy__cyclic_modules.Bundle_typ_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_T1 = | T1_T1 : t_T1

type t_T = | T_T : t_T1 -> t_T

let t_T1_cast_to_repr (x: t_T1) : isize = match x <: t_T1 with | T1_T1  -> mk_isize 0

type t_T2 = | T2_T2 : t_T -> t_T2

type t_T2Rec = | T2Rec_T2 : t_TRec -> t_T2Rec

and t_T1Rec = | T1Rec_T1 : Alloc.Boxed.t_Box t_T2Rec Alloc.Alloc.t_Global -> t_T1Rec

and t_TRec =
  | TRec_T : t_T1Rec -> t_TRec
  | TRec_Empty : t_TRec
