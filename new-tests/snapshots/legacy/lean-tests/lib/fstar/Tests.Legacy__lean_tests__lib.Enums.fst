module Tests.Legacy__lean_tests__lib.Enums
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_E =
  | E_V1 : t_E
  | E_V2 : t_E
  | E_V3 : usize -> t_E
  | E_V4 : usize -> usize -> usize -> t_E
  | E_V5 {
    f_f1:usize;
    f_f2:usize
  }: t_E
  | E_V6 {
    f_f1:usize;
    f_f2:usize
  }: t_E

type t_MyList (v_T: Type0) =
  | MyList_Nil : t_MyList v_T
  | MyList_Cons {
    f_hd:v_T;
    f_tl:Alloc.Boxed.t_Box (t_MyList v_T) Alloc.Alloc.t_Global
  }: t_MyList v_T

/// @fail(extraction): ssprove(HAX0001)
let enums (_: Prims.unit) : Prims.unit =
  let e_v1:t_E = E_V1 <: t_E in
  let e_v2:t_E = E_V2 <: t_E in
  let e_v3:t_E = E_V3 (mk_usize 23) <: t_E in
  let e_v4:t_E = E_V4 (mk_usize 23) (mk_usize 12) (mk_usize 1) <: t_E in
  let e_v5:t_E = E_V5 ({ f_f1 = mk_usize 23; f_f2 = mk_usize 43 }) <: t_E in
  let e_v6:t_E = E_V6 ({ f_f1 = mk_usize 12; f_f2 = mk_usize 13 }) <: t_E in
  let (nil: t_MyList usize):t_MyList usize = MyList_Nil <: t_MyList usize in
  let cons_1_:t_MyList usize = MyList_Cons ({ f_hd = mk_usize 1; f_tl = nil }) <: t_MyList usize in
  let cons_2_1_:t_MyList usize =
    MyList_Cons ({ f_hd = mk_usize 2; f_tl = cons_1_ }) <: t_MyList usize
  in
  match e_v1 <: t_E with
  | E_V1  -> () <: Prims.unit
  | E_V2  -> () <: Prims.unit
  | E_V3 _ -> () <: Prims.unit
  | E_V4 x1 x2 x3 ->
    let y1:usize = x1 +! x2 in
    let y2:usize = y1 -! x2 in
    let y3:usize = y2 +! x3 in
    () <: Prims.unit
  | E_V5 { f_f1 = f1 ; f_f2 = f2 } -> () <: Prims.unit
  | E_V6 { f_f1 = f1 ; f_f2 = other_name_for_f2 } -> () <: Prims.unit
