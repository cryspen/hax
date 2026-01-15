module Tests.Legacy__lean_tests__lib.Structs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_T0 = | T0 : t_T0

type t_T1 (v_A: Type0) = | T1 : v_A -> t_T1 v_A

type t_T2 (v_A: Type0) (v_B: Type0) = | T2 : v_A -> v_B -> t_T2 v_A v_B

type t_T3 (v_A: Type0) (v_B: Type0) (v_C: Type0) = | T3 : v_A -> v_B -> v_C -> t_T3 v_A v_B v_C

type t_T3p (v_A: Type0) (v_B: Type0) (v_C: Type0) = | T3p : v_A -> t_T2 v_B v_C -> t_T3p v_A v_B v_C

let tuple_structs (_: Prims.unit) : Prims.unit =
  let t0:t_T0 = T0 <: t_T0 in
  let t1:t_T1 i32 = T1 (mk_i32 1) <: t_T1 i32 in
  let t2:t_T2 i32 i32 = T2 (mk_i32 1) (mk_i32 2) <: t_T2 i32 i32 in
  let t3:t_T3 t_T0 (t_T1 i32) (t_T2 i32 i32) =
    T3 (T0 <: t_T0) (T1 (mk_i32 1) <: t_T1 i32) (T2 (mk_i32 1) (mk_i32 2) <: t_T2 i32 i32)
    <:
    t_T3 t_T0 (t_T1 i32) (t_T2 i32 i32)
  in
  let t3p:t_T3p t_T0 (t_T1 i32) (t_T2 i32 i32) =
    T3p (T0 <: t_T0)
      (T2 (T1 (mk_i32 1) <: t_T1 i32) (T2 (mk_i32 1) (mk_i32 2) <: t_T2 i32 i32)
        <:
        t_T2 (t_T1 i32) (t_T2 i32 i32))
    <:
    t_T3p t_T0 (t_T1 i32) (t_T2 i32 i32)
  in
  let T0 :t_T0 = t0 in
  let T1 u1:t_T1 i32 = t1 in
  let T2 u2 u3:t_T2 i32 i32 = t2 in
  let T3 (T0 ) (T1 _) (T2 _ _):t_T3 t_T0 (t_T1 i32) (t_T2 i32 i32) = t3 in
  let T3p (T0 ) (T2 (T1 _) (T2 _ _)):t_T3p t_T0 (t_T1 i32) (t_T2 i32 i32) = t3p in
  let _:i32 = t1._0 in
  let _:i32 = t2._0 in
  let _:i32 = t2._1 in
  let _:t_T0 = t3._0 in
  let _:t_T1 i32 = t3._1 in
  let _:t_T2 i32 i32 = t3._2 in
  let _:i32 = t3._2._1 in
  let _:t_T0 = t3p._0 in
  let _:t_T2 (t_T1 i32) (t_T2 i32 i32) = t3p._1 in
  let _:i32 = t3p._1._1._0 in
  let _:t_T1 i32 = t3p._1._0 in
  let _:t_T2 i32 i32 = t3p._1._1 in
  let _:Prims.unit = match t0 <: t_T0 with | T0  -> () in
  let _:Prims.unit = match t1 <: t_T1 i32 with | T1 u1 -> () in
  let _:Prims.unit = match t2 <: t_T2 i32 i32 with | T2 u2 u3 -> () in
  let _:Prims.unit =
    match t3 <: t_T3 t_T0 (t_T1 i32) (t_T2 i32 i32) with | T3 (T0 ) (T1 u1) (T2 u2 u3) -> ()
  in
  let _:Prims.unit =
    match t3p <: t_T3p t_T0 (t_T1 i32) (t_T2 i32 i32) with | T3p (T0 ) (T2 (T1 u1) (T2 u2 u3)) -> ()
  in
  ()

type t_S1 = {
  f_f1:usize;
  f_f2:usize
}

type t_S2 = {
  f_f1:t_S1;
  f_f2:usize
}

type t_S3 = {
  f_end:usize;
  f_def:usize;
  f_theorem:usize;
  f_structure:usize;
  f_inductive:usize
}

/// @fail(extraction): ssprove(HAX0001)
let normal_structs (_: Prims.unit) : Prims.unit =
  let s1:t_S1 = { f_f1 = mk_usize 0; f_f2 = mk_usize 1 } <: t_S1 in
  let s2:t_S2 =
    { f_f1 = { f_f1 = mk_usize 2; f_f2 = mk_usize 3 } <: t_S1; f_f2 = mk_usize 4 } <: t_S2
  in
  let s3:t_S3 =
    {
      f_end = mk_usize 0;
      f_def = mk_usize 0;
      f_theorem = mk_usize 0;
      f_structure = mk_usize 0;
      f_inductive = mk_usize 0
    }
    <:
    t_S3
  in
  let { f_f1 = f1 ; f_f2 = f2 }:t_S1 = s1 in
  let { f_f1 = f1 ; f_f2 = other_name_for_f2 }:t_S1 = s1 in
  let { f_f1 = { f_f1 = f1 ; f_f2 = f2 } ; f_f2 = other_name_for_f2 }:t_S2 = s2 in
  let
  { f_end = v_end ;
    f_def = def ;
    f_theorem = theorem ;
    f_structure = structure ;
    f_inductive = inductive }:t_S3 =
    s3
  in
  let _:(usize & usize) = s1.f_f1, s1.f_f2 <: (usize & usize) in
  let _:(usize & usize & usize & usize & usize & usize & usize & usize) =
    s1.f_f1, s1.f_f2, s2.f_f1.f_f1, s2.f_f1.f_f2, s2.f_f2, s3.f_end, s3.f_def, s3.f_theorem
    <:
    (usize & usize & usize & usize & usize & usize & usize & usize)
  in
  let _:Prims.unit = match s1 <: t_S1 with | { f_f1 = f1 ; f_f2 = f2 } -> () in
  let _:Prims.unit =
    match s2 <: t_S2 with | { f_f1 = { f_f1 = f1 ; f_f2 = other_name_for_f2 } ; f_f2 = f2 } -> ()
  in
  match s3 <: t_S3 with
  | { f_end = v_end ;
    f_def = def ;
    f_theorem = theorem ;
    f_structure = structure ;
    f_inductive = inductive } ->
    ()
