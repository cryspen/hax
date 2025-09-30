
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

structure Tests.Legacy__lean_tests__src__structs.Miscellaneous.S where
  f : i32

def Tests.Legacy__lean_tests__src__structs.Miscellaneous.test_tuples
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 i32 i32)
  := do
  let lit : i32 ← (pure (1 : i32));
  let constr : Tests.Legacy__lean_tests__src__structs.Miscellaneous.S ← (pure
    (Tests.Legacy__lean_tests__src__structs.Miscellaneous.S.mk
      (f := (42 : i32))));
  let proj : i32 ← (pure
    (Tests.Legacy__lean_tests__src__structs.Miscellaneous.S.f constr));
  let ite : (Rust_primitives.Hax.Tuple2 i32 i32) ← (pure
    (← if true then do
      (Rust_primitives.Hax.Tuple2.mk (1 : i32) (2 : i32))
    else do
      let z : i32 ← (pure (← (1 : i32) +? (2 : i32)));
      (Rust_primitives.Hax.Tuple2.mk z z)));
  (Rust_primitives.Hax.Tuple2.mk (1 : i32) (2 : i32))

structure Tests.Legacy__lean_tests__src__structs.T0 where


structure Tests.Legacy__lean_tests__src__structs.T1 (A : Type) where
  _0 : A

structure Tests.Legacy__lean_tests__src__structs.T2 (A : Type) (B : Type) where
  _0 : A
  _1 : B

structure Tests.Legacy__lean_tests__src__structs.T3
  (A : Type) (B : Type) (C : Type) where
  _0 : A
  _1 : B
  _2 : C

structure Tests.Legacy__lean_tests__src__structs.T3p
  (A : Type) (B : Type) (C : Type) where
  _0 : A
  _1 : (Tests.Legacy__lean_tests__src__structs.T2 B C)

def Tests.Legacy__lean_tests__src__structs.tuple_structs
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let t0 : Tests.Legacy__lean_tests__src__structs.T0 ← (pure
    Tests.Legacy__lean_tests__src__structs.T0.mk);
  let t1 : (Tests.Legacy__lean_tests__src__structs.T1 i32) ← (pure
    (Tests.Legacy__lean_tests__src__structs.T1.mk (1 : i32)));
  let t2 : (Tests.Legacy__lean_tests__src__structs.T2 i32 i32) ← (pure
    (Tests.Legacy__lean_tests__src__structs.T2.mk (1 : i32) (2 : i32)));
  let
    t3 : (Tests.Legacy__lean_tests__src__structs.T3
      Tests.Legacy__lean_tests__src__structs.T0
      (Tests.Legacy__lean_tests__src__structs.T1 i32)
      (Tests.Legacy__lean_tests__src__structs.T2 i32 i32)) ← (pure
    (Tests.Legacy__lean_tests__src__structs.T3.mk
      Tests.Legacy__lean_tests__src__structs.T0.mk
      (Tests.Legacy__lean_tests__src__structs.T1.mk (1 : i32))
      (Tests.Legacy__lean_tests__src__structs.T2.mk (1 : i32) (2 : i32))));
  let
    t3p : (Tests.Legacy__lean_tests__src__structs.T3p
      Tests.Legacy__lean_tests__src__structs.T0
      (Tests.Legacy__lean_tests__src__structs.T1 i32)
      (Tests.Legacy__lean_tests__src__structs.T2 i32 i32)) ← (pure
    (Tests.Legacy__lean_tests__src__structs.T3p.mk
      Tests.Legacy__lean_tests__src__structs.T0.mk
      (Tests.Legacy__lean_tests__src__structs.T2.mk
        (Tests.Legacy__lean_tests__src__structs.T1.mk (1 : i32))
        (Tests.Legacy__lean_tests__src__structs.T2.mk (1 : i32) (2 : i32)))));
  let ⟨⟩ ← (pure t0);
  let ⟨u1⟩ ← (pure t1);
  let ⟨u2, u3⟩ ← (pure t2);
  let ⟨⟨⟩, ⟨_⟩, ⟨_, _⟩⟩ ← (pure t3);
  let ⟨⟨⟩, ⟨⟨_⟩, ⟨_, _⟩⟩⟩ ← (pure t3p);
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T1._0 t1));
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T2._0 t2));
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T2._1 t2));
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T3._0 t3));
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T3._1 t3));
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T3._2 t3));
  let _ ← (pure
    (Tests.Legacy__lean_tests__src__structs.T2._1
        (Tests.Legacy__lean_tests__src__structs.T3._2 t3)));
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T3p._0 t3p));
  let _ ← (pure (Tests.Legacy__lean_tests__src__structs.T3p._1 t3p));
  let _ ← (pure
    (Tests.Legacy__lean_tests__src__structs.T2._0
        (Tests.Legacy__lean_tests__src__structs.T2._1
            (Tests.Legacy__lean_tests__src__structs.T3p._1 t3p))));
  let _ ← (pure
    (Tests.Legacy__lean_tests__src__structs.T2._0
        (Tests.Legacy__lean_tests__src__structs.T3p._1 t3p)));
  let _ ← (pure
    (Tests.Legacy__lean_tests__src__structs.T2._1
        (Tests.Legacy__lean_tests__src__structs.T3p._1 t3p)));
  let _ ← (pure (match t0 with | ⟨⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (match t1 with | ⟨u1⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (match t2 with | ⟨u2, u3⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match t3 with | ⟨⟨⟩, ⟨u1⟩, ⟨u2, u3⟩⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match t3p with
      | ⟨⟨⟩, ⟨⟨u1⟩, ⟨u2, u3⟩⟩⟩ => do Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__lean_tests__src__structs.S1 where
  f1 : usize
  f2 : usize

structure Tests.Legacy__lean_tests__src__structs.S2 where
  f1 : Tests.Legacy__lean_tests__src__structs.S1
  f2 : usize

structure Tests.Legacy__lean_tests__src__structs.S3 where
  _end : usize
  _def : usize
  _theorem : usize
  _structure : usize
  _inductive : usize

def Tests.Legacy__lean_tests__src__structs.normal_structs
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let s1 : Tests.Legacy__lean_tests__src__structs.S1 ← (pure
    (Tests.Legacy__lean_tests__src__structs.S1.mk
      (f1 := (0 : usize)) (f2 := (1 : usize))));
  let s2 : Tests.Legacy__lean_tests__src__structs.S2 ← (pure
    (Tests.Legacy__lean_tests__src__structs.S2.mk
      (f1 := (Tests.Legacy__lean_tests__src__structs.S1.mk
        (f1 := (2 : usize)) (f2 := (3 : usize))))
      (f2 := (4 : usize))));
  let s3 : Tests.Legacy__lean_tests__src__structs.S3 ← (pure
    (Tests.Legacy__lean_tests__src__structs.S3.mk
      (_end := (0 : usize))
      (_def := (0 : usize))
      (_theorem := (0 : usize))
      (_structure := (0 : usize))
      (_inductive := (0 : usize))));
  let {f1 := f1, f2 := f2} ← (pure s1);
  let {f1 := f1, f2 := other_name_for_f2} ← (pure s1);
  let {f1 := {f1 := f1, f2 := f2}, f2 := other_name_for_f2} ← (pure s2);
  let
    {_end := _end,
     _def := _def,
     _theorem := _theorem,
     _structure := _structure,
     _inductive := _inductive} ← (pure s3);
  let _ ← (pure
    (Rust_primitives.Hax.Tuple2.mk
      (Tests.Legacy__lean_tests__src__structs.S1.f1 s1)
      (Tests.Legacy__lean_tests__src__structs.S1.f2 s1)));
  let _ ← (pure
    (Rust_primitives.Hax.Tuple8.mk
      (Tests.Legacy__lean_tests__src__structs.S1.f1 s1)
      (Tests.Legacy__lean_tests__src__structs.S1.f2 s1)
      (Tests.Legacy__lean_tests__src__structs.S1.f1
          (Tests.Legacy__lean_tests__src__structs.S2.f1 s2))
      (Tests.Legacy__lean_tests__src__structs.S1.f2
          (Tests.Legacy__lean_tests__src__structs.S2.f1 s2))
      (Tests.Legacy__lean_tests__src__structs.S2.f2 s2)
      (Tests.Legacy__lean_tests__src__structs.S3._end s3)
      (Tests.Legacy__lean_tests__src__structs.S3._def s3)
      (Tests.Legacy__lean_tests__src__structs.S3._theorem s3)));
  let _ ← (pure
    (match s1 with | {f1 := f1, f2 := f2} => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match s2 with
      | {f1 := {f1 := f1, f2 := other_name_for_f2}, f2 := f2}
        => do Rust_primitives.Hax.Tuple0.mk));
  (match s3 with
    | {_end := _end,
       _def := _def,
       _theorem := _theorem,
       _structure := _structure,
       _inductive := _inductive}
      => do Rust_primitives.Hax.Tuple0.mk)