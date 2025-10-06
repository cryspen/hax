
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

class Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T1
  (Self : Type)
  where
  f : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T2
  (Self : Type)
  where
  f : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T3
  (Self : Type)
  where
  f : Self -> Result usize

instance Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.Impl :
  Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T1 u32
  where
  f (self : u32) := do (0 : usize)

instance Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.Impl_1 :
  Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T2 u32
  where
  f (self : u32) := do (1 : usize)

instance Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.Impl_2 :
  Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T3 u32
  where
  f (self : u32) := do (2 : usize)

def Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.test
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  let x ← (pure (9 : u32));
  (← (← (← Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T1.f x)
      +? (← Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T2.f x))
    +? (← Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods.T3.f x))

class Tests.Legacy__lean_tests__lib.Traits.Inheritance.T1 (Self : Type) where
  f1 : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Inheritance.T2 (Self : Type) where
  f2 : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Inheritance.T3 (Self : Type) where
  [_constr_4681669453038871009 :
  (Tests.Legacy__lean_tests__lib.Traits.Inheritance.T2 Self)]
  [_constr_4145440524185414164 :
  (Tests.Legacy__lean_tests__lib.Traits.Inheritance.T1 Self)]
  f3 : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Inheritance.Tp1 (Self : Type) where
  f1 : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Inheritance.Tp2 (Self : Type) where
  [_constr_7003374932835866648 :
  (Tests.Legacy__lean_tests__lib.Traits.Inheritance.Tp1 Self)]
  [_constr_15052774938804589053 :
  (Tests.Legacy__lean_tests__lib.Traits.Inheritance.T3 Self)]
  fp2 : Self -> Result usize

structure Tests.Legacy__lean_tests__lib.Traits.Inheritance.S where


instance Tests.Legacy__lean_tests__lib.Traits.Inheritance.Impl :
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.T1
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.S
  where
  f1 (self : Tests.Legacy__lean_tests__lib.Traits.Inheritance.S) := do
    (1 : usize)

instance Tests.Legacy__lean_tests__lib.Traits.Inheritance.Impl_1 :
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.T2
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.S
  where
  f2 (self : Tests.Legacy__lean_tests__lib.Traits.Inheritance.S) := do
    (2 : usize)

instance Tests.Legacy__lean_tests__lib.Traits.Inheritance.Impl_2 :
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.T3
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.S
  where
  f3 (self : Tests.Legacy__lean_tests__lib.Traits.Inheritance.S) := do
    (3 : usize)

instance Tests.Legacy__lean_tests__lib.Traits.Inheritance.Impl_3 :
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.Tp1
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.S
  where
  f1 (self : Tests.Legacy__lean_tests__lib.Traits.Inheritance.S) := do
    (10 : usize)

instance Tests.Legacy__lean_tests__lib.Traits.Inheritance.Impl_4 :
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.Tp2
  Tests.Legacy__lean_tests__lib.Traits.Inheritance.S
  where
  fp2 (self : Tests.Legacy__lean_tests__lib.Traits.Inheritance.S) := do
    (← (← (← (← Tests.Legacy__lean_tests__lib.Traits.Inheritance.Tp1.f1 self)
          +? (← Tests.Legacy__lean_tests__lib.Traits.Inheritance.T1.f1 self))
        +? (← Tests.Legacy__lean_tests__lib.Traits.Inheritance.T2.f2 self))
      +? (← Tests.Legacy__lean_tests__lib.Traits.Inheritance.T3.f3 self))

def Tests.Legacy__lean_tests__lib.Traits.Inheritance.test
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  let s : Tests.Legacy__lean_tests__lib.Traits.Inheritance.S ← (pure
    Tests.Legacy__lean_tests__lib.Traits.Inheritance.S.mk);
  (← (← Tests.Legacy__lean_tests__lib.Traits.Inheritance.T3.f3 s)
    +? (1 : usize))

class Tests.Legacy__lean_tests__lib.Traits.Bounds.T1 (Self : Type) where
  f1 : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Bounds.T2 (Self : Type) where
  f2 : Self -> Result usize

class Tests.Legacy__lean_tests__lib.Traits.Bounds.Test
  (Self : Type) (T : Type)
  where
  [_constr_1529261179564284687 :
  (Tests.Legacy__lean_tests__lib.Traits.Bounds.T2 Self)]
  [_constr_5255745353837564140 :
  (Tests.Legacy__lean_tests__lib.Traits.Bounds.T1 T)]
  f_test : Self -> T -> Result usize

structure Tests.Legacy__lean_tests__lib.Traits.Bounds.S1 where


instance Tests.Legacy__lean_tests__lib.Traits.Bounds.Impl :
  Tests.Legacy__lean_tests__lib.Traits.Bounds.T1
  Tests.Legacy__lean_tests__lib.Traits.Bounds.S1
  where
  f1 (self : Tests.Legacy__lean_tests__lib.Traits.Bounds.S1) := do (0 : usize)

structure Tests.Legacy__lean_tests__lib.Traits.Bounds.S2 where


instance Tests.Legacy__lean_tests__lib.Traits.Bounds.Impl_1 :
  Tests.Legacy__lean_tests__lib.Traits.Bounds.T2
  Tests.Legacy__lean_tests__lib.Traits.Bounds.S2
  where
  f2 (self : Tests.Legacy__lean_tests__lib.Traits.Bounds.S2) := do (1 : usize)

instance Tests.Legacy__lean_tests__lib.Traits.Bounds.Impl_2 :
  Tests.Legacy__lean_tests__lib.Traits.Bounds.Test
  Tests.Legacy__lean_tests__lib.Traits.Bounds.S2
  Tests.Legacy__lean_tests__lib.Traits.Bounds.S1
  where
  f_test (self : Tests.Legacy__lean_tests__lib.Traits.Bounds.S2)
    (x : Tests.Legacy__lean_tests__lib.Traits.Bounds.S1)
    := do
    (← (← (← Tests.Legacy__lean_tests__lib.Traits.Bounds.T1.f1 x)
        +? (← Tests.Legacy__lean_tests__lib.Traits.Bounds.T2.f2 self))
      +? (1 : usize))

def Tests.Legacy__lean_tests__lib.Traits.Bounds.test
  (x1 : Tests.Legacy__lean_tests__lib.Traits.Bounds.S1)
  (x2 : Tests.Legacy__lean_tests__lib.Traits.Bounds.S2)
  : Result usize
  := do
  (← (← Tests.Legacy__lean_tests__lib.Traits.Bounds.Test.f_test x2 x1)
    +? (← Tests.Legacy__lean_tests__lib.Traits.Bounds.T1.f1 x1))

class Tests.Legacy__lean_tests__lib.Traits.Basic.T1 (Self : Type) where
  f1 : Self -> Result usize
  f2 : Self -> Self -> Result usize

structure Tests.Legacy__lean_tests__lib.Traits.Basic.S where


instance Tests.Legacy__lean_tests__lib.Traits.Basic.Impl :
  Tests.Legacy__lean_tests__lib.Traits.Basic.T1
  Tests.Legacy__lean_tests__lib.Traits.Basic.S
  where
  f1 (self : Tests.Legacy__lean_tests__lib.Traits.Basic.S) := do (42 : usize)
  f2 (self : Tests.Legacy__lean_tests__lib.Traits.Basic.S)
    (other : Tests.Legacy__lean_tests__lib.Traits.Basic.S)
    := do
    (43 : usize)

def Tests.Legacy__lean_tests__lib.Traits.Basic.f
  (T : Type) [(Tests.Legacy__lean_tests__lib.Traits.Basic.T1 T)] (x : T)
  : Result usize
  := do
  (← (← Tests.Legacy__lean_tests__lib.Traits.Basic.T1.f1 x)
    +? (← Tests.Legacy__lean_tests__lib.Traits.Basic.T1.f2 x x))

class Tests.Legacy__lean_tests__lib.Traits.Associated_types.Foo
  (Self : Type) (T : Type)
  where


class Tests.Legacy__lean_tests__lib.Traits.Associated_types.Bar
  (Self : Type)
  where


structure Tests.Legacy__lean_tests__lib.Traits.Associated_types.S where


instance Tests.Legacy__lean_tests__lib.Traits.Associated_types.Impl_2 :
  Tests.Legacy__lean_tests__lib.Traits.Associated_types.Bar i16
  where


instance Tests.Legacy__lean_tests__lib.Traits.Associated_types.Impl_3
  (A : Type) :
  Tests.Legacy__lean_tests__lib.Traits.Associated_types.Foo
  (Rust_primitives.Hax.Tuple2 u32 A)
  i16
  where


class Tests.Legacy__lean_tests__lib.Traits.Associated_types.T1
  (Self : Type)
  where
  T : Type
  f : Self -> T -> Result T

class Tests.Legacy__lean_tests__lib.Traits.Associated_types.T3
  (Self : Type)
  where
  T : Type
  [_constr_4101979666136489415 :
    (Tests.Legacy__lean_tests__lib.Traits.Associated_types.Bar T)]
  Tp : Type
  [_constr_13521341099752925627 :
    (Tests.Legacy__lean_tests__lib.Traits.Associated_types.Foo Tp T)]
  f (A : Type) [(Tests.Legacy__lean_tests__lib.Traits.Associated_types.Bar A)] :
    Self -> T -> Tp -> Result usize

instance Tests.Legacy__lean_tests__lib.Traits.Associated_types.Impl :
  Tests.Legacy__lean_tests__lib.Traits.Associated_types.T1
  Tests.Legacy__lean_tests__lib.Traits.Associated_types.S
  where
  T := i32
  f (self : Tests.Legacy__lean_tests__lib.Traits.Associated_types.S)
    (x : i32)
    := do
    (2121 : i32)

class Tests.Legacy__lean_tests__lib.Traits.Associated_types.T2
  (Self : Type)
  where
  T : Type
  [_constr_83052203690501683 :
    (Tests.Legacy__lean_tests__lib.Traits.Associated_types.T1 T)]
  f : Self -> T -> Result usize

instance Tests.Legacy__lean_tests__lib.Traits.Associated_types.Impl_1 :
  Tests.Legacy__lean_tests__lib.Traits.Associated_types.T2
  Tests.Legacy__lean_tests__lib.Traits.Associated_types.S
  where
  T := Tests.Legacy__lean_tests__lib.Traits.Associated_types.S
  f (self : Tests.Legacy__lean_tests__lib.Traits.Associated_types.S)
    (x : Tests.Legacy__lean_tests__lib.Traits.Associated_types.S)
    := do
    (21 : usize)

structure Tests.Legacy__lean_tests__lib.Structs.Miscellaneous.S where
  f : i32

def Tests.Legacy__lean_tests__lib.Structs.Miscellaneous.test_tuples
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 i32 i32)
  := do
  let lit : i32 ← (pure (1 : i32));
  let constr : Tests.Legacy__lean_tests__lib.Structs.Miscellaneous.S ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.Miscellaneous.S.mk
      (f := (42 : i32))));
  let proj : i32 ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.Miscellaneous.S.f constr));
  let ite : (Rust_primitives.Hax.Tuple2 i32 i32) ← (pure
    (← if true then do
      (Rust_primitives.Hax.Tuple2.mk (1 : i32) (2 : i32))
    else do
      let z : i32 ← (pure (← (1 : i32) +? (2 : i32)));
      (Rust_primitives.Hax.Tuple2.mk z z)));
  (Rust_primitives.Hax.Tuple2.mk (1 : i32) (2 : i32))

structure Tests.Legacy__lean_tests__lib.Structs.T0 where


structure Tests.Legacy__lean_tests__lib.Structs.T1 (A : Type) where
  _0 : A

structure Tests.Legacy__lean_tests__lib.Structs.T2 (A : Type) (B : Type) where
  _0 : A
  _1 : B

structure Tests.Legacy__lean_tests__lib.Structs.T3
  (A : Type) (B : Type) (C : Type) where
  _0 : A
  _1 : B
  _2 : C

structure Tests.Legacy__lean_tests__lib.Structs.T3p
  (A : Type) (B : Type) (C : Type) where
  _0 : A
  _1 : (Tests.Legacy__lean_tests__lib.Structs.T2 B C)

def Tests.Legacy__lean_tests__lib.Structs.tuple_structs
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let t0 : Tests.Legacy__lean_tests__lib.Structs.T0 ← (pure
    Tests.Legacy__lean_tests__lib.Structs.T0.mk);
  let t1 : (Tests.Legacy__lean_tests__lib.Structs.T1 i32) ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T1.mk (1 : i32)));
  let t2 : (Tests.Legacy__lean_tests__lib.Structs.T2 i32 i32) ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T2.mk (1 : i32) (2 : i32)));
  let
    t3 : (Tests.Legacy__lean_tests__lib.Structs.T3
      Tests.Legacy__lean_tests__lib.Structs.T0
      (Tests.Legacy__lean_tests__lib.Structs.T1 i32)
      (Tests.Legacy__lean_tests__lib.Structs.T2 i32 i32)) ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T3.mk
      Tests.Legacy__lean_tests__lib.Structs.T0.mk
      (Tests.Legacy__lean_tests__lib.Structs.T1.mk (1 : i32))
      (Tests.Legacy__lean_tests__lib.Structs.T2.mk (1 : i32) (2 : i32))));
  let
    t3p : (Tests.Legacy__lean_tests__lib.Structs.T3p
      Tests.Legacy__lean_tests__lib.Structs.T0
      (Tests.Legacy__lean_tests__lib.Structs.T1 i32)
      (Tests.Legacy__lean_tests__lib.Structs.T2 i32 i32)) ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T3p.mk
      Tests.Legacy__lean_tests__lib.Structs.T0.mk
      (Tests.Legacy__lean_tests__lib.Structs.T2.mk
        (Tests.Legacy__lean_tests__lib.Structs.T1.mk (1 : i32))
        (Tests.Legacy__lean_tests__lib.Structs.T2.mk (1 : i32) (2 : i32)))));
  let ⟨⟩ ← (pure t0);
  let ⟨u1⟩ ← (pure t1);
  let ⟨u2, u3⟩ ← (pure t2);
  let ⟨⟨⟩, ⟨_⟩, ⟨_, _⟩⟩ ← (pure t3);
  let ⟨⟨⟩, ⟨⟨_⟩, ⟨_, _⟩⟩⟩ ← (pure t3p);
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T1._0 t1));
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T2._0 t2));
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T2._1 t2));
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T3._0 t3));
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T3._1 t3));
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T3._2 t3));
  let _ ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T2._1
        (Tests.Legacy__lean_tests__lib.Structs.T3._2 t3)));
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T3p._0 t3p));
  let _ ← (pure (Tests.Legacy__lean_tests__lib.Structs.T3p._1 t3p));
  let _ ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T2._0
        (Tests.Legacy__lean_tests__lib.Structs.T2._1
            (Tests.Legacy__lean_tests__lib.Structs.T3p._1 t3p))));
  let _ ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T2._0
        (Tests.Legacy__lean_tests__lib.Structs.T3p._1 t3p)));
  let _ ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.T2._1
        (Tests.Legacy__lean_tests__lib.Structs.T3p._1 t3p)));
  let _ ← (pure (match t0 with | ⟨⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (match t1 with | ⟨u1⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (match t2 with | ⟨u2, u3⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match t3 with | ⟨⟨⟩, ⟨u1⟩, ⟨u2, u3⟩⟩ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match t3p with
      | ⟨⟨⟩, ⟨⟨u1⟩, ⟨u2, u3⟩⟩⟩ => do Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__lean_tests__lib.Structs.S1 where
  f1 : usize
  f2 : usize

structure Tests.Legacy__lean_tests__lib.Structs.S2 where
  f1 : Tests.Legacy__lean_tests__lib.Structs.S1
  f2 : usize

structure Tests.Legacy__lean_tests__lib.Structs.S3 where
  _end : usize
  _def : usize
  _theorem : usize
  _structure : usize
  _inductive : usize

--  @fail(extraction): ssprove(HAX0001)
def Tests.Legacy__lean_tests__lib.Structs.normal_structs
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let s1 : Tests.Legacy__lean_tests__lib.Structs.S1 ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.S1.mk
      (f1 := (0 : usize)) (f2 := (1 : usize))));
  let s2 : Tests.Legacy__lean_tests__lib.Structs.S2 ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.S2.mk
      (f1 := (Tests.Legacy__lean_tests__lib.Structs.S1.mk
        (f1 := (2 : usize)) (f2 := (3 : usize))))
      (f2 := (4 : usize))));
  let s3 : Tests.Legacy__lean_tests__lib.Structs.S3 ← (pure
    (Tests.Legacy__lean_tests__lib.Structs.S3.mk
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
      (Tests.Legacy__lean_tests__lib.Structs.S1.f1 s1)
      (Tests.Legacy__lean_tests__lib.Structs.S1.f2 s1)));
  let _ ← (pure
    (Rust_primitives.Hax.Tuple8.mk
      (Tests.Legacy__lean_tests__lib.Structs.S1.f1 s1)
      (Tests.Legacy__lean_tests__lib.Structs.S1.f2 s1)
      (Tests.Legacy__lean_tests__lib.Structs.S1.f1
          (Tests.Legacy__lean_tests__lib.Structs.S2.f1 s2))
      (Tests.Legacy__lean_tests__lib.Structs.S1.f2
          (Tests.Legacy__lean_tests__lib.Structs.S2.f1 s2))
      (Tests.Legacy__lean_tests__lib.Structs.S2.f2 s2)
      (Tests.Legacy__lean_tests__lib.Structs.S3._end s3)
      (Tests.Legacy__lean_tests__lib.Structs.S3._def s3)
      (Tests.Legacy__lean_tests__lib.Structs.S3._theorem s3)));
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

inductive Tests.Legacy__lean_tests__lib.Loops.Errors.Error : Type
| Foo : Tests.Legacy__lean_tests__lib.Loops.Errors.Error 
| Bar : u32 -> Tests.Legacy__lean_tests__lib.Loops.Errors.Error 


--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__lean_tests__lib.Loops.Errors.loop3
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result u32 Tests.Legacy__lean_tests__lib.Loops.Errors.Error)
  := do
  let x : u32 ← (pure (0 : u32));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (1 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x i => (do
            (← if (← Rust_primitives.Hax.Machine_int.eq i (5 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break
                  (Core.Result.Result.Err
                    Tests.Legacy__lean_tests__lib.Loops.Errors.Error.Foo)))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← x +? (5 : u32)))) :
            Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Result.Result
                  u32
                  Tests.Legacy__lean_tests__lib.Loops.Errors.Error)
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 u32))
              u32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue x)
      => do (Core.Result.Result.Ok x))

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__lean_tests__lib.Loops.Errors.loop4
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2 u32 u32)
    Tests.Legacy__lean_tests__lib.Loops.Errors.Error)
  := do
  let e : u32 ← (pure (0 : u32));
  let f : Rust_primitives.Hax.Tuple0 -> Result u32 ← (pure
    (fun ⟨⟩ => (do (42 : u32) : Result u32)));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (0 : u32)
        (← Core.Ops.Function.Fn.call
            f
            (Rust_primitives.Hax.Tuple1.mk Rust_primitives.Hax.Tuple0.mk))
        (fun e _ => (do true : Result Bool))
        e
        (fun e i => (do
            (← if (← Rust_primitives.Hax.Machine_int.gt i (10 : u32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break
                  (Core.Result.Result.Err
                    (Tests.Legacy__lean_tests__lib.Loops.Errors.Error.Bar e))))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← e +? i))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Result.Result
                  (Rust_primitives.Hax.Tuple2 u32 u32)
                  Tests.Legacy__lean_tests__lib.Loops.Errors.Error)
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 u32))
              u32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue e)
      => do (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk e e)))

inductive Tests.Legacy__lean_tests__lib.Enums.E : Type
| V1 : Tests.Legacy__lean_tests__lib.Enums.E 
| V2 : Tests.Legacy__lean_tests__lib.Enums.E 
| V3 : usize -> Tests.Legacy__lean_tests__lib.Enums.E 
| V4 : usize -> usize -> usize -> Tests.Legacy__lean_tests__lib.Enums.E 
| V5 (f1 : usize) (f2 : usize) : Tests.Legacy__lean_tests__lib.Enums.E 
| V6 (f1 : usize) (f2 : usize) : Tests.Legacy__lean_tests__lib.Enums.E 


inductive Tests.Legacy__lean_tests__lib.Enums.MyList (T : Type) : Type
| Nil : Tests.Legacy__lean_tests__lib.Enums.MyList (T : Type) 
| Cons (hd : T)
       (tl : (Alloc.Boxed.Box
         (Tests.Legacy__lean_tests__lib.Enums.MyList T)
         Alloc.Alloc.Global))
    : Tests.Legacy__lean_tests__lib.Enums.MyList (T : Type) 


--  @fail(extraction): ssprove(HAX0001)
def Tests.Legacy__lean_tests__lib.Enums.enums
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let e_v1 : Tests.Legacy__lean_tests__lib.Enums.E ← (pure
    Tests.Legacy__lean_tests__lib.Enums.E.V1);
  let e_v2 : Tests.Legacy__lean_tests__lib.Enums.E ← (pure
    Tests.Legacy__lean_tests__lib.Enums.E.V2);
  let e_v3 : Tests.Legacy__lean_tests__lib.Enums.E ← (pure
    (Tests.Legacy__lean_tests__lib.Enums.E.V3 (23 : usize)));
  let e_v4 : Tests.Legacy__lean_tests__lib.Enums.E ← (pure
    (Tests.Legacy__lean_tests__lib.Enums.E.V4
      (23 : usize) (12 : usize) (1 : usize)));
  let e_v5 : Tests.Legacy__lean_tests__lib.Enums.E ← (pure
    (Tests.Legacy__lean_tests__lib.Enums.E.V5
      (f1 := (23 : usize)) (f2 := (43 : usize))));
  let e_v6 : Tests.Legacy__lean_tests__lib.Enums.E ← (pure
    (Tests.Legacy__lean_tests__lib.Enums.E.V6
      (f1 := (12 : usize)) (f2 := (13 : usize))));
  let nil ← (pure Tests.Legacy__lean_tests__lib.Enums.MyList.Nil);
  let cons_1 : (Tests.Legacy__lean_tests__lib.Enums.MyList usize) ← (pure
    (Tests.Legacy__lean_tests__lib.Enums.MyList.Cons
      (hd := (1 : usize)) (tl := nil)));
  let cons_2_1 : (Tests.Legacy__lean_tests__lib.Enums.MyList usize) ← (pure
    (Tests.Legacy__lean_tests__lib.Enums.MyList.Cons
      (hd := (2 : usize)) (tl := cons_1)));
  (match e_v1 with
    | (Tests.Legacy__lean_tests__lib.Enums.E.V1 )
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__lib.Enums.E.V2 )
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__lib.Enums.E.V3 _)
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__lib.Enums.E.V4 x1 x2 x3)
      => do
        let y1 : usize ← (pure (← x1 +? x2));
        let y2 : usize ← (pure (← y1 -? x2));
        let y3 : usize ← (pure (← y2 +? x3));
        Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__lib.Enums.E.V5 (f1 := f1) (f2 := f2))
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__lib.Enums.E.V6
        (f1 := f1) (f2 := other_name_for_f2))
      => do Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__lean_tests__lib.FORTYTWO : usize := 42

def Tests.Legacy__lean_tests__lib.MINUS_FORTYTWO : isize := -42

def Tests.Legacy__lean_tests__lib.returns42
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  Tests.Legacy__lean_tests__lib.FORTYTWO

def Tests.Legacy__lean_tests__lib.add_two_numbers
  (x : usize)
  (y : usize)
  : Result usize
  := do
  (← x +? y)

def Tests.Legacy__lean_tests__lib.letBinding
  (x : usize)
  (y : usize)
  : Result usize
  := do
  let useless : Rust_primitives.Hax.Tuple0 ← (pure
    Rust_primitives.Hax.Tuple0.mk);
  let result1 : usize ← (pure (← x +? y));
  let result2 : usize ← (pure (← result1 +? (2 : usize)));
  (← result2 +? (1 : usize))

def Tests.Legacy__lean_tests__lib.closure
  (_ : Rust_primitives.Hax.Tuple0)
  : Result i32
  := do
  let x : i32 ← (pure (41 : i32));
  let f1 : i32 -> Result i32 ← (pure (fun y => (do (← y +? x) : Result i32)));
  let f2 : i32 -> i32 -> Result i32 ← (pure
    (fun y z => (do (← (← y +? x) +? z) : Result i32)));
  let res1 : i32 ← (pure
    (← Core.Ops.Function.Fn.call f1 (Rust_primitives.Hax.Tuple1.mk (1 : i32))));
  let res2 : i32 ← (pure
    (← Core.Ops.Function.Fn.call
        f2
        (Rust_primitives.Hax.Tuple2.mk (2 : i32) (3 : i32))));
  (← res1 +? res2)

@[spec]

def Tests.Legacy__lean_tests__lib.test_before_verbatime_single_line
  (x : u8)
  : Result u8
  := do
  (42 : u8)


def multiline : Unit := ()


def Tests.Legacy__lean_tests__lib.test_before_verbatim_multi_line
  (x : u8)
  : Result u8
  := do
  (32 : u8)

def Tests.Legacy__lean_tests__lib.binop_resugarings (x : u32) : Result u32 := do
  let add : u32 ← (pure (← x +? (1 : u32)));
  let sub : u32 ← (pure (← add -? (2 : u32)));
  let mul : u32 ← (pure (← sub *? (3 : u32)));
  let rem : u32 ← (pure (← mul %? (4 : u32)));
  let div : u32 ← (pure (← rem /? (5 : u32)));
  let rshift : u32 ← (pure (← div >>>? x));
  x

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__lean_tests__lib.Loops.loop1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  let x ← (pure (0 : u32));
  let x : u32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (1 : u32)
        (10 : u32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x i => (do (← x +? i) : Result u32))));
  x

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__lean_tests__lib.Loops.loop2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  let x ← (pure (0 : u32));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (1 : u32)
        (10 : u32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x i => (do
            (← if (← Rust_primitives.Hax.Machine_int.eq i (5 : u32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break x))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← x +? i))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                u32
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 u32))
              u32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue x) => do x)

def Tests.Legacy__lean_tests__lib.Ite.test1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result i32
  := do
  let x : i32 ← (pure (← if true then do (0 : i32) else do (1 : i32)));
  (← if false then do (2 : i32) else do (3 : i32))

def Tests.Legacy__lean_tests__lib.Ite.test2 (b : Bool) : Result i32 := do
  let x : i32 ← (pure
    (← (1 : i32) +? (← if true then do (0 : i32) else do (1 : i32))));
  let y : i32 ← (pure (0 : i32));
  let y : i32 ← (pure
    (← if true then do
      (← (← y +? x) +? (1 : i32))
    else do
      (← (← y -? x) -? (1 : i32))));
  (← if b then do
    let z : i32 ← (pure (← y +? y));
    (← (← z +? y) +? x)
  else do
    let z : i32 ← (pure (← y -? x));
    (← (← z +? y) +? x))

--  Single line doc comment
def Tests.Legacy__lean_tests__lib.Comments.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

/--
   Block doc-comment : Lorem ipsum dolor sit amet, consectetur adipiscing elit. Vestibulum rutrum
  orci ac tellus ullamcorper sollicitudin. Sed fringilla mi id arcu suscipit rhoncus. Pellentesque et
  metus a ante feugiat lobortis. Nam a mauris eget nisl congue egestas. Duis et gravida
  nulla. Curabitur mattis leo vel molestie posuere. Etiam malesuada et augue eget
  varius. Pellentesque quis tincidunt erat. Vestibulum id consectetur turpis. Cras elementum magna id
  urna volutpat fermentum. In vel erat quis nunc rhoncus porta. Aliquam sed pellentesque
  tellus. Quisque odio diam, mollis ut venenatis non, scelerisque at nulla. Nunc urna ante, tristique
  quis nisi quis, congue maximus nisl. Curabitur non efficitur odio. 
  -/
def Tests.Legacy__lean_tests__lib.Comments.heavily_documented
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  (4 : u32)