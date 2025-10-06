
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

def Tests.Legacy__side_effects.Nested_return.other_fun
  (rng : i8)
  : Result
  (Rust_primitives.Hax.Tuple2
    i8
    (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0))
  := do
  let
    hax_temp_output : (Core.Result.Result
      Rust_primitives.Hax.Tuple0
      Rust_primitives.Hax.Tuple0) ← (pure
    (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk));
  (Rust_primitives.Hax.Tuple2.mk rng hax_temp_output)

def Tests.Legacy__side_effects.Nested_return.fun
  (rng : i8)
  : Result
  (Rust_primitives.Hax.Tuple2
    i8
    (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0))
  := do
  let ⟨tmp0, out⟩ ← (pure
    (← Tests.Legacy__side_effects.Nested_return.other_fun rng));
  let rng : i8 ← (pure tmp0);
  (match out with
    | (Core.Result.Result.Ok hoist41)
      => do (Rust_primitives.Hax.Tuple2.mk rng (Core.Result.Result.Ok hoist41))
    | (Core.Result.Result.Err err)
      => do (Rust_primitives.Hax.Tuple2.mk rng (Core.Result.Result.Err err)))

structure Tests.Legacy__side_effects.Issue_1299.Foo where
  y : u8

structure Tests.Legacy__side_effects.Issue_1299.S where
  g : Tests.Legacy__side_effects.Issue_1299.Foo

structure Tests.Legacy__side_effects.Issue_1299.OtherS where
  g : (Core.Option.Option Tests.Legacy__side_effects.Issue_1299.Foo)

def Tests.Legacy__side_effects.Issue_1299.Impl.from
  (i : Tests.Legacy__side_effects.Issue_1299.Foo)
  : Result Tests.Legacy__side_effects.Issue_1299.Foo
  := do
  (Tests.Legacy__side_effects.Issue_1299.Foo.mk
    (y := (← Core.Clone.Clone.clone
        (Tests.Legacy__side_effects.Issue_1299.Foo.y i))))

structure Tests.Legacy__side_effects.Issue_1299.Error where


def Tests.Legacy__side_effects.Issue_1299.Impl_1.from
  (i : Tests.Legacy__side_effects.Issue_1299.OtherS)
  : Result
  (Core.Result.Result
    Tests.Legacy__side_effects.Issue_1299.S
    Tests.Legacy__side_effects.Issue_1299.Error)
  := do
  (match
    (← Core.Option.Impl.ok_or
        Tests.Legacy__side_effects.Issue_1299.Foo
        Tests.Legacy__side_effects.Issue_1299.Error
        (← Core.Option.Impl.as_ref Tests.Legacy__side_effects.Issue_1299.Foo
            (Tests.Legacy__side_effects.Issue_1299.OtherS.g i))
        Tests.Legacy__side_effects.Issue_1299.Error.mk)
  with
    | (Core.Result.Result.Ok hoist47)
      => do
        (Core.Result.Result.Ok
          (Tests.Legacy__side_effects.Issue_1299.S.mk
            (g := (← Tests.Legacy__side_effects.Issue_1299.Impl.from hoist47))))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

class Tests.Legacy__side_effects.Issue_1083.MyFrom
  (Self : Type) (T : Type)
  where
  my_from : T -> Result Self

instance Tests.Legacy__side_effects.Issue_1083.Impl :
  Tests.Legacy__side_effects.Issue_1083.MyFrom u16 u8
  where
  my_from (x : u8) := do (← Rust_primitives.Hax.cast_op x)

def Tests.Legacy__side_effects.Issue_1083.f
  (x : u8)
  : Result (Core.Result.Result u16 u16)
  := do
  (match
    (← Core.Ops.Try_trait.Try.branch (Core.Result.Result.Err (1 : u8)))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break residual)
      => do (← Core.Ops.Try_trait.FromResidual.from_residual residual)
    | (Core.Ops.Control_flow.ControlFlow.Continue val)
      => do
        let _ ← (pure val);
        (Core.Result.Result.Ok
          (← Tests.Legacy__side_effects.Issue_1083.MyFrom.my_from x)))

--  Helper function
def Tests.Legacy__side_effects.add3
  (x : u32)
  (y : u32)
  (z : u32)
  : Result u32
  := do
  (← Core.Num.Impl_8.wrapping_add (← Core.Num.Impl_8.wrapping_add x y) z)

--  Exercise local mutation with control flow and loops
--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__side_effects.local_mutation (x : u32) : Result u32 := do
  let y : u32 ← (pure (0 : u32));
  let x : u32 ← (pure (← Core.Num.Impl_8.wrapping_add x (1 : u32)));
  (← if (← Rust_primitives.Hax.Machine_int.gt x (3 : u32)) then do
    let x : u32 ← (pure (← Core.Num.Impl_8.wrapping_sub x (3 : u32)));
    let y : u32 ← (pure (← x /? (2 : u32)));
    let y : u32 ← (pure (← Core.Num.Impl_8.wrapping_add y (2 : u32)));
    let y : u32 ← (pure
      (← Core.Iter.Traits.Iterator.Iterator.fold
          (← Core.Iter.Traits.Collect.IntoIterator.into_iter
              (Core.Ops.Range.Range.mk
                (start := (0 : u32)) (_end := (10 : u32))))
          y
          (fun y i => (do (← Core.Num.Impl_8.wrapping_add x i) : Result u32))));
    (← Core.Num.Impl_8.wrapping_add x y)
  else do
    let ⟨⟨x, y⟩, hoist7⟩ ← (pure
      (match x with
        | sorry
          => do
            let y : u32 ← (pure (← Core.Num.Impl_8.wrapping_add x y));
            (Rust_primitives.Hax.Tuple2.mk
              (Rust_primitives.Hax.Tuple2.mk x y) (3 : u32))
        | sorry
          => do
            let x : u32 ← (pure (← Core.Num.Impl_8.wrapping_add x (1 : u32)));
            (Rust_primitives.Hax.Tuple2.mk
              (Rust_primitives.Hax.Tuple2.mk x y)
              (← Tests.Legacy__side_effects.add3
                  x
                  (← Core.Num.Impl_8.wrapping_add (123 : u32) x)
                  x))
        | _
          => do
            (Rust_primitives.Hax.Tuple2.mk
              (Rust_primitives.Hax.Tuple2.mk x y) (0 : u32))));
    let x : u32 ← (pure hoist7);
    (← Core.Num.Impl_8.wrapping_add x y))

--  Exercise early returns with control flow and loops
def Tests.Legacy__side_effects.early_returns (x : u32) : Result u32 := do
  (← if (← Rust_primitives.Hax.Machine_int.gt x (3 : u32)) then do
    (0 : u32)
  else do
    (← if (← Rust_primitives.Hax.Machine_int.gt x (30 : u32)) then do
      (match true with
        | sorry => do (34 : u32)
        | _
          => do
            let ⟨x, hoist11⟩ ← (pure
              (Rust_primitives.Hax.Tuple2.mk x (3 : u32)));
            (← Core.Num.Impl_8.wrapping_add
                (← Core.Num.Impl_8.wrapping_add (123 : u32) hoist11)
                x))
    else do
      let x : u32 ← (pure (← x +? (9 : u32)));
      let ⟨x, hoist11⟩ ← (pure
        (Rust_primitives.Hax.Tuple2.mk x (← x +? (1 : u32))));
      (← Core.Num.Impl_8.wrapping_add
          (← Core.Num.Impl_8.wrapping_add (123 : u32) hoist11)
          x)))

def Tests.Legacy__side_effects.simplifiable_return
  (c1 : Bool)
  (c2 : Bool)
  (c3 : Bool)
  : Result i32
  := do
  let x : i32 ← (pure (0 : i32));
  (← if c1 then do
    (← if c2 then do
      let x : i32 ← (pure (← x +? (10 : i32)));
      (← if c3 then do (1 : i32) else do (← x +? (1 : i32)))
    else do
      (← x +? (1 : i32)))
  else do
    x)

def Tests.Legacy__side_effects.simplifiable_question_mark
  (c : Bool)
  (x : (Core.Option.Option i32))
  : Result (Core.Option.Option i32)
  := do
  (← if c then do
    (match x with
      | (Core.Option.Option.Some hoist16)
        => do
          let a : i32 ← (pure (← hoist16 +? (10 : i32)));
          let b : i32 ← (pure (20 : i32));
          (Core.Option.Option.Some (← a +? b))
      | (Core.Option.Option.None ) => do Core.Option.Option.None)
  else do
    let a : i32 ← (pure (0 : i32));
    let b : i32 ← (pure (20 : i32));
    (Core.Option.Option.Some (← a +? b)))

--  Question mark without error coercion
def Tests.Legacy__side_effects.direct_result_question_mark
  (y : (Core.Result.Result Rust_primitives.Hax.Tuple0 u32))
  : Result (Core.Result.Result i8 u32)
  := do
  (match y with
    | (Core.Result.Result.Ok _) => do (Core.Result.Result.Ok (0 : i8))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

--  Question mark with an error coercion
def Tests.Legacy__side_effects.direct_result_question_mark_coercion
  (y : (Core.Result.Result i8 u16))
  : Result (Core.Result.Result i8 u32)
  := do
  (match y with
    | (Core.Result.Result.Ok hoist17) => do (Core.Result.Result.Ok hoist17)
    | (Core.Result.Result.Err err)
      => do (Core.Result.Result.Err (← Core.Convert.From.from err)))

--  Test question mark on `Option`s with some control flow
def Tests.Legacy__side_effects.options
  (x : (Core.Option.Option u8))
  (y : (Core.Option.Option u8))
  (z : (Core.Option.Option u64))
  : Result (Core.Option.Option u8)
  := do
  (match x with
    | (Core.Option.Option.Some hoist21)
      => do
        (← if (← Rust_primitives.Hax.Machine_int.gt hoist21 (10 : u8)) then do
          (match x with
            | (Core.Option.Option.Some hoist23)
              => do
                (match
                  (Core.Option.Option.Some
                    (← Core.Num.Impl_6.wrapping_add hoist23 (3 : u8)))
                with
                  | (Core.Option.Option.Some hoist29)
                    => do
                      (match hoist29 with
                        | sorry
                          => do
                            (match Core.Option.Option.None with
                              | (Core.Option.Option.Some some)
                                => do
                                  let v : u8 ← (pure some);
                                  (match x with
                                    | (Core.Option.Option.Some hoist30)
                                      => do
                                        (match y with
                                          | (Core.Option.Option.Some hoist31)
                                            => do
                                              (Core.Option.Option.Some
                                                (← Core.Num.Impl_6.wrapping_add
                                                    (← Core.Num.Impl_6.wrapping_add
                                                        v
                                                        hoist30)
                                                    hoist31))
                                          | (Core.Option.Option.None )
                                            => do Core.Option.Option.None)
                                    | (Core.Option.Option.None )
                                      => do Core.Option.Option.None)
                              | (Core.Option.Option.None )
                                => do Core.Option.Option.None)
                        | sorry
                          => do
                            (match z with
                              | (Core.Option.Option.Some hoist18)
                                => do
                                  let v : u8 ← (pure
                                    (← (4 : u8)
                                      +? (← if
                                      (← Rust_primitives.Hax.Machine_int.gt
                                          hoist18
                                          (4 : u64)) then do
                                        (0 : u8)
                                      else do
                                        (3 : u8))));
                                  (match x with
                                    | (Core.Option.Option.Some hoist30)
                                      => do
                                        (match y with
                                          | (Core.Option.Option.Some hoist31)
                                            => do
                                              (Core.Option.Option.Some
                                                (← Core.Num.Impl_6.wrapping_add
                                                    (← Core.Num.Impl_6.wrapping_add
                                                        v
                                                        hoist30)
                                                    hoist31))
                                          | (Core.Option.Option.None )
                                            => do Core.Option.Option.None)
                                    | (Core.Option.Option.None )
                                      => do Core.Option.Option.None)
                              | (Core.Option.Option.None )
                                => do Core.Option.Option.None)
                        | _
                          => do
                            let v : u8 ← (pure (12 : u8));
                            (match x with
                              | (Core.Option.Option.Some hoist30)
                                => do
                                  (match y with
                                    | (Core.Option.Option.Some hoist31)
                                      => do
                                        (Core.Option.Option.Some
                                          (← Core.Num.Impl_6.wrapping_add
                                              (← Core.Num.Impl_6.wrapping_add
                                                  v
                                                  hoist30)
                                              hoist31))
                                    | (Core.Option.Option.None )
                                      => do Core.Option.Option.None)
                              | (Core.Option.Option.None )
                                => do Core.Option.Option.None))
                  | (Core.Option.Option.None ) => do Core.Option.Option.None)
            | (Core.Option.Option.None ) => do Core.Option.Option.None)
        else do
          (match x with
            | (Core.Option.Option.Some hoist26)
              => do
                (match y with
                  | (Core.Option.Option.Some hoist25)
                    => do
                      (match
                        (Core.Option.Option.Some
                          (← Core.Num.Impl_6.wrapping_add hoist26 hoist25))
                      with
                        | (Core.Option.Option.Some hoist29)
                          => do
                            (match hoist29 with
                              | sorry
                                => do
                                  (match Core.Option.Option.None with
                                    | (Core.Option.Option.Some some)
                                      => do
                                        let v : u8 ← (pure some);
                                        (match x with
                                          | (Core.Option.Option.Some hoist30)
                                            => do
                                              (match y with
                                                | (Core.Option.Option.Some
                                                    hoist31)
                                                  => do
                                                    (Core.Option.Option.Some
                                                      (← Core.Num.Impl_6.wrapping_add
                                                          (← Core.Num.Impl_6.wrapping_add
                                                              v
                                                              hoist30)
                                                          hoist31))
                                                | (Core.Option.Option.None )
                                                  => do Core.Option.Option.None)
                                          | (Core.Option.Option.None )
                                            => do Core.Option.Option.None)
                                    | (Core.Option.Option.None )
                                      => do Core.Option.Option.None)
                              | sorry
                                => do
                                  (match z with
                                    | (Core.Option.Option.Some hoist18)
                                      => do
                                        let v : u8 ← (pure
                                          (← (4 : u8)
                                            +? (← if
                                            (← Rust_primitives.Hax.Machine_int.gt
                                                hoist18
                                                (4 : u64)) then do
                                              (0 : u8)
                                            else do
                                              (3 : u8))));
                                        (match x with
                                          | (Core.Option.Option.Some hoist30)
                                            => do
                                              (match y with
                                                | (Core.Option.Option.Some
                                                    hoist31)
                                                  => do
                                                    (Core.Option.Option.Some
                                                      (← Core.Num.Impl_6.wrapping_add
                                                          (← Core.Num.Impl_6.wrapping_add
                                                              v
                                                              hoist30)
                                                          hoist31))
                                                | (Core.Option.Option.None )
                                                  => do Core.Option.Option.None)
                                          | (Core.Option.Option.None )
                                            => do Core.Option.Option.None)
                                    | (Core.Option.Option.None )
                                      => do Core.Option.Option.None)
                              | _
                                => do
                                  let v : u8 ← (pure (12 : u8));
                                  (match x with
                                    | (Core.Option.Option.Some hoist30)
                                      => do
                                        (match y with
                                          | (Core.Option.Option.Some hoist31)
                                            => do
                                              (Core.Option.Option.Some
                                                (← Core.Num.Impl_6.wrapping_add
                                                    (← Core.Num.Impl_6.wrapping_add
                                                        v
                                                        hoist30)
                                                    hoist31))
                                          | (Core.Option.Option.None )
                                            => do Core.Option.Option.None)
                                    | (Core.Option.Option.None )
                                      => do Core.Option.Option.None))
                        | (Core.Option.Option.None )
                          => do Core.Option.Option.None)
                  | (Core.Option.Option.None ) => do Core.Option.Option.None)
            | (Core.Option.Option.None ) => do Core.Option.Option.None))
    | (Core.Option.Option.None ) => do Core.Option.Option.None)

--  Test question mark on `Result`s with local mutation
def Tests.Legacy__side_effects.question_mark
  (x : u32)
  : Result (Core.Result.Result u32 u32)
  := do
  (← if (← Rust_primitives.Hax.Machine_int.gt x (40 : u32)) then do
    let y : u32 ← (pure (0 : u32));
    let x : u32 ← (pure (← Core.Num.Impl_8.wrapping_add x (3 : u32)));
    let y : u32 ← (pure (← Core.Num.Impl_8.wrapping_add x y));
    let x : u32 ← (pure (← Core.Num.Impl_8.wrapping_add x y));
    (← if (← Rust_primitives.Hax.Machine_int.gt x (90 : u32)) then do
      (match (Core.Result.Result.Err (12 : u8)) with
        | (Core.Result.Result.Ok ok)
          => do
            (Core.Result.Result.Ok (← Core.Num.Impl_8.wrapping_add (3 : u32) x))
        | (Core.Result.Result.Err err)
          => do (Core.Result.Result.Err (← Core.Convert.From.from err)))
    else do
      (Core.Result.Result.Ok (← Core.Num.Impl_8.wrapping_add (3 : u32) x)))
  else do
    (Core.Result.Result.Ok (← Core.Num.Impl_8.wrapping_add (3 : u32) x)))

structure Tests.Legacy__side_effects.A where


structure Tests.Legacy__side_effects.B where


--  Combine `?` and early return
def Tests.Legacy__side_effects.monad_lifting
  (x : u8)
  : Result
  (Core.Result.Result Tests.Legacy__side_effects.A Tests.Legacy__side_effects.B)
  := do
  (← if (← Rust_primitives.Hax.Machine_int.gt x (123 : u8)) then do
    (match (Core.Result.Result.Err Tests.Legacy__side_effects.B.mk) with
      | (Core.Result.Result.Ok hoist35) => do (Core.Result.Result.Ok hoist35)
      | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))
  else do
    (Core.Result.Result.Ok Tests.Legacy__side_effects.A.mk))

structure Tests.Legacy__side_effects.Bar where
  a : Bool
  b : (Rust_primitives.Hax.Tuple2
      (RustArray (Rust_primitives.Hax.Tuple2 Bool Bool) 6)
      Bool)

structure Tests.Legacy__side_effects.Foo where
  x : Bool
  y : (Rust_primitives.Hax.Tuple2
      Bool
      (Alloc.Vec.Vec Tests.Legacy__side_effects.Bar Alloc.Alloc.Global))
  z : (RustArray Tests.Legacy__side_effects.Bar 6)
  bar : Tests.Legacy__side_effects.Bar

--  Test assignation on non-trivial places
--  @fail(extraction): coq(HAX0002, HAX0002), ssprove(HAX0001)
--  @fail(extraction): proverif(HAX0002, HAX0002, HAX0002, HAX0002)
def Tests.Legacy__side_effects.assign_non_trivial_lhs
  (foo : Tests.Legacy__side_effects.Foo)
  : Result Tests.Legacy__side_effects.Foo
  := do
  let foo : Tests.Legacy__side_effects.Foo ← (pure sorry);
  let foo : Tests.Legacy__side_effects.Foo ← (pure sorry);
  let foo : Tests.Legacy__side_effects.Foo ← (pure sorry);
  let foo : Tests.Legacy__side_effects.Foo ← (pure sorry);
  let foo : Tests.Legacy__side_effects.Foo ← (pure sorry);
  foo

def Tests.Legacy__side_effects.Issue_1300.fun
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Rust_primitives.Hax.Tuple0 u8)
  := do
  (match
    (← Core.Iter.Traits.Iterator.Iterator.collect
        (Core.Result.Result
          (Alloc.Vec.Vec
            (Rust_primitives.Hax.Tuple2 u8 (RustArray u8 32))
            Alloc.Alloc.Global)
          u8)
        (← Core.Iter.Traits.Iterator.Iterator.map
            (Core.Result.Result
              (Rust_primitives.Hax.Tuple2 u8 (RustArray u8 32))
              u8)
            u8
            -> Result (Core.Result.Result
              (Rust_primitives.Hax.Tuple2 u8 (RustArray u8 32))
              u8)
            (← Core.Slice.Impl.iter u8
                (← Rust_primitives.unsize
                    (← Rust_primitives.Hax.repeat (0 : u8) (5 : usize))))
            (fun prev => (do
                (match
                  (Core.Result.Result.Ok
                    (← Rust_primitives.Hax.repeat (0 : u8) (32 : usize)))
                with
                  | (Core.Result.Result.Ok hoist45)
                    => do
                      (Core.Result.Result.Ok
                        (Rust_primitives.Hax.Tuple2.mk prev hoist45))
                  | (Core.Result.Result.Err err)
                    => do (Core.Result.Result.Err err)) : Result
                (Core.Result.Result
                  (Rust_primitives.Hax.Tuple2 u8 (RustArray u8 32))
                  u8)))))
  with
    | (Core.Result.Result.Ok val)
      => do (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__side_effects.Issue_1089.test
  (x : (Core.Option.Option i32))
  (y : (Core.Option.Option i32))
  : Result (Core.Option.Option i32)
  := do
  (match
    (← Core.Option.Impl.map
        i32
        (Core.Option.Option i32)
        i32 -> Result (Core.Option.Option i32)
        x
        (fun i => (do
            (match y with
              | (Core.Option.Option.Some hoist38)
                => do (Core.Option.Option.Some (← i +? hoist38))
              | (Core.Option.Option.None ) => do Core.Option.Option.None) :
            Result (Core.Option.Option i32))))
  with
    | (Core.Option.Option.Some some) => do some
    | (Core.Option.Option.None ) => do Core.Option.Option.None)