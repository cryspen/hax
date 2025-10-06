
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

structure Tests.Legacy__mut_ref_functionalization.S where
  b : (RustArray u8 5)

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__mut_ref_functionalization.foo
  (lhs : Tests.Legacy__mut_ref_functionalization.S)
  (rhs : Tests.Legacy__mut_ref_functionalization.S)
  : Result Tests.Legacy__mut_ref_functionalization.S
  := do
  let lhs : Tests.Legacy__mut_ref_functionalization.S ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (1 : usize)
        (fun lhs _ => (do true : Result Bool))
        lhs
        (fun lhs i => (do
            sorry : Result Tests.Legacy__mut_ref_functionalization.S))));
  lhs

def Tests.Legacy__mut_ref_functionalization.Impl.update
  (self : Tests.Legacy__mut_ref_functionalization.S)
  (x : u8)
  : Result Tests.Legacy__mut_ref_functionalization.S
  := do
  let self : Tests.Legacy__mut_ref_functionalization.S ← (pure sorry);
  self

def Tests.Legacy__mut_ref_functionalization.index_mutation
  (x : (Core.Ops.Range.Range usize))
  (a : (RustSlice u8))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let v : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Slice.Impl.into_vec u8 Alloc.Alloc.Global
        (← Rust_primitives.unsize
            (← Rust_primitives.Hax.box_new #v[(1 : u8)]))));
  let v : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_range
        v
        x
        (← Core.Slice.Impl.copy_from_slice u8 (← v[x]_?) a)));
  let v : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        v
        (1 : usize)
        (3 : u8)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__mut_ref_functionalization.index_mutation_unsize
  (x : (RustArray u8 12))
  : Result u8
  := do
  let x : (RustArray u8 12) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_range
        x
        (Core.Ops.Range.Range.mk (start := (4 : usize)) (_end := (5 : usize)))
        (← Core.Slice.Impl.copy_from_slice u8
            (← x[
              (Core.Ops.Range.Range.mk
                (start := (4 : usize)) (_end := (5 : usize)))
              ]_?)
            (← Rust_primitives.unsize #v[(1 : u8), (2 : u8)]))));
  (42 : u8)

def Tests.Legacy__mut_ref_functionalization.build_vec
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  (← Alloc.Slice.Impl.into_vec u8 Alloc.Alloc.Global
      (← Rust_primitives.unsize
          (← Rust_primitives.Hax.box_new #v[(1 : u8), (2 : u8), (3 : u8)])))

def Tests.Legacy__mut_ref_functionalization.test_append
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let vec1 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk));
  let vec2 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Slice.Impl.into_vec u8 Alloc.Alloc.Global
        (← Rust_primitives.unsize
            (← Rust_primitives.Hax.box_new #v[(1 : u8), (2 : u8), (3 : u8)]))));
  let ⟨tmp0, tmp1⟩ ← (pure
    (← Alloc.Vec.Impl_1.append u8 Alloc.Alloc.Global vec1 vec2));
  let vec1 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure tmp0);
  let vec2 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure tmp1);
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let vec1 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl_1.append u8 Alloc.Alloc.Global
        vec1
        (← Tests.Legacy__mut_ref_functionalization.build_vec
            Rust_primitives.Hax.Tuple0.mk)));
  vec1

def Tests.Legacy__mut_ref_functionalization.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let vec : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk));
  let vec : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global vec (1 : u8)));
  let vec : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global vec (2 : u8)));
  let vec : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Core.Slice.Impl.swap u8 vec (0 : usize) (1 : usize)));
  let vec : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Core.Slice.Impl.swap u8 vec (0 : usize) (1 : usize)));
  vec

structure Tests.Legacy__mut_ref_functionalization.Foo where
  field : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

structure Tests.Legacy__mut_ref_functionalization.Pair (T : Type) where
  a : T
  b : Tests.Legacy__mut_ref_functionalization.Foo

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__mut_ref_functionalization.g
  (x :
  (Tests.Legacy__mut_ref_functionalization.Pair
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let
    x : (Tests.Legacy__mut_ref_functionalization.Pair
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)) ← (pure x);
  let
    x : (Tests.Legacy__mut_ref_functionalization.Pair
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (1 : u8)
        (10 : u8)
        (fun x _ => (do true : Result Bool))
        x
        (fun x i => (do
            sorry : Result
            (Tests.Legacy__mut_ref_functionalization.Pair
              (Alloc.Vec.Vec u8 Alloc.Alloc.Global))))));
  let
    x : (Tests.Legacy__mut_ref_functionalization.Pair
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)) ← (pure sorry);
  let
    x : (Tests.Legacy__mut_ref_functionalization.Pair
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)) ← (pure sorry);
  (Tests.Legacy__mut_ref_functionalization.Pair.a x)

def Tests.Legacy__mut_ref_functionalization.h (x : u8) : Result u8 := do
  let x : u8 ← (pure (← x +? (10 : u8)));
  x

structure Tests.Legacy__mut_ref_functionalization.Bar where
  a : u8
  b : u8

def Tests.Legacy__mut_ref_functionalization.i
  (bar : Tests.Legacy__mut_ref_functionalization.Bar)
  : Result
  (Rust_primitives.Hax.Tuple2 Tests.Legacy__mut_ref_functionalization.Bar u8)
  := do
  let bar : Tests.Legacy__mut_ref_functionalization.Bar ← (pure sorry);
  let bar : Tests.Legacy__mut_ref_functionalization.Bar ← (pure sorry);
  let hax_temp_output : u8 ← (pure
    (← (Tests.Legacy__mut_ref_functionalization.Bar.a bar)
      +? (Tests.Legacy__mut_ref_functionalization.Bar.b bar)));
  (Rust_primitives.Hax.Tuple2.mk bar hax_temp_output)

def Tests.Legacy__mut_ref_functionalization.j
  (x : Tests.Legacy__mut_ref_functionalization.Bar)
  : Result
  (Rust_primitives.Hax.Tuple2 Tests.Legacy__mut_ref_functionalization.Bar u8)
  := do
  let out : u8 ← (pure (123 : u8));
  let ⟨tmp0, out1⟩ ← (pure (← Tests.Legacy__mut_ref_functionalization.i x));
  let x : Tests.Legacy__mut_ref_functionalization.Bar ← (pure tmp0);
  let hax_temp_output : u8 ← (pure (← out1 +? out));
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__mut_ref_functionalization.k
  (vec : (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  (arg_1_wild3 : u16)
  (arg_1_wild : u8)
  (arg_3_wild2 : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple4
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
    u16
    Rust_primitives.Hax.Tuple0
    u64)
  := do
  let arg_1_wild2 : u8 ← (pure (← vec[(1 : usize)]_?));
  let arg_3_wild : u8 ← (pure (← vec[(2 : usize)]_?));
  let arg_1_wild1 : u8 ← (pure (← vec[(3 : usize)]_?));
  let arg_3_wild1 : u8 ← (pure (← vec[(4 : usize)]_?));
  let vec : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        vec
        (0 : usize)
        (← (← (← (← arg_1_wild +? arg_3_wild) +? arg_1_wild1) +? arg_3_wild1)
          +? arg_1_wild)));
  let hax_temp_output : u64 ← (pure (12345 : u64));
  (Rust_primitives.Hax.Tuple4.mk vec arg_1_wild3 arg_3_wild2 hax_temp_output)

class Tests.Legacy__mut_ref_functionalization.FooTrait (Self : Type) where
  z : Self -> Result Self

instance Tests.Legacy__mut_ref_functionalization.Impl_1 :
  Tests.Legacy__mut_ref_functionalization.FooTrait
  Tests.Legacy__mut_ref_functionalization.Foo
  where
  z (self : Tests.Legacy__mut_ref_functionalization.Foo) := do self

def Tests.Legacy__mut_ref_functionalization.array
  (x : (RustArray u8 10))
  : Result (RustArray u8 10)
  := do
  let x : (RustArray u8 10) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        x
        (1 : usize)
        (← x[(2 : usize)]_?)));
  x