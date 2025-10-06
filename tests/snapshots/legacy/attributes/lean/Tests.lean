
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

def Tests.Legacy__attributes.Verifcation_status.a_function_which_only_laxes
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Hax_lib.assert false)

def Tests.Legacy__attributes.Verifcation_status._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Verifcation_status._.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : u8)
  : Result Bool
  := do
  false

def Tests.Legacy__attributes.Verifcation_status.a_panicfree_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u8
  := do
  let a : u8 ← (pure (3 : u8));
  let b : u8 ← (pure (6 : u8));
  let result : u8 ← (pure (← a +? b));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  result

def Tests.Legacy__attributes.Verifcation_status.__1.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Verifcation_status.__1.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  false

def Tests.Legacy__attributes.Verifcation_status.another_panicfree_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let not_much : i32 ← (pure (0 : i32));
  let nothing : i32 ← (pure (0 : i32));
  let still_not_much : i32 ← (pure (← not_much +? nothing));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.Requires_mut._.requires
  (Self_ : Type) (x : u8)
  (y : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.lt
      (← Rust_primitives.Hax.Int.add
          (← Rust_primitives.Hax.Int.from_machine x)
          (← Rust_primitives.Hax.Int.from_machine y))
      (← Hax_lib.Int.Impl_7._unsafe_from_str "254"))

def Tests.Legacy__attributes.Requires_mut.__1.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Requires_mut.__1.ensures
  (Self_ : Type) (x : u8)
  (y : u8)
  (⟨y_future, output_variable⟩ : (Rust_primitives.Hax.Tuple2 u8 u8))
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.eq output_variable y_future)

class Tests.Legacy__attributes.Requires_mut.Foo (Self : Type) where
  f : u8 -> u8 -> Result (Rust_primitives.Hax.Tuple2 u8 u8)
  g : u8 -> u8 -> Result u8
  h : u8 -> u8 -> Result Rust_primitives.Hax.Tuple0
  i : u8 -> u8 -> Result u8

def Tests.Legacy__attributes.Requires_mut.Impl.f._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Requires_mut.Impl.f._.ensures
  (x : u8)
  (y : u8)
  (⟨y_future, output_variable⟩ : (Rust_primitives.Hax.Tuple2 u8 u8))
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.eq output_variable y_future)

def Tests.Legacy__attributes.Requires_mut.Impl.f.__1.requires
  (x : u8)
  (y : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.lt
      (← Rust_primitives.Hax.Int.add
          (← Rust_primitives.Hax.Int.from_machine x)
          (← Rust_primitives.Hax.Int.from_machine y))
      (← Hax_lib.Int.Impl_7._unsafe_from_str "254"))

def Tests.Legacy__attributes.Requires_mut.Impl.g._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Requires_mut.Impl.g._.ensures
  (x : u8)
  (y : u8)
  (output_variable : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.eq output_variable y)

def Tests.Legacy__attributes.Requires_mut.Impl.g.__1.requires
  (x : u8)
  (y : u8)
  : Result Bool
  := do
  true

def Tests.Legacy__attributes.Requires_mut.Impl.h._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Requires_mut.Impl.h._.ensures
  (x : u8)
  (y : u8)
  (output_variable : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  (← Core.Cmp.PartialEq.eq output_variable Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__attributes.Requires_mut.Impl.h.__1.requires
  (x : u8)
  (y : u8)
  : Result Bool
  := do
  true

def Tests.Legacy__attributes.Requires_mut.Impl.i._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Requires_mut.Impl.i._.ensures
  (x : u8)
  (y : u8)
  (y_future : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.eq y_future y)

def Tests.Legacy__attributes.Requires_mut.Impl.i.__1.requires
  (x : u8)
  (y : u8)
  : Result Bool
  := do
  true

instance Tests.Legacy__attributes.Requires_mut.Impl :
  Tests.Legacy__attributes.Requires_mut.Foo Rust_primitives.Hax.Tuple0
  where
  f (x : u8) (y : u8) := do
    let y : u8 ← (pure (← y +? x));
    let hax_temp_output : u8 ← (pure y);
    (Rust_primitives.Hax.Tuple2.mk y hax_temp_output)
  g (x : u8) (y : u8) := do y
  h (x : u8) (y : u8) := do Rust_primitives.Hax.Tuple0.mk
  i (x : u8) (y : u8) := do let _ ← (pure Rust_primitives.Hax.Tuple0.mk); y

def Tests.Legacy__attributes.Replace_body.f (x : u8) (y : u8) : Result u8 := do
  (← (1 : u8) +? (2 : u8))

structure Tests.Legacy__attributes.Replace_body.Foo where


def Tests.Legacy__attributes.Replace_body.Impl.assoc_fn
  (self : Tests.Legacy__attributes.Replace_body.Foo)
  (x : u8)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

instance Tests.Legacy__attributes.Replace_body.Impl_1 :
  Alloc.String.ToString Tests.Legacy__attributes.Replace_body.Foo
  where
  to_string (self : Tests.Legacy__attributes.Replace_body.Foo) := do
    (← Core.Convert.Into.into "Hello")

structure Tests.Legacy__attributes.Reorder.Foo where
  field_3 : u8
  field_4 : u8
  field_2 : u8
  field_1 : u8

inductive Tests.Legacy__attributes.Reorder.Bar : Type
| A (a_field_3 : u8)
    (a_field_1 : u8)
    (a_field_2 : u8)
    : Tests.Legacy__attributes.Reorder.Bar 
| B (b_field_1 : u8)
    (b_field_3 : u8)
    (b_field_2 : u8)
    : Tests.Legacy__attributes.Reorder.Bar 


def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedU8._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedU8._.ensures
  -- Unsupported const param -- Unsupported const param (_ :
  Rust_primitives.Hax.Tuple0)
  (x : u8)
  : Result Bool
  := do
  (← (← Rust_primitives.Hax.Machine_int.ge x MIN)
    &&? (← Rust_primitives.Hax.Machine_int.le x MAX))

abbrev Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedU8.BoundedU8
:= u8

def Tests.Legacy__attributes.Refinement_types.bounded_u8
  (x :
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedU8.BoundedU8
    (12 : u8)
    (15 : u8)))
  (y :
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedU8.BoundedU8
    (10 : u8)
    (11 : u8)))
  : Result
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedU8.BoundedU8
    (1 : u8)
    (23 : u8))
  := do
  (← (← (← x : u8) +? (← y : u8)) :
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedU8.BoundedU8
    (1 : u8)
    (23 : u8)))

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__Even._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__Even._.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.eq (← x %? (2 : u8)) (0 : u8))

abbrev Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__Even.Even
:= u8

def Tests.Legacy__attributes.Refinement_types._.requires
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.lt x (127 : u8))

def Tests.Legacy__attributes.Refinement_types.double
  (x : u8)
  : Result
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__Even.Even
  := do
  (← (← x +? x) :
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__Even.Even)

def Tests.Legacy__attributes.Refinement_types.__1.requires
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.lt x (127 : u8))

def Tests.Legacy__attributes.Refinement_types.double_refine
  (x : u8)
  : Result
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__Even.Even
  := do
  (← (← x +? x) :
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__Even.Even)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__NoE._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__NoE._.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : Alloc.String.String)
  : Result Bool
  := do
  let ⟨_, out⟩ ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.any Char -> Result Bool
        (← Core.Str.Impl.chars (← Core.Ops.Deref.Deref.deref x))
        (fun ch => (do (← Core.Cmp.PartialEq.eq ch ' ') : Result Bool))));
  (← Core.Ops.Bit.Not.not out)

abbrev Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__NoE.NoE
:= Alloc.String.String

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__ModInverse._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__ModInverse._.ensures
  -- Unsupported const param (_ : Rust_primitives.Hax.Tuple0)
  (n : u32)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.eq
      (← (← (← Rust_primitives.Hax.cast_op n)
          *? (← Rust_primitives.Hax.cast_op MOD))
        %? (← Rust_primitives.Hax.cast_op MOD))
      (1 : u128))

abbrev Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__ModInverse.ModInverse
:= u32

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__FieldElement._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__FieldElement._.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : u16)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.le x (2347 : u16))

abbrev Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__FieldElement.FieldElement
:= u16

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__CompressionFactor._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__CompressionFactor._.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : u8)
  : Result Bool
  := do
  (← (← (← (← Rust_primitives.Hax.Machine_int.eq x (4 : u8))
        ||? (← Rust_primitives.Hax.Machine_int.eq x (5 : u8)))
      ||? (← Rust_primitives.Hax.Machine_int.eq x (10 : u8)))
    ||? (← Rust_primitives.Hax.Machine_int.eq x (11 : u8)))

abbrev Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__CompressionFactor.CompressionFactor
:= u8

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16._.ensures
  -- Unsupported const param (_ : Rust_primitives.Hax.Tuple0)
  (x : i16)
  : Result Bool
  := do
  (← (← (← Rust_primitives.Hax.Int.lt
          (← Rust_primitives.Hax.Int.from_machine B)
          (← Hax_lib.Int.Impl_7._unsafe_from_str "32768"))
      &&? (← Rust_primitives.Hax.Int.ge
          (← Rust_primitives.Hax.Int.from_machine x)
          (← Rust_primitives.Hax.Int.neg
              (← Rust_primitives.Hax.Int.from_machine B))))
    &&? (← Rust_primitives.Hax.Int.le
        (← Rust_primitives.Hax.Int.from_machine x)
        (← Rust_primitives.Hax.Int.from_machine B)))

abbrev Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
:= i16

instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl
  -- Unsupported const param :
  Core.Clone.Clone
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl_1
  -- Unsupported const param :
  Core.Marker.Copy
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl_3
  -- Unsupported const param :
  Core.Marker.StructuralPartialEq
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl_4
  -- Unsupported const param :
  Core.Cmp.PartialEq
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl_2
  -- Unsupported const param :
  Core.Cmp.Eq
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl_6
  -- Unsupported const param :
  Core.Cmp.PartialOrd
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl_5
  -- Unsupported const param :
  Core.Cmp.Ord
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


instance
  Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.Impl_7
  -- Unsupported const param :
  Core.Hash.Hash
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    B)
  where


def Tests.Legacy__attributes.Refinement_types.__3.requires
  -- Unsupported const param -- Unsupported const param (x :
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    N))
  : Result Bool
  := do
  (← (← Rust_primitives.Hax.Int.lt
        (← Rust_primitives.Hax.Int.from_machine M)
        (← Hax_lib.Int.Impl_7._unsafe_from_str "32768"))
    &&? (← Rust_primitives.Hax.Int.eq
        (← Rust_primitives.Hax.Int.from_machine M)
        (← Rust_primitives.Hax.Int.mul
            (← Rust_primitives.Hax.Int.from_machine N)
            (← Hax_lib.Int.Impl_7._unsafe_from_str "2"))))

def Tests.Legacy__attributes.Refinement_types.double_abs_i16
  -- Unsupported const param -- Unsupported const param (x :
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    N))
  : Result
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    M)
  := do
  (← (← Core.Ops.Arith.Mul.mul x (2 : i16)) :
  (Tests.Legacy__attributes.Refinement_types.Hax__autogenerated_refinement__BoundedAbsI16.BoundedAbsI16
    M))

def Tests.Legacy__attributes.Refined_indexes.MAX : usize := 10

structure Tests.Legacy__attributes.Refined_indexes.MyArray where
  _0 : (RustArray u8 (10 : usize))

def Tests.Legacy__attributes.Refined_indexes.Impl_1.index._.requires
  (self_ : Tests.Legacy__attributes.Refined_indexes.MyArray)
  (index : usize)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.lt
      index
      Tests.Legacy__attributes.Refined_indexes.MAX)

def Tests.Legacy__attributes.Refined_indexes.mutation_example
  (use_generic_update_at : Tests.Legacy__attributes.Refined_indexes.MyArray)
  (use_specialized_update_at : (RustSlice u8))
  (specialized_as_well : (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  : Result
  (Rust_primitives.Hax.Tuple3
    Tests.Legacy__attributes.Refined_indexes.MyArray
    (RustSlice u8)
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  := do
  let use_generic_update_at : Tests.Legacy__attributes.Refined_indexes.MyArray ←
    (pure
    (← Rust_primitives.Hax.update_at
        use_generic_update_at
        (2 : usize)
        (0 : u8)));
  let use_specialized_update_at : (RustSlice u8) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        use_specialized_update_at
        (2 : usize)
        (0 : u8)));
  let specialized_as_well : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        specialized_as_well
        (2 : usize)
        (0 : u8)));
  (Rust_primitives.Hax.Tuple3.mk
    use_generic_update_at use_specialized_update_at specialized_as_well)

instance Tests.Legacy__attributes.Refined_indexes.Impl_1 :
  Core.Ops.Index.Index Tests.Legacy__attributes.Refined_indexes.MyArray usize
  where
  Output := u8
  index (self : Tests.Legacy__attributes.Refined_indexes.MyArray)
    (index : usize)
    := do
    (← Core.Ops.Index.Index.index self index)

structure Tests.Legacy__attributes.Refined_arithmetic.Foo where
  _0 : u8

def Tests.Legacy__attributes.Refined_arithmetic.Impl.add._.requires
  (self_ : Tests.Legacy__attributes.Refined_arithmetic.Foo)
  (rhs : Tests.Legacy__attributes.Refined_arithmetic.Foo)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.lt
      (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 self_)
      (← (255 : u8)
        -? (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 rhs)))

instance Tests.Legacy__attributes.Refined_arithmetic.Impl :
  Core.Ops.Arith.Add
  Tests.Legacy__attributes.Refined_arithmetic.Foo
  Tests.Legacy__attributes.Refined_arithmetic.Foo
  where
  Output := Tests.Legacy__attributes.Refined_arithmetic.Foo
  add (self : Tests.Legacy__attributes.Refined_arithmetic.Foo)
    (rhs : Tests.Legacy__attributes.Refined_arithmetic.Foo)
    := do
    (Tests.Legacy__attributes.Refined_arithmetic.Foo.mk
      (← (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 self)
        +? (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 rhs)))

def Tests.Legacy__attributes.Refined_arithmetic.Impl_1.mul._.requires
  (self_ : Tests.Legacy__attributes.Refined_arithmetic.Foo)
  (rhs : Tests.Legacy__attributes.Refined_arithmetic.Foo)
  : Result Bool
  := do
  (← (← Rust_primitives.Hax.Machine_int.eq
        (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 rhs)
        (0 : u8))
    ||? (← Rust_primitives.Hax.Machine_int.lt
        (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 self_)
        (← (255 : u8)
          /? (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 rhs))))

instance Tests.Legacy__attributes.Refined_arithmetic.Impl_1 :
  Core.Ops.Arith.Mul
  Tests.Legacy__attributes.Refined_arithmetic.Foo
  Tests.Legacy__attributes.Refined_arithmetic.Foo
  where
  Output := Tests.Legacy__attributes.Refined_arithmetic.Foo
  mul (self : Tests.Legacy__attributes.Refined_arithmetic.Foo)
    (rhs : Tests.Legacy__attributes.Refined_arithmetic.Foo)
    := do
    (Tests.Legacy__attributes.Refined_arithmetic.Foo.mk
      (← (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 self)
        *? (Tests.Legacy__attributes.Refined_arithmetic.Foo._0 rhs)))

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls._.requires
  (Self_ : Type) (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.le
      (← Rust_primitives.Hax.Int.from_machine x)
      (← Hax_lib.Int.Impl_7._unsafe_from_str "127"))

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.__1.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.__1.ensures
  (Self_ : Type) (x : u8)
  (result : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.eq
      (← Rust_primitives.Hax.Int.mul
          (← Rust_primitives.Hax.Int.from_machine x)
          (← Hax_lib.Int.Impl_7._unsafe_from_str "2"))
      (← Rust_primitives.Hax.Int.from_machine result))

class Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Operation
  (Self : Type)
  where
  double : u8 -> Result u8

structure Tests.Legacy__attributes.Pre_post_on_traits_and_impls.ViaAdd where


structure Tests.Legacy__attributes.Pre_post_on_traits_and_impls.ViaMul where


def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl.double._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl.double._.ensures
  (x : u8)
  (result : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.eq
      (← Rust_primitives.Hax.Int.mul
          (← Rust_primitives.Hax.Int.from_machine x)
          (← Hax_lib.Int.Impl_7._unsafe_from_str "2"))
      (← Rust_primitives.Hax.Int.from_machine result))

def
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl.double.__1.requires
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.le
      (← Rust_primitives.Hax.Int.from_machine x)
      (← Hax_lib.Int.Impl_7._unsafe_from_str "127"))

instance Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl :
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Operation
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.ViaAdd
  where
  double (x : u8) := do (← x +? x)

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl_1.double._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl_1.double._.ensures
  (x : u8)
  (result : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.eq
      (← Rust_primitives.Hax.Int.mul
          (← Rust_primitives.Hax.Int.from_machine x)
          (← Hax_lib.Int.Impl_7._unsafe_from_str "2"))
      (← Rust_primitives.Hax.Int.from_machine result))

def
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl_1.double.__1.requires
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Int.le
      (← Rust_primitives.Hax.Int.from_machine x)
      (← Hax_lib.Int.Impl_7._unsafe_from_str "127"))

instance Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Impl_1 :
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.Operation
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.ViaMul
  where
  double (x : u8) := do (← x *? (2 : u8))

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.__2.requires
  (Self_ : Type) (self_ : Self_)
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.lt x (100 : u8))

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.__3.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.__3.ensures
  (Self_ : Type) (self_ : Self_)
  (x : u8)
  (r : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.gt r (88 : u8))

class
  Tests.Legacy__attributes.Pre_post_on_traits_and_impls.TraitWithRequiresAndEnsures
  (Self : Type)
  where
  method : Self -> u8 -> Result u8

def Tests.Legacy__attributes.Pre_post_on_traits_and_impls.test
  (T : Type)
  [(Tests.Legacy__attributes.Pre_post_on_traits_and_impls.TraitWithRequiresAndEnsures
    T)]
  (x : T)
  : Result u8
  := do
  (← (← Tests.Legacy__attributes.Pre_post_on_traits_and_impls.TraitWithRequiresAndEnsures.method
        x
        (99 : u8))
    -? (88 : u8))

def Tests.Legacy__attributes.Newtype_pattern.MAX : usize := 10

def Tests.Legacy__attributes.Newtype_pattern._.refinement
  (i : usize)
  : Result Hax_lib.Prop.Prop
  := do
  (← Hax_lib.Prop.Constructors.from_bool
      (← Rust_primitives.Hax.Machine_int.lt
          i
          Tests.Legacy__attributes.Newtype_pattern.MAX))

structure Tests.Legacy__attributes.Newtype_pattern.SafeIndex where
  i : usize

def Tests.Legacy__attributes.Newtype_pattern.Impl.new
  (i : usize)
  : Result
  (Core.Option.Option Tests.Legacy__attributes.Newtype_pattern.SafeIndex)
  := do
  (← if
  (← Rust_primitives.Hax.Machine_int.lt
      i
      Tests.Legacy__attributes.Newtype_pattern.MAX) then do
    (Core.Option.Option.Some
      (Tests.Legacy__attributes.Newtype_pattern.SafeIndex.mk (i := i)))
  else do
    Core.Option.Option.None)

def Tests.Legacy__attributes.Newtype_pattern.Impl.as_usize
  (self : Tests.Legacy__attributes.Newtype_pattern.SafeIndex)
  : Result usize
  := do
  (Tests.Legacy__attributes.Newtype_pattern.SafeIndex.i self)

instance Tests.Legacy__attributes.Newtype_pattern.Impl_1 (T : Type) :
  Core.Ops.Index.Index
  (RustArray T (10 : usize))
  Tests.Legacy__attributes.Newtype_pattern.SafeIndex
  where
  Output := T
  index (self : (RustArray T (10 : usize)))
    (index : Tests.Legacy__attributes.Newtype_pattern.SafeIndex)
    := do
    (← Core.Ops.Index.Index.index
        self
        (Tests.Legacy__attributes.Newtype_pattern.SafeIndex.i index))

def
  Tests.Legacy__attributes.Nested_refinement_elim.Hax__autogenerated_refinement__DummyRefinement._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def
  Tests.Legacy__attributes.Nested_refinement_elim.Hax__autogenerated_refinement__DummyRefinement._.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : u16)
  : Result Bool
  := do
  true

abbrev Tests.Legacy__attributes.Nested_refinement_elim.Hax__autogenerated_refinement__DummyRefinement.DummyRefinement
:= u16

def Tests.Legacy__attributes.Nested_refinement_elim.elim_twice
  (x :
  Tests.Legacy__attributes.Nested_refinement_elim.Hax__autogenerated_refinement__DummyRefinement.DummyRefinement)
  : Result u16
  := do
  (← (← (← x : u16) :
  Tests.Legacy__attributes.Nested_refinement_elim.Hax__autogenerated_refinement__DummyRefinement.DummyRefinement)
  : u16)

structure Tests.Legacy__attributes.Issue_evit_57.Foo where


def Tests.Legacy__attributes.Issue_evit_57.Impl.f._.requires
  (self_ : Tests.Legacy__attributes.Issue_evit_57.Foo)
  : Result Bool
  := do
  true

def Tests.Legacy__attributes.Issue_evit_57.Impl.f
  (self : Tests.Legacy__attributes.Issue_evit_57.Foo)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__attributes.Issue_1276.S where
  _0 : u8

def Tests.Legacy__attributes.Issue_1276.Impl.f._.requires
  (self_3 : Tests.Legacy__attributes.Issue_1276.S)
  (self_ : u8)
  (self_0 : u8)
  (self_1 : u8)
  (self_2 : u8)
  : Result Bool
  := do
  (← (← (← Rust_primitives.Hax.Machine_int.eq
          (Tests.Legacy__attributes.Issue_1276.S._0 self_3)
          (0 : u8))
      &&? (← Rust_primitives.Hax.Machine_int.eq self_ self_1))
    &&? (← Rust_primitives.Hax.Machine_int.eq self_2 (9 : u8)))

def Tests.Legacy__attributes.Issue_1276.Impl.f
  (self : Tests.Legacy__attributes.Issue_1276.S)
  (self_ : u8)
  (self_0 : u8)
  (self_1 : u8)
  (self_2 : u8)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.Issue_1266._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Issue_1266._.ensures
  (Self_ : Type) (x : Self_)
  (x_future : Self_)
  : Result Bool
  := do
  true

class Tests.Legacy__attributes.Issue_1266.T (Self : Type) where
  v : Self -> Result Self

structure Tests.Legacy__attributes.Int_model.Int where
  _0 : u128

instance Tests.Legacy__attributes.Int_model.Impl_2 :
  Core.Clone.Clone Tests.Legacy__attributes.Int_model.Int
  where


instance Tests.Legacy__attributes.Int_model.Impl_1 :
  Core.Marker.Copy Tests.Legacy__attributes.Int_model.Int
  where


def Tests.Legacy__attributes.Int_model.add
  (x : Tests.Legacy__attributes.Int_model.Int)
  (y : Tests.Legacy__attributes.Int_model.Int)
  : Result Tests.Legacy__attributes.Int_model.Int
  := do
  (Tests.Legacy__attributes.Int_model.Int.mk
    (← (Tests.Legacy__attributes.Int_model.Int._0 x)
      +? (Tests.Legacy__attributes.Int_model.Int._0 y)))

instance Tests.Legacy__attributes.Int_model.Impl :
  Core.Ops.Arith.Sub
  Tests.Legacy__attributes.Int_model.Int
  Tests.Legacy__attributes.Int_model.Int
  where
  Output := Tests.Legacy__attributes.Int_model.Int
  sub (self : Tests.Legacy__attributes.Int_model.Int)
    (other : Tests.Legacy__attributes.Int_model.Int)
    := do
    (Tests.Legacy__attributes.Int_model.Int.mk
      (← (Tests.Legacy__attributes.Int_model.Int._0 self)
        +? (Tests.Legacy__attributes.Int_model.Int._0 other)))

def Tests.Legacy__attributes.Inlined_code_ensures_requires._.requires
  (v : (RustArray u8 (4 : usize)))
  : Result Hax_lib.Prop.Prop
  := do
  (← Hax_lib.Prop.Impl.from_bool true)

def Tests.Legacy__attributes.Inlined_code_ensures_requires.__1.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Inlined_code_ensures_requires.__1.ensures
  (v : (RustArray u8 (4 : usize)))
  (v_future : (RustArray u8 (4 : usize)))
  : Result Hax_lib.Prop.Prop
  := do
  let future_v : (RustArray u8 (4 : usize)) ← (pure v_future);
  (← Hax_lib.Prop.Impl.from_bool true)

def Tests.Legacy__attributes.Inlined_code_ensures_requires.increment_array
  (v : (RustArray u8 (4 : usize)))
  : Result (RustArray u8 (4 : usize))
  := do
  let v : (RustArray u8 (4 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        v
        (0 : usize)
        (← (← Core.Ops.Index.Index.index v (0 : usize)) +? (1 : u8))));
  let v : (RustArray u8 (4 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        v
        (1 : usize)
        (← (← Core.Ops.Index.Index.index v (1 : usize)) +? (1 : u8))));
  let v : (RustArray u8 (4 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        v
        (2 : usize)
        (← (← Core.Ops.Index.Index.index v (2 : usize)) +? (1 : u8))));
  let v : (RustArray u8 (4 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        v
        (3 : usize)
        (← (← Core.Ops.Index.Index.index v (3 : usize)) +? (1 : u8))));
  v

structure Tests.Legacy__attributes.Future_self.Dummy where


instance Tests.Legacy__attributes.Future_self.Impl_1 :
  Core.Marker.StructuralPartialEq Tests.Legacy__attributes.Future_self.Dummy
  where


instance Tests.Legacy__attributes.Future_self.Impl_2 :
  Core.Cmp.PartialEq
  Tests.Legacy__attributes.Future_self.Dummy
  Tests.Legacy__attributes.Future_self.Dummy
  where


instance Tests.Legacy__attributes.Future_self.Impl :
  Core.Cmp.Eq Tests.Legacy__attributes.Future_self.Dummy
  where


def Tests.Legacy__attributes.Future_self.Impl_3.f._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Future_self.Impl_3.f._.ensures
  (self_ : Tests.Legacy__attributes.Future_self.Dummy)
  (self__future : Tests.Legacy__attributes.Future_self.Dummy)
  : Result Bool
  := do
  (← Core.Cmp.PartialEq.eq self__future self_)

def Tests.Legacy__attributes.Future_self.Impl_3.f
  (self : Tests.Legacy__attributes.Future_self.Dummy)
  : Result Tests.Legacy__attributes.Future_self.Dummy
  := do
  self

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns._.requires
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  true

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns.__1.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns.__1.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (_x : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  true

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns.doing_nothing
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns.__2.requires
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  true

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns.__3.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns.__3.ensures
  (_ : Rust_primitives.Hax.Tuple0)
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.gt x (100 : u8))

def Tests.Legacy__attributes.Ensures_on_arity_zero_fns.basically_a_constant
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u8
  := do
  (127 : u8)

def Tests.Legacy__attributes.u32_max : u32 := 90000

def Tests.Legacy__attributes.__9.requires
  (x : u32)
  (y : u32)
  (z : u32)
  : Result Bool
  := do
  (← (← (← (← Rust_primitives.Hax.Machine_int.gt x (10 : u32))
        &&? (← Rust_primitives.Hax.Machine_int.gt y (10 : u32)))
      &&? (← Rust_primitives.Hax.Machine_int.gt z (10 : u32)))
    &&? (← Rust_primitives.Hax.Machine_int.lt
        (← (← x +? y) +? z)
        Tests.Legacy__attributes.u32_max))

def Tests.Legacy__attributes.__10.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.__10.ensures
  (x : u32)
  (y : u32)
  (z : u32)
  (result : u32)
  : Result Hax_lib.Prop.Prop
  := do
  (← Hax_lib.Prop.Constructors.implies
      (← Hax_lib.Prop.Constructors.from_bool true)
      (← Hax_lib.Prop.Constructors.from_bool
          (← Rust_primitives.Hax.Machine_int.gt result (32 : u32))))

def Tests.Legacy__attributes.add3
  (x : u32)
  (y : u32)
  (z : u32)
  : Result u32
  := do
  (← (← x +? y) +? z)

def Tests.Legacy__attributes.__7.requires
  (x : u32)
  (y : u32)
  : Result Bool
  := do
  (← (← Rust_primitives.Hax.Machine_int.lt x (40 : u32))
    &&? (← Rust_primitives.Hax.Machine_int.lt y (300 : u32)))

def Tests.Legacy__attributes.__8.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.__8.ensures
  (x : u32)
  (y : u32)
  (⟨x_future, y_future, result⟩ : (Rust_primitives.Hax.Tuple3 u32 u32 u32))
  : Result Bool
  := do
  (← (← (← Rust_primitives.Hax.Machine_int.eq x_future y)
      &&? (← Rust_primitives.Hax.Machine_int.eq y_future x))
    &&? (← Rust_primitives.Hax.Machine_int.eq result (← x +? y)))

def Tests.Legacy__attributes.swap_and_mut_req_ens
  (x : u32)
  (y : u32)
  : Result (Rust_primitives.Hax.Tuple3 u32 u32 u32)
  := do
  let x0 : u32 ← (pure x);
  let x : u32 ← (pure y);
  let y : u32 ← (pure x0);
  let hax_temp_output : u32 ← (pure (← x +? y));
  (Rust_primitives.Hax.Tuple3.mk x y hax_temp_output)

def Tests.Legacy__attributes._.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes._.ensures
  (_x : u8)
  (_x_future : u8)
  : Result Bool
  := do
  true

def Tests.Legacy__attributes.issue_844 (_x : u8) : Result u8 := do _x

def Tests.Legacy__attributes.__6.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.__6.ensures
  (x : u32)
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  (← (← (← Rust_primitives.Hax.Machine_int.le x (10 : u32))
      ||? (← Rust_primitives.Hax.Machine_int.ge
          x
          (← Tests.Legacy__attributes.u32_max /? (3 : u32))))
    ||? (← Rust_primitives.Hax.Machine_int.eq
        (← Tests.Legacy__attributes.add3 x x x)
        (← x *? (3 : u32))))

def Tests.Legacy__attributes.add3_lemma
  (x : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.dummy_function (x : u32) : Result u32 := do x

def Tests.Legacy__attributes.__4.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__attributes.__4.ensures
  (x : u32)
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.eq
      x
      (← Tests.Legacy__attributes.dummy_function x))

def Tests.Legacy__attributes.__5.SMTPat
  (x : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Hax_lib.any_to_unit u32 x)

def Tests.Legacy__attributes.apply_dummy_function_lemma
  (x : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.__3.decreases
  (x : usize)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Hax_lib.any_to_unit usize x)

def Tests.Legacy__attributes.__1.refinement
  (x : u32)
  (y : u32)
  : Result Hax_lib.Prop.Prop
  := do
  (← Hax_lib.Prop.Constructors.from_bool
      (← Rust_primitives.Hax.Machine_int.gt y (3 : u32)))

def Tests.Legacy__attributes.__2.refinement
  (x : u32)
  (y : u32)
  (z : u32)
  : Result Hax_lib.Prop.Prop
  := do
  (← Hax_lib.Prop.Constructors.from_bool
      (← Rust_primitives.Hax.Machine_int.gt (← (← y +? x) +? z) (3 : u32)))

structure Tests.Legacy__attributes.Foo where
  x : u32
  y : u32
  z : u32

def Tests.Legacy__attributes.props
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Hax_lib.assume (← Hax_lib.Prop.Impl.from_bool true)));
  let _ ← (pure (← Hax_lib.assert_prop (← Hax_lib.Prop.Impl.from_bool true)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.inlined_code
  (foo : Tests.Legacy__attributes.Foo)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let v_a : i32 ← (pure (13 : i32));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.inlined_code.V : u8 := 12

def Tests.Legacy__attributes.mutliple_before_after
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.some_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Alloc.String.String
  := do
  (← Core.Convert.From.from "hello from Rust")

def Tests.Legacy__attributes.fib (x : usize) : Result usize := do
  (← if (← Rust_primitives.Hax.Machine_int.le x (2 : usize)) then do
    x
  else do
    (← Core.Num.Impl_11.wrapping_add
        (← Tests.Legacy__attributes.fib (← x -? (1 : usize)))
        (← Tests.Legacy__attributes.fib (← x -? (2 : usize)))))

def Tests.Legacy__attributes.Props.f
  (x : Hax_lib.Prop.Prop)
  (y : Bool)
  : Result Hax_lib.Prop.Prop
  := do
  let xprop ← (pure (← Hax_lib.Prop.Constructors.from_bool y));
  let p : Hax_lib.Prop.Prop ← (pure
    (← Hax_lib.Prop.Constructors.and
        (← Hax_lib.Prop.Constructors.and
            (← Hax_lib.Prop.Constructors.and
                (← Hax_lib.Prop.Constructors.from_bool y)
                xprop)
            (← Hax_lib.Prop.Constructors.from_bool y))
        (← Hax_lib.Prop.Constructors.from_bool y)));
  (← Hax_lib.Prop.Constructors.not
      (← Hax_lib.Prop.Constructors.implies
          (← Hax_lib.Prop.Constructors.or
              p
              (← Hax_lib.Prop.Constructors.from_bool y))
          (← Hax_lib.Prop.Constructors.and
              (← Hax_lib.Prop.Constructors.forall
                  (fun x => (do
                      (← Hax_lib.Prop.Constructors.from_bool
                          (← Rust_primitives.Hax.Machine_int.le
                              x
                              Core.Num.Impl_6.MAX)) : Result
                      Hax_lib.Prop.Prop)))
              (← Hax_lib.Prop.Constructors.exists
                  (fun x => (do
                      (← Hax_lib.Prop.Constructors.from_bool
                          (← Rust_primitives.Hax.Machine_int.gt x (300 : u16)))
                      : Result Hax_lib.Prop.Prop))))))

def Tests.Legacy__attributes.Postprocess_with.Somewhere.some_hypothetical_tactic
  (some_param : u8)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.Postprocess_with.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__attributes.Postprocess_with.g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk