
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax.Core
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

structure Core_models.Array.TryFromSliceError where


def Core_models.Array.Impl_23.as_slice
  (T : Type) (N : usize) (s : (RustArray T N))
  : RustM (RustSlice T)
  := do
  (Rust_primitives.Slice.array_as_slice T (N) s)

structure Core_models.Array.Iter.IntoIter (T : Type) (N : usize) where
  _0 : (Rust_primitives.Sequence.Seq T)

class Core_models.Borrow.Borrow.AssociatedTypes (Self : Type) (Borrowed : Type)
  where

class Core_models.Borrow.Borrow
  (Self : Type)
  (Borrowed : Type)
  [associatedTypes : outParam (Core_models.Borrow.Borrow.AssociatedTypes (Self :
      Type) (Borrowed : Type))]
  where
  borrow (Self Borrowed) : (Self -> RustM Borrowed)

class Core_models.Clone.Clone.AssociatedTypes (Self : Type) where

class Core_models.Clone.Clone
  (Self : Type)
  [associatedTypes : outParam (Core_models.Clone.Clone.AssociatedTypes (Self :
      Type))]
  where
  clone (Self) : (Self -> RustM Self)

@[reducible] instance Core_models.Clone.Impl.AssociatedTypes (T : Type) :
  Core_models.Clone.Clone.AssociatedTypes T
  where

instance Core_models.Clone.Impl (T : Type) : Core_models.Clone.Clone T where
  clone := fun (self : T) => do (pure self)

class Core_models.Cmp.PartialEq.AssociatedTypes (Self : Type) (Rhs : Type) where

class Core_models.Cmp.PartialEq
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Cmp.PartialEq.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  eq (Self Rhs) : (Self -> Rhs -> RustM Bool)

class Core_models.Cmp.Eq.AssociatedTypes (Self : Type) where
  [trait_constr_Eq_i0 : Core_models.Cmp.PartialEq.AssociatedTypes Self Self]

attribute [instance] Core_models.Cmp.Eq.AssociatedTypes.trait_constr_Eq_i0

class Core_models.Cmp.Eq
  (Self : Type)
  [associatedTypes : outParam (Core_models.Cmp.Eq.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_Eq_i0 : Core_models.Cmp.PartialEq Self Self]

attribute [instance] Core_models.Cmp.Eq.trait_constr_Eq_i0

inductive Core_models.Cmp.Ordering : Type
| Less : Core_models.Cmp.Ordering
| Equal : Core_models.Cmp.Ordering
| Greater : Core_models.Cmp.Ordering


def Core_models.Cmp.Ordering.Less.AnonConst : isize :=
  RustM.of_isOk (do (pure (-1 : isize))) (by rfl)

def Core_models.Cmp.Ordering.Equal.AnonConst : isize :=
  RustM.of_isOk (do (pure (0 : isize))) (by rfl)

def Core_models.Cmp.Ordering.Greater.AnonConst : isize :=
  RustM.of_isOk (do (pure (1 : isize))) (by rfl)

def Core_models.Cmp.Ordering_ (x : Core_models.Cmp.Ordering) : RustM isize := do
  match x with
    | (Core_models.Cmp.Ordering.Less )
      => (pure Core_models.Cmp.Ordering.Less.AnonConst)
    | (Core_models.Cmp.Ordering.Equal )
      => (pure Core_models.Cmp.Ordering.Equal.AnonConst)
    | (Core_models.Cmp.Ordering.Greater )
      => (pure Core_models.Cmp.Ordering.Greater.AnonConst)

class Core_models.Cmp.Neq.AssociatedTypes (Self : Type) (Rhs : Type) where

class Core_models.Cmp.Neq
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Cmp.Neq.AssociatedTypes (Self : Type)
      (Rhs : Type))]
  where
  neq (Self Rhs) : (Self -> Rhs -> RustM Bool)

@[reducible] instance Core_models.Cmp.Impl.AssociatedTypes
  (T : Type)
  [Core_models.Cmp.PartialEq.AssociatedTypes T T]
  [Core_models.Cmp.PartialEq T T ]
  :
  Core_models.Cmp.Neq.AssociatedTypes T T
  where

instance Core_models.Cmp.Impl
  (T : Type)
  [Core_models.Cmp.PartialEq.AssociatedTypes T T]
  [Core_models.Cmp.PartialEq T T ]
  :
  Core_models.Cmp.Neq T T
  where
  neq := fun (self : T) (y : T) => do
    (Core.Cmp.PartialEq.eq (← (Core_models.Cmp.PartialEq.eq T T self y)) false)

structure Core_models.Cmp.Reverse (T : Type) where
  _0 : T

@[reducible] instance Core_models.Cmp.Impl_3.AssociatedTypes
  (T : Type)
  [Core_models.Cmp.PartialEq.AssociatedTypes T T]
  [Core_models.Cmp.PartialEq T T ]
  :
  Core_models.Cmp.PartialEq.AssociatedTypes
  (Core_models.Cmp.Reverse T)
  (Core_models.Cmp.Reverse T)
  where

instance Core_models.Cmp.Impl_3
  (T : Type)
  [Core_models.Cmp.PartialEq.AssociatedTypes T T]
  [Core_models.Cmp.PartialEq T T ]
  :
  Core_models.Cmp.PartialEq
  (Core_models.Cmp.Reverse T)
  (Core_models.Cmp.Reverse T)
  where
  eq :=
    fun
      (self : (Core_models.Cmp.Reverse T))
      (other : (Core_models.Cmp.Reverse T))
      => do
    (Core_models.Cmp.PartialEq.eq
      T
      T (Core_models.Cmp.Reverse._0 other) (Core_models.Cmp.Reverse._0 self))

@[reducible] instance Core_models.Cmp.Impl_4.AssociatedTypes
  (T : Type) [Core_models.Cmp.Eq.AssociatedTypes T] [Core_models.Cmp.Eq T ] :
  Core_models.Cmp.Eq.AssociatedTypes (Core_models.Cmp.Reverse T)
  where

instance Core_models.Cmp.Impl_4
  (T : Type) [Core_models.Cmp.Eq.AssociatedTypes T] [Core_models.Cmp.Eq T ] :
  Core_models.Cmp.Eq (Core_models.Cmp.Reverse T)
  where

@[reducible] instance Core_models.Cmp.Impl_6.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes u8 u8
  where

instance Core_models.Cmp.Impl_6 : Core_models.Cmp.PartialEq u8 u8 where
  eq := fun (self : u8) (other : u8) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_7.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes u8
  where

instance Core_models.Cmp.Impl_7 : Core_models.Cmp.Eq u8 where

@[reducible] instance Core_models.Cmp.Impl_8.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes i8 i8
  where

instance Core_models.Cmp.Impl_8 : Core_models.Cmp.PartialEq i8 i8 where
  eq := fun (self : i8) (other : i8) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_9.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes i8
  where

instance Core_models.Cmp.Impl_9 : Core_models.Cmp.Eq i8 where

@[reducible] instance Core_models.Cmp.Impl_10.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes u16 u16
  where

instance Core_models.Cmp.Impl_10 : Core_models.Cmp.PartialEq u16 u16 where
  eq := fun (self : u16) (other : u16) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_11.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes u16
  where

instance Core_models.Cmp.Impl_11 : Core_models.Cmp.Eq u16 where

@[reducible] instance Core_models.Cmp.Impl_12.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes i16 i16
  where

instance Core_models.Cmp.Impl_12 : Core_models.Cmp.PartialEq i16 i16 where
  eq := fun (self : i16) (other : i16) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_13.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes i16
  where

instance Core_models.Cmp.Impl_13 : Core_models.Cmp.Eq i16 where

@[reducible] instance Core_models.Cmp.Impl_14.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes u32 u32
  where

instance Core_models.Cmp.Impl_14 : Core_models.Cmp.PartialEq u32 u32 where
  eq := fun (self : u32) (other : u32) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_15.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes u32
  where

instance Core_models.Cmp.Impl_15 : Core_models.Cmp.Eq u32 where

@[reducible] instance Core_models.Cmp.Impl_16.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes i32 i32
  where

instance Core_models.Cmp.Impl_16 : Core_models.Cmp.PartialEq i32 i32 where
  eq := fun (self : i32) (other : i32) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_17.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes i32
  where

instance Core_models.Cmp.Impl_17 : Core_models.Cmp.Eq i32 where

@[reducible] instance Core_models.Cmp.Impl_18.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes u64 u64
  where

instance Core_models.Cmp.Impl_18 : Core_models.Cmp.PartialEq u64 u64 where
  eq := fun (self : u64) (other : u64) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_19.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes u64
  where

instance Core_models.Cmp.Impl_19 : Core_models.Cmp.Eq u64 where

@[reducible] instance Core_models.Cmp.Impl_20.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes i64 i64
  where

instance Core_models.Cmp.Impl_20 : Core_models.Cmp.PartialEq i64 i64 where
  eq := fun (self : i64) (other : i64) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_21.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes i64
  where

instance Core_models.Cmp.Impl_21 : Core_models.Cmp.Eq i64 where

@[reducible] instance Core_models.Cmp.Impl_22.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes u128 u128
  where

instance Core_models.Cmp.Impl_22 : Core_models.Cmp.PartialEq u128 u128 where
  eq := fun (self : u128) (other : u128) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_23.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes u128
  where

instance Core_models.Cmp.Impl_23 : Core_models.Cmp.Eq u128 where

@[reducible] instance Core_models.Cmp.Impl_24.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes i128 i128
  where

instance Core_models.Cmp.Impl_24 : Core_models.Cmp.PartialEq i128 i128 where
  eq := fun (self : i128) (other : i128) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_25.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes i128
  where

instance Core_models.Cmp.Impl_25 : Core_models.Cmp.Eq i128 where

@[reducible] instance Core_models.Cmp.Impl_26.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes usize usize
  where

instance Core_models.Cmp.Impl_26 : Core_models.Cmp.PartialEq usize usize where
  eq := fun (self : usize) (other : usize) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_27.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes usize
  where

instance Core_models.Cmp.Impl_27 : Core_models.Cmp.Eq usize where

@[reducible] instance Core_models.Cmp.Impl_28.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes isize isize
  where

instance Core_models.Cmp.Impl_28 : Core_models.Cmp.PartialEq isize isize where
  eq := fun (self : isize) (other : isize) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Core_models.Cmp.Impl_29.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes isize
  where

instance Core_models.Cmp.Impl_29 : Core_models.Cmp.Eq isize where

class Core_models.Convert.Into.AssociatedTypes (Self : Type) (T : Type) where

class Core_models.Convert.Into
  (Self : Type)
  (T : Type)
  [associatedTypes : outParam (Core_models.Convert.Into.AssociatedTypes (Self :
      Type) (T : Type))]
  where
  into (Self T) : (Self -> RustM T)

class Core_models.Convert.From.AssociatedTypes (Self : Type) (T : Type) where

class Core_models.Convert.From
  (Self : Type)
  (T : Type)
  [associatedTypes : outParam (Core_models.Convert.From.AssociatedTypes (Self :
      Type) (T : Type))]
  where
  __from (Self T) : (T -> RustM Self)

@[reducible] instance Core_models.Convert.Impl.AssociatedTypes
  (T : Type)
  (U : Type)
  [Core_models.Convert.From.AssociatedTypes U T] [Core_models.Convert.From U T ]
  :
  Core_models.Convert.Into.AssociatedTypes T U
  where

instance Core_models.Convert.Impl
  (T : Type)
  (U : Type)
  [Core_models.Convert.From.AssociatedTypes U T] [Core_models.Convert.From U T ]
  :
  Core_models.Convert.Into T U
  where
  into := fun (self : T) => do (Core_models.Convert.From.__from U T self)

structure Core_models.Convert.Infallible where


@[reducible] instance Core_models.Convert.Impl_4.AssociatedTypes (T : Type) :
  Core_models.Convert.From.AssociatedTypes T T
  where

instance Core_models.Convert.Impl_4 (T : Type) :
  Core_models.Convert.From T T
  where
  __from := fun (x : T) => do (pure x)

class Core_models.Convert.AsRef.AssociatedTypes (Self : Type) (T : Type) where

class Core_models.Convert.AsRef
  (Self : Type)
  (T : Type)
  [associatedTypes : outParam (Core_models.Convert.AsRef.AssociatedTypes (Self :
      Type) (T : Type))]
  where
  as_ref (Self T) : (Self -> RustM T)

@[reducible] instance Core_models.Convert.Impl_5.AssociatedTypes (T : Type) :
  Core_models.Convert.AsRef.AssociatedTypes T T
  where

instance Core_models.Convert.Impl_5 (T : Type) :
  Core_models.Convert.AsRef T T
  where
  as_ref := fun (self : T) => do (pure self)

@[reducible] instance Core_models.Convert.Impl_6.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u16 u8
  where

instance Core_models.Convert.Impl_6 : Core_models.Convert.From u16 u8 where
  __from := fun (x : u8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_7.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u32 u8
  where

instance Core_models.Convert.Impl_7 : Core_models.Convert.From u32 u8 where
  __from := fun (x : u8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_8.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u32 u16
  where

instance Core_models.Convert.Impl_8 : Core_models.Convert.From u32 u16 where
  __from := fun (x : u16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_9.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u64 u8
  where

instance Core_models.Convert.Impl_9 : Core_models.Convert.From u64 u8 where
  __from := fun (x : u8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_10.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u64 u16
  where

instance Core_models.Convert.Impl_10 : Core_models.Convert.From u64 u16 where
  __from := fun (x : u16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_11.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u64 u32
  where

instance Core_models.Convert.Impl_11 : Core_models.Convert.From u64 u32 where
  __from := fun (x : u32) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_12.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u64 usize
  where

instance Core_models.Convert.Impl_12 : Core_models.Convert.From u64 usize where
  __from := fun (x : usize) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_13.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u128 u8
  where

instance Core_models.Convert.Impl_13 : Core_models.Convert.From u128 u8 where
  __from := fun (x : u8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_14.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u128 u16
  where

instance Core_models.Convert.Impl_14 : Core_models.Convert.From u128 u16 where
  __from := fun (x : u16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_15.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u128 u32
  where

instance Core_models.Convert.Impl_15 : Core_models.Convert.From u128 u32 where
  __from := fun (x : u32) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_16.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u128 u64
  where

instance Core_models.Convert.Impl_16 : Core_models.Convert.From u128 u64 where
  __from := fun (x : u64) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_17.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u128 usize
  where

instance Core_models.Convert.Impl_17 : Core_models.Convert.From u128 usize where
  __from := fun (x : usize) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_18.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes usize u8
  where

instance Core_models.Convert.Impl_18 : Core_models.Convert.From usize u8 where
  __from := fun (x : u8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_19.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes usize u16
  where

instance Core_models.Convert.Impl_19 : Core_models.Convert.From usize u16 where
  __from := fun (x : u16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_20.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes usize u32
  where

instance Core_models.Convert.Impl_20 : Core_models.Convert.From usize u32 where
  __from := fun (x : u32) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_21.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i16 i8
  where

instance Core_models.Convert.Impl_21 : Core_models.Convert.From i16 i8 where
  __from := fun (x : i8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_22.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i32 i8
  where

instance Core_models.Convert.Impl_22 : Core_models.Convert.From i32 i8 where
  __from := fun (x : i8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_23.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i32 i16
  where

instance Core_models.Convert.Impl_23 : Core_models.Convert.From i32 i16 where
  __from := fun (x : i16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_24.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i64 i8
  where

instance Core_models.Convert.Impl_24 : Core_models.Convert.From i64 i8 where
  __from := fun (x : i8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_25.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i64 i16
  where

instance Core_models.Convert.Impl_25 : Core_models.Convert.From i64 i16 where
  __from := fun (x : i16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_26.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i64 i32
  where

instance Core_models.Convert.Impl_26 : Core_models.Convert.From i64 i32 where
  __from := fun (x : i32) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_27.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i64 isize
  where

instance Core_models.Convert.Impl_27 : Core_models.Convert.From i64 isize where
  __from := fun (x : isize) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_28.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i128 i8
  where

instance Core_models.Convert.Impl_28 : Core_models.Convert.From i128 i8 where
  __from := fun (x : i8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_29.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i128 i16
  where

instance Core_models.Convert.Impl_29 : Core_models.Convert.From i128 i16 where
  __from := fun (x : i16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_30.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i128 i32
  where

instance Core_models.Convert.Impl_30 : Core_models.Convert.From i128 i32 where
  __from := fun (x : i32) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_31.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i128 i64
  where

instance Core_models.Convert.Impl_31 : Core_models.Convert.From i128 i64 where
  __from := fun (x : i64) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_32.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i128 isize
  where

instance Core_models.Convert.Impl_32 : Core_models.Convert.From i128 isize where
  __from := fun (x : isize) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_33.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes isize i8
  where

instance Core_models.Convert.Impl_33 : Core_models.Convert.From isize i8 where
  __from := fun (x : i8) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_34.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes isize i16
  where

instance Core_models.Convert.Impl_34 : Core_models.Convert.From isize i16 where
  __from := fun (x : i16) => do (Rust_primitives.Hax.cast_op x)

@[reducible] instance Core_models.Convert.Impl_35.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes isize i32
  where

instance Core_models.Convert.Impl_35 : Core_models.Convert.From isize i32 where
  __from := fun (x : i32) => do (Rust_primitives.Hax.cast_op x)

class Core_models.Default.Default.AssociatedTypes (Self : Type) where

class Core_models.Default.Default
  (Self : Type)
  [associatedTypes : outParam (Core_models.Default.Default.AssociatedTypes (Self
      : Type))]
  where
  default (Self) : (Rust_primitives.Hax.Tuple0 -> RustM Self)

opaque Core_models.F32.Impl.abs (x : f64) : RustM f64 

structure Core_models.Fmt.Error where


structure Core_models.Fmt.Formatter where


structure Core_models.Fmt.Arguments where
  _0 : Rust_primitives.Hax.Tuple0

inductive Core_models.Fmt.Rt.ArgumentType : Type


structure Core_models.Fmt.Rt.Argument where
  ty : Core_models.Fmt.Rt.ArgumentType

opaque Core_models.Fmt.Rt.Impl.new_display
  (T : Type) (x : T)
  : RustM Core_models.Fmt.Rt.Argument


opaque Core_models.Fmt.Rt.Impl.new_debug
  (T : Type) (x : T)
  : RustM Core_models.Fmt.Rt.Argument


opaque Core_models.Fmt.Rt.Impl.new_lower_hex
  (T : Type) (x : T)
  : RustM Core_models.Fmt.Rt.Argument


opaque Core_models.Fmt.Rt.Impl_1.new_binary
  (T : Type) (x : T)
  : RustM Core_models.Fmt.Rt.Argument


opaque Core_models.Fmt.Rt.Impl_1.new_const
  (T : Type) (U : Type) (x : T)
  (y : U)
  : RustM Core_models.Fmt.Arguments


opaque Core_models.Fmt.Rt.Impl_1.new_v1
  (T : Type) (U : Type) (V : Type) (W : Type) (x : T)
  (y : U)
  (z : V)
  (t : W)
  : RustM Core_models.Fmt.Arguments


def Core_models.Fmt.Rt.Impl_1.none
  (_ : Rust_primitives.Hax.Tuple0)
  : RustM (RustArray Core_models.Fmt.Rt.Argument 0)
  := do
  (pure #v[])

opaque Core_models.Fmt.Rt.Impl_1.new_v1_formatted
  (T : Type) (U : Type) (V : Type) (x : T)
  (y : U)
  (z : V)
  : RustM Core_models.Fmt.Arguments


inductive Core_models.Fmt.Rt.Count : Type
| Is : u16 -> Core_models.Fmt.Rt.Count
| Param : u16 -> Core_models.Fmt.Rt.Count
| Implied : Core_models.Fmt.Rt.Count


structure Core_models.Fmt.Rt.Placeholder where
  position : usize
  flags : u32
  precision : Core_models.Fmt.Rt.Count
  width : Core_models.Fmt.Rt.Count

structure Core_models.Fmt.Rt.UnsafeArg where


class Core_models.Hash.Hasher.AssociatedTypes (Self : Type) where

class Core_models.Hash.Hasher
  (Self : Type)
  [associatedTypes : outParam (Core_models.Hash.Hasher.AssociatedTypes (Self :
      Type))]
  where

class Core_models.Hash.Hash.AssociatedTypes (Self : Type) where

class Core_models.Hash.Hash
  (Self : Type)
  [associatedTypes : outParam (Core_models.Hash.Hash.AssociatedTypes (Self :
      Type))]
  where
  hash (Self)
    (H : Type)
    [Core_models.Hash.Hasher.AssociatedTypes H] [Core_models.Hash.Hasher H ]
    :
    (Self -> H -> RustM H)

def Core_models.Hint.black_box (T : Type) (dummy : T) : RustM T := do
  (pure dummy)

@[spec]
def Core_models.Hint.black_box.spec (T : Type) (dummy : T)  :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (Hax_lib.Prop.Impl.from_bool true))
      (Core_models.Hint.black_box (T : Type) (dummy : T) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Hint.black_box] <;> try grind
}

def Core_models.Hint.must_use (T : Type) (value : T) : RustM T := do
  (pure value)

@[spec]
def Core_models.Hint.must_use.spec (T : Type) (value : T)  :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (Hax_lib.Prop.Impl.from_bool true))
      (Core_models.Hint.must_use (T : Type) (value : T) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Hint.must_use] <;> try grind
}

structure Core_models.Iter.Adapters.Enumerate.Enumerate (I : Type) where
  iter : I
  count : usize

def Core_models.Iter.Adapters.Enumerate.Impl.new
  (I : Type) (iter : I)
  : RustM (Core_models.Iter.Adapters.Enumerate.Enumerate I)
  := do
  (pure (Core_models.Iter.Adapters.Enumerate.Enumerate.mk
    (iter := iter) (count := (0 : usize))))

structure Core_models.Iter.Adapters.Step_by.StepBy (I : Type) where
  iter : I
  step : usize

def Core_models.Iter.Adapters.Step_by.Impl.new
  (I : Type) (iter : I)
  (step : usize)
  : RustM (Core_models.Iter.Adapters.Step_by.StepBy I)
  := do
  (pure (Core_models.Iter.Adapters.Step_by.StepBy.mk
    (iter := iter) (step := step)))

structure Core_models.Iter.Adapters.Map.Map (I : Type) (F : Type) where
  iter : I
  f : F

def Core_models.Iter.Adapters.Map.Impl.new
  (I : Type) (F : Type) (iter : I)
  (f : F)
  : RustM (Core_models.Iter.Adapters.Map.Map I F)
  := do
  (pure (Core_models.Iter.Adapters.Map.Map.mk (iter := iter) (f := f)))

structure Core_models.Iter.Adapters.Take.Take (I : Type) where
  iter : I
  n : usize

def Core_models.Iter.Adapters.Take.Impl.new
  (I : Type) (iter : I)
  (n : usize)
  : RustM (Core_models.Iter.Adapters.Take.Take I)
  := do
  (pure (Core_models.Iter.Adapters.Take.Take.mk (iter := iter) (n := n)))

structure Core_models.Iter.Adapters.Zip.Zip (I1 : Type) (I2 : Type) where
  it1 : I1
  it2 : I2

class Core_models.Marker.Copy.AssociatedTypes (Self : Type) where
  [trait_constr_Copy_i0 : Core_models.Clone.Clone.AssociatedTypes Self]

attribute [instance]
  Core_models.Marker.Copy.AssociatedTypes.trait_constr_Copy_i0

class Core_models.Marker.Copy
  (Self : Type)
  [associatedTypes : outParam (Core_models.Marker.Copy.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_Copy_i0 : Core_models.Clone.Clone Self]

attribute [instance] Core_models.Marker.Copy.trait_constr_Copy_i0

class Core_models.Marker.Send.AssociatedTypes (Self : Type) where

class Core_models.Marker.Send
  (Self : Type)
  [associatedTypes : outParam (Core_models.Marker.Send.AssociatedTypes (Self :
      Type))]
  where

class Core_models.Marker.Sync.AssociatedTypes (Self : Type) where

class Core_models.Marker.Sync
  (Self : Type)
  [associatedTypes : outParam (Core_models.Marker.Sync.AssociatedTypes (Self :
      Type))]
  where

class Core_models.Marker.Sized.AssociatedTypes (Self : Type) where

class Core_models.Marker.Sized
  (Self : Type)
  [associatedTypes : outParam (Core_models.Marker.Sized.AssociatedTypes (Self :
      Type))]
  where

class Core_models.Marker.StructuralPartialEq.AssociatedTypes (Self : Type) where

class Core_models.Marker.StructuralPartialEq
  (Self : Type)
  [associatedTypes : outParam
    (Core_models.Marker.StructuralPartialEq.AssociatedTypes (Self : Type))]
  where

@[reducible] instance Core_models.Marker.Impl.AssociatedTypes (T : Type) :
  Core_models.Marker.Send.AssociatedTypes T
  where

instance Core_models.Marker.Impl (T : Type) : Core_models.Marker.Send T where

@[reducible] instance Core_models.Marker.Impl_1.AssociatedTypes (T : Type) :
  Core_models.Marker.Sync.AssociatedTypes T
  where

instance Core_models.Marker.Impl_1 (T : Type) : Core_models.Marker.Sync T where

@[reducible] instance Core_models.Marker.Impl_2.AssociatedTypes (T : Type) :
  Core_models.Marker.Sized.AssociatedTypes T
  where

instance Core_models.Marker.Impl_2 (T : Type) : Core_models.Marker.Sized T where

@[reducible] instance Core_models.Marker.Impl_3.AssociatedTypes
  (T : Type)
  [Core_models.Clone.Clone.AssociatedTypes T] [Core_models.Clone.Clone T ]
  :
  Core_models.Marker.Copy.AssociatedTypes T
  where

instance Core_models.Marker.Impl_3
  (T : Type)
  [Core_models.Clone.Clone.AssociatedTypes T] [Core_models.Clone.Clone T ]
  :
  Core_models.Marker.Copy T
  where

structure Core_models.Marker.PhantomData (T : Type) where
  _0 : T

opaque Core_models.Mem.forget
  (T : Type) (t : T)
  : RustM Rust_primitives.Hax.Tuple0


opaque Core_models.Mem.forget_unsized
  (T : Type) (t : T)
  : RustM Rust_primitives.Hax.Tuple0


opaque Core_models.Mem.size_of
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM usize


opaque Core_models.Mem.size_of_val (T : Type) (val : T) : RustM usize 

opaque Core_models.Mem.min_align_of
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM usize


opaque Core_models.Mem.min_align_of_val (T : Type) (val : T) : RustM usize 

opaque Core_models.Mem.align_of
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM usize


opaque Core_models.Mem.align_of_val (T : Type) (val : T) : RustM usize 

opaque Core_models.Mem.align_of_val_raw (T : Type) (val : T) : RustM usize 

opaque Core_models.Mem.needs_drop
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM Bool


opaque Core_models.Mem.uninitialized
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM T


opaque Core_models.Mem.swap
  (T : Type) (x : T)
  (y : T)
  : RustM (Rust_primitives.Hax.Tuple2 T T)


opaque Core_models.Mem.replace
  (T : Type) (dest : T)
  (src : T)
  : RustM (Rust_primitives.Hax.Tuple2 T T)


opaque Core_models.Mem.drop
  (T : Type) (_x : T)
  : RustM Rust_primitives.Hax.Tuple0


def Core_models.Mem.copy
  (T : Type)
  [Core_models.Marker.Copy.AssociatedTypes T] [Core_models.Marker.Copy T ]
  (x : T)
  : RustM T
  := do
  (Rust_primitives.Mem.copy T x)

opaque Core_models.Mem.take
  (T : Type) (x : T)
  : RustM (Rust_primitives.Hax.Tuple2 T T)


opaque Core_models.Mem.transmute_copy
  (Src : Type) (Dst : Type) (src : Src)
  : RustM Dst


opaque Core_models.Mem.variant_count
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM usize


opaque Core_models.Mem.zeroed
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM T


opaque Core_models.Mem.transmute
  (Src : Type) (Dst : Type) (src : Src)
  : RustM Dst


structure Core_models.Mem.Manually_drop.ManuallyDrop (T : Type) where
  value : T

structure Core_models.Num.Error.TryFromIntError where
  _0 : Rust_primitives.Hax.Tuple0

structure Core_models.Num.Error.IntErrorKind where


structure Core_models.Num.Error.ParseIntError where
  kind : Core_models.Num.Error.IntErrorKind

def Core_models.Num.Impl_1.MIN : u8 :=
  RustM.of_isOk (do (pure (0 : u8))) (by rfl)

def Core_models.Num.Impl_1.MAX : u8 :=
  RustM.of_isOk (do (pure (255 : u8))) (by rfl)

def Core_models.Num.Impl_1.BITS : u32 :=
  RustM.of_isOk (do (pure (8 : u32))) (by rfl)

def Core_models.Num.Impl_1.wrapping_add (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.wrapping_add_u8 x y)

def Core_models.Num.Impl_1.saturating_add (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.saturating_add_u8 x y)

def Core_models.Num.Impl_1.overflowing_add
  (x : u8)
  (y : u8)
  : RustM (Rust_primitives.Hax.Tuple2 u8 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_u8 x y)

def Core_models.Num.Impl_1.wrapping_sub (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u8 x y)

def Core_models.Num.Impl_1.saturating_sub (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.saturating_sub_u8 x y)

def Core_models.Num.Impl_1.overflowing_sub
  (x : u8)
  (y : u8)
  : RustM (Rust_primitives.Hax.Tuple2 u8 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_u8 x y)

def Core_models.Num.Impl_1.wrapping_mul (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u8 x y)

def Core_models.Num.Impl_1.saturating_mul (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.saturating_mul_u8 x y)

def Core_models.Num.Impl_1.overflowing_mul
  (x : u8)
  (y : u8)
  : RustM (Rust_primitives.Hax.Tuple2 u8 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_u8 x y)

def Core_models.Num.Impl_1.pow (x : u8) (exp : u32) : RustM u8 := do
  (Rust_primitives.Arithmetic.pow_u8 x exp)

def Core_models.Num.Impl_1.count_ones (x : u8) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_u8 x)

opaque Core_models.Num.Impl_1.rotate_right (x : u8) (n : u32) : RustM u8 

opaque Core_models.Num.Impl_1.rotate_left (x : u8) (n : u32) : RustM u8 

opaque Core_models.Num.Impl_1.leading_zeros (x : u8) : RustM u32 

opaque Core_models.Num.Impl_1.ilog2 (x : u8) : RustM u32 

opaque Core_models.Num.Impl_1.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result u8 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_1.from_be_bytes
  (bytes : (RustArray u8 1))
  : RustM u8


opaque Core_models.Num.Impl_1.from_le_bytes
  (bytes : (RustArray u8 1))
  : RustM u8


opaque Core_models.Num.Impl_1.to_be_bytes (bytes : u8) : RustM (RustArray u8 1) 

opaque Core_models.Num.Impl_1.to_le_bytes (bytes : u8) : RustM (RustArray u8 1) 

def Core_models.Num.Impl_1.rem_euclid (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.rem_euclid_u8 x y)

@[spec]
def Core_models.Num.Impl_1.rem_euclid.spec (x : u8) (y : u8)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : u8)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_1.rem_euclid (x : u8) (y : u8) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_1.rem_euclid] <;> try grind
}

@[reducible] instance Core_models.Num.Impl.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u8
  where

instance Core_models.Num.Impl : Core_models.Default.Default u8 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u8))

def Core_models.Num.Impl_3.MIN : u16 :=
  RustM.of_isOk (do (pure (0 : u16))) (by rfl)

def Core_models.Num.Impl_3.MAX : u16 :=
  RustM.of_isOk (do (pure (65535 : u16))) (by rfl)

def Core_models.Num.Impl_3.BITS : u32 :=
  RustM.of_isOk (do (pure (16 : u32))) (by rfl)

def Core_models.Num.Impl_3.wrapping_add (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.wrapping_add_u16 x y)

def Core_models.Num.Impl_3.saturating_add (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.saturating_add_u16 x y)

def Core_models.Num.Impl_3.overflowing_add
  (x : u16)
  (y : u16)
  : RustM (Rust_primitives.Hax.Tuple2 u16 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_u16 x y)

def Core_models.Num.Impl_3.wrapping_sub (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u16 x y)

def Core_models.Num.Impl_3.saturating_sub (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.saturating_sub_u16 x y)

def Core_models.Num.Impl_3.overflowing_sub
  (x : u16)
  (y : u16)
  : RustM (Rust_primitives.Hax.Tuple2 u16 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_u16 x y)

def Core_models.Num.Impl_3.wrapping_mul (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u16 x y)

def Core_models.Num.Impl_3.saturating_mul (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.saturating_mul_u16 x y)

def Core_models.Num.Impl_3.overflowing_mul
  (x : u16)
  (y : u16)
  : RustM (Rust_primitives.Hax.Tuple2 u16 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_u16 x y)

def Core_models.Num.Impl_3.pow (x : u16) (exp : u32) : RustM u16 := do
  (Rust_primitives.Arithmetic.pow_u16 x exp)

def Core_models.Num.Impl_3.count_ones (x : u16) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_u16 x)

opaque Core_models.Num.Impl_3.rotate_right (x : u16) (n : u32) : RustM u16 

opaque Core_models.Num.Impl_3.rotate_left (x : u16) (n : u32) : RustM u16 

opaque Core_models.Num.Impl_3.leading_zeros (x : u16) : RustM u32 

opaque Core_models.Num.Impl_3.ilog2 (x : u16) : RustM u32 

opaque Core_models.Num.Impl_3.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result u16 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_3.from_be_bytes
  (bytes : (RustArray u8 2))
  : RustM u16


opaque Core_models.Num.Impl_3.from_le_bytes
  (bytes : (RustArray u8 2))
  : RustM u16


opaque Core_models.Num.Impl_3.to_be_bytes
  (bytes : u16)
  : RustM (RustArray u8 2)


opaque Core_models.Num.Impl_3.to_le_bytes
  (bytes : u16)
  : RustM (RustArray u8 2)


def Core_models.Num.Impl_3.rem_euclid (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.rem_euclid_u16 x y)

@[spec]
def Core_models.Num.Impl_3.rem_euclid.spec (x : u16) (y : u16)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : u16)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_3.rem_euclid (x : u16) (y : u16) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_3.rem_euclid] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_2.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u16
  where

instance Core_models.Num.Impl_2 : Core_models.Default.Default u16 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u16))

def Core_models.Num.Impl_5.MIN : u32 :=
  RustM.of_isOk (do (pure (0 : u32))) (by rfl)

def Core_models.Num.Impl_5.MAX : u32 :=
  RustM.of_isOk (do (pure (4294967295 : u32))) (by rfl)

def Core_models.Num.Impl_5.BITS : u32 :=
  RustM.of_isOk (do (pure (32 : u32))) (by rfl)

def Core_models.Num.Impl_5.wrapping_add (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.wrapping_add_u32 x y)

def Core_models.Num.Impl_5.saturating_add (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.saturating_add_u32 x y)

def Core_models.Num.Impl_5.overflowing_add
  (x : u32)
  (y : u32)
  : RustM (Rust_primitives.Hax.Tuple2 u32 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_u32 x y)

def Core_models.Num.Impl_5.wrapping_sub (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u32 x y)

def Core_models.Num.Impl_5.saturating_sub (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.saturating_sub_u32 x y)

def Core_models.Num.Impl_5.overflowing_sub
  (x : u32)
  (y : u32)
  : RustM (Rust_primitives.Hax.Tuple2 u32 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_u32 x y)

def Core_models.Num.Impl_5.wrapping_mul (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u32 x y)

def Core_models.Num.Impl_5.saturating_mul (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.saturating_mul_u32 x y)

def Core_models.Num.Impl_5.overflowing_mul
  (x : u32)
  (y : u32)
  : RustM (Rust_primitives.Hax.Tuple2 u32 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_u32 x y)

def Core_models.Num.Impl_5.pow (x : u32) (exp : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.pow_u32 x exp)

def Core_models.Num.Impl_5.count_ones (x : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_u32 x)

opaque Core_models.Num.Impl_5.rotate_right (x : u32) (n : u32) : RustM u32 

opaque Core_models.Num.Impl_5.rotate_left (x : u32) (n : u32) : RustM u32 

opaque Core_models.Num.Impl_5.leading_zeros (x : u32) : RustM u32 

opaque Core_models.Num.Impl_5.ilog2 (x : u32) : RustM u32 

opaque Core_models.Num.Impl_5.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result u32 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_5.from_be_bytes
  (bytes : (RustArray u8 4))
  : RustM u32


opaque Core_models.Num.Impl_5.from_le_bytes
  (bytes : (RustArray u8 4))
  : RustM u32


opaque Core_models.Num.Impl_5.to_be_bytes
  (bytes : u32)
  : RustM (RustArray u8 4)


opaque Core_models.Num.Impl_5.to_le_bytes
  (bytes : u32)
  : RustM (RustArray u8 4)


def Core_models.Num.Impl_5.rem_euclid (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.rem_euclid_u32 x y)

@[spec]
def Core_models.Num.Impl_5.rem_euclid.spec (x : u32) (y : u32)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : u32)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_5.rem_euclid (x : u32) (y : u32) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_5.rem_euclid] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_4.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u32
  where

instance Core_models.Num.Impl_4 : Core_models.Default.Default u32 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u32))

def Core_models.Num.Impl_7.MIN : u64 :=
  RustM.of_isOk (do (pure (0 : u64))) (by rfl)

def Core_models.Num.Impl_7.MAX : u64 :=
  RustM.of_isOk (do (pure (18446744073709551615 : u64))) (by rfl)

def Core_models.Num.Impl_7.BITS : u32 :=
  RustM.of_isOk (do (pure (64 : u32))) (by rfl)

def Core_models.Num.Impl_7.wrapping_add (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.wrapping_add_u64 x y)

def Core_models.Num.Impl_7.saturating_add (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.saturating_add_u64 x y)

def Core_models.Num.Impl_7.overflowing_add
  (x : u64)
  (y : u64)
  : RustM (Rust_primitives.Hax.Tuple2 u64 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_u64 x y)

def Core_models.Num.Impl_7.wrapping_sub (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u64 x y)

def Core_models.Num.Impl_7.saturating_sub (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.saturating_sub_u64 x y)

def Core_models.Num.Impl_7.overflowing_sub
  (x : u64)
  (y : u64)
  : RustM (Rust_primitives.Hax.Tuple2 u64 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_u64 x y)

def Core_models.Num.Impl_7.wrapping_mul (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u64 x y)

def Core_models.Num.Impl_7.saturating_mul (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.saturating_mul_u64 x y)

def Core_models.Num.Impl_7.overflowing_mul
  (x : u64)
  (y : u64)
  : RustM (Rust_primitives.Hax.Tuple2 u64 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_u64 x y)

def Core_models.Num.Impl_7.pow (x : u64) (exp : u32) : RustM u64 := do
  (Rust_primitives.Arithmetic.pow_u64 x exp)

def Core_models.Num.Impl_7.count_ones (x : u64) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_u64 x)

opaque Core_models.Num.Impl_7.rotate_right (x : u64) (n : u32) : RustM u64 

opaque Core_models.Num.Impl_7.rotate_left (x : u64) (n : u32) : RustM u64 

opaque Core_models.Num.Impl_7.leading_zeros (x : u64) : RustM u32 

opaque Core_models.Num.Impl_7.ilog2 (x : u64) : RustM u32 

opaque Core_models.Num.Impl_7.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result u64 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_7.from_be_bytes
  (bytes : (RustArray u8 8))
  : RustM u64


opaque Core_models.Num.Impl_7.from_le_bytes
  (bytes : (RustArray u8 8))
  : RustM u64


opaque Core_models.Num.Impl_7.to_be_bytes
  (bytes : u64)
  : RustM (RustArray u8 8)


opaque Core_models.Num.Impl_7.to_le_bytes
  (bytes : u64)
  : RustM (RustArray u8 8)


def Core_models.Num.Impl_7.rem_euclid (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.rem_euclid_u64 x y)

@[spec]
def Core_models.Num.Impl_7.rem_euclid.spec (x : u64) (y : u64)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : u64)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_7.rem_euclid (x : u64) (y : u64) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_7.rem_euclid] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_6.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u64
  where

instance Core_models.Num.Impl_6 : Core_models.Default.Default u64 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u64))

def Core_models.Num.Impl_9.MIN : u128 :=
  RustM.of_isOk (do (pure (0 : u128))) (by rfl)

def Core_models.Num.Impl_9.MAX : u128 :=
  RustM.of_isOk
    (do (pure (340282366920938463463374607431768211455 : u128)))
    (by rfl)

def Core_models.Num.Impl_9.BITS : u32 :=
  RustM.of_isOk (do (pure (128 : u32))) (by rfl)

def Core_models.Num.Impl_9.wrapping_add (x : u128) (y : u128) : RustM u128 := do
  (Rust_primitives.Arithmetic.wrapping_add_u128 x y)

def Core_models.Num.Impl_9.saturating_add
  (x : u128)
  (y : u128)
  : RustM u128
  := do
  (Rust_primitives.Arithmetic.saturating_add_u128 x y)

def Core_models.Num.Impl_9.overflowing_add
  (x : u128)
  (y : u128)
  : RustM (Rust_primitives.Hax.Tuple2 u128 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_u128 x y)

def Core_models.Num.Impl_9.wrapping_sub (x : u128) (y : u128) : RustM u128 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u128 x y)

def Core_models.Num.Impl_9.saturating_sub
  (x : u128)
  (y : u128)
  : RustM u128
  := do
  (Rust_primitives.Arithmetic.saturating_sub_u128 x y)

def Core_models.Num.Impl_9.overflowing_sub
  (x : u128)
  (y : u128)
  : RustM (Rust_primitives.Hax.Tuple2 u128 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_u128 x y)

def Core_models.Num.Impl_9.wrapping_mul (x : u128) (y : u128) : RustM u128 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u128 x y)

def Core_models.Num.Impl_9.saturating_mul
  (x : u128)
  (y : u128)
  : RustM u128
  := do
  (Rust_primitives.Arithmetic.saturating_mul_u128 x y)

def Core_models.Num.Impl_9.overflowing_mul
  (x : u128)
  (y : u128)
  : RustM (Rust_primitives.Hax.Tuple2 u128 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_u128 x y)

def Core_models.Num.Impl_9.pow (x : u128) (exp : u32) : RustM u128 := do
  (Rust_primitives.Arithmetic.pow_u128 x exp)

def Core_models.Num.Impl_9.count_ones (x : u128) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_u128 x)

opaque Core_models.Num.Impl_9.rotate_right (x : u128) (n : u32) : RustM u128 

opaque Core_models.Num.Impl_9.rotate_left (x : u128) (n : u32) : RustM u128 

opaque Core_models.Num.Impl_9.leading_zeros (x : u128) : RustM u32 

opaque Core_models.Num.Impl_9.ilog2 (x : u128) : RustM u32 

opaque Core_models.Num.Impl_9.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result u128 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_9.from_be_bytes
  (bytes : (RustArray u8 16))
  : RustM u128


opaque Core_models.Num.Impl_9.from_le_bytes
  (bytes : (RustArray u8 16))
  : RustM u128


opaque Core_models.Num.Impl_9.to_be_bytes
  (bytes : u128)
  : RustM (RustArray u8 16)


opaque Core_models.Num.Impl_9.to_le_bytes
  (bytes : u128)
  : RustM (RustArray u8 16)


def Core_models.Num.Impl_9.rem_euclid (x : u128) (y : u128) : RustM u128 := do
  (Rust_primitives.Arithmetic.rem_euclid_u128 x y)

@[spec]
def Core_models.Num.Impl_9.rem_euclid.spec (x : u128) (y : u128)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : u128)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_9.rem_euclid (x : u128) (y : u128) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_9.rem_euclid] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_8.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u128
  where

instance Core_models.Num.Impl_8 : Core_models.Default.Default u128 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u128))

def Core_models.Num.Impl_11.MIN : usize :=
  RustM.of_isOk (do (pure (0 : usize))) (by rfl)

def Core_models.Num.Impl_11.MAX : usize :=
  RustM.of_isOk (do (pure Rust_primitives.Arithmetic.USIZE_MAX)) (by rfl)

def Core_models.Num.Impl_11.BITS : u32 :=
  RustM.of_isOk (do (pure Rust_primitives.Arithmetic.SIZE_BITS)) (by rfl)

def Core_models.Num.Impl_11.wrapping_add
  (x : usize)
  (y : usize)
  : RustM usize
  := do
  (Rust_primitives.Arithmetic.wrapping_add_usize x y)

def Core_models.Num.Impl_11.saturating_add
  (x : usize)
  (y : usize)
  : RustM usize
  := do
  (Rust_primitives.Arithmetic.saturating_add_usize x y)

def Core_models.Num.Impl_11.overflowing_add
  (x : usize)
  (y : usize)
  : RustM (Rust_primitives.Hax.Tuple2 usize Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_usize x y)

def Core_models.Num.Impl_11.wrapping_sub
  (x : usize)
  (y : usize)
  : RustM usize
  := do
  (Rust_primitives.Arithmetic.wrapping_sub_usize x y)

def Core_models.Num.Impl_11.saturating_sub
  (x : usize)
  (y : usize)
  : RustM usize
  := do
  (Rust_primitives.Arithmetic.saturating_sub_usize x y)

def Core_models.Num.Impl_11.overflowing_sub
  (x : usize)
  (y : usize)
  : RustM (Rust_primitives.Hax.Tuple2 usize Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_usize x y)

def Core_models.Num.Impl_11.wrapping_mul
  (x : usize)
  (y : usize)
  : RustM usize
  := do
  (Rust_primitives.Arithmetic.wrapping_mul_usize x y)

def Core_models.Num.Impl_11.saturating_mul
  (x : usize)
  (y : usize)
  : RustM usize
  := do
  (Rust_primitives.Arithmetic.saturating_mul_usize x y)

def Core_models.Num.Impl_11.overflowing_mul
  (x : usize)
  (y : usize)
  : RustM (Rust_primitives.Hax.Tuple2 usize Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_usize x y)

def Core_models.Num.Impl_11.pow (x : usize) (exp : u32) : RustM usize := do
  (Rust_primitives.Arithmetic.pow_usize x exp)

def Core_models.Num.Impl_11.count_ones (x : usize) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_usize x)

opaque Core_models.Num.Impl_11.rotate_right (x : usize) (n : u32) : RustM usize 

opaque Core_models.Num.Impl_11.rotate_left (x : usize) (n : u32) : RustM usize 

opaque Core_models.Num.Impl_11.leading_zeros (x : usize) : RustM u32 

opaque Core_models.Num.Impl_11.ilog2 (x : usize) : RustM u32 

opaque Core_models.Num.Impl_11.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result usize Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_11.from_be_bytes
  (bytes : (RustArray u8 0))
  : RustM usize


opaque Core_models.Num.Impl_11.from_le_bytes
  (bytes : (RustArray u8 0))
  : RustM usize


opaque Core_models.Num.Impl_11.to_be_bytes
  (bytes : usize)
  : RustM (RustArray u8 0)


opaque Core_models.Num.Impl_11.to_le_bytes
  (bytes : usize)
  : RustM (RustArray u8 0)


def Core_models.Num.Impl_11.rem_euclid
  (x : usize)
  (y : usize)
  : RustM usize
  := do
  (Rust_primitives.Arithmetic.rem_euclid_usize x y)

@[spec]
def Core_models.Num.Impl_11.rem_euclid.spec (x : usize) (y : usize)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : usize)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_11.rem_euclid (x : usize) (y : usize) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_11.rem_euclid] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_10.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes usize
  where

instance Core_models.Num.Impl_10 : Core_models.Default.Default usize where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : usize))

def Core_models.Num.Impl_13.MIN : i8 :=
  RustM.of_isOk (do (pure (-128 : i8))) (by rfl)

def Core_models.Num.Impl_13.MAX : i8 :=
  RustM.of_isOk (do (pure (127 : i8))) (by rfl)

def Core_models.Num.Impl_13.BITS : u32 :=
  RustM.of_isOk (do (pure (8 : u32))) (by rfl)

def Core_models.Num.Impl_13.wrapping_add (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.wrapping_add_i8 x y)

def Core_models.Num.Impl_13.saturating_add (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.saturating_add_i8 x y)

def Core_models.Num.Impl_13.overflowing_add
  (x : i8)
  (y : i8)
  : RustM (Rust_primitives.Hax.Tuple2 i8 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_i8 x y)

def Core_models.Num.Impl_13.wrapping_sub (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i8 x y)

def Core_models.Num.Impl_13.saturating_sub (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.saturating_sub_i8 x y)

def Core_models.Num.Impl_13.overflowing_sub
  (x : i8)
  (y : i8)
  : RustM (Rust_primitives.Hax.Tuple2 i8 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_i8 x y)

def Core_models.Num.Impl_13.wrapping_mul (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i8 x y)

def Core_models.Num.Impl_13.saturating_mul (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.saturating_mul_i8 x y)

def Core_models.Num.Impl_13.overflowing_mul
  (x : i8)
  (y : i8)
  : RustM (Rust_primitives.Hax.Tuple2 i8 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_i8 x y)

def Core_models.Num.Impl_13.pow (x : i8) (exp : u32) : RustM i8 := do
  (Rust_primitives.Arithmetic.pow_i8 x exp)

def Core_models.Num.Impl_13.count_ones (x : i8) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_i8 x)

opaque Core_models.Num.Impl_13.rotate_right (x : i8) (n : u32) : RustM i8 

opaque Core_models.Num.Impl_13.rotate_left (x : i8) (n : u32) : RustM i8 

opaque Core_models.Num.Impl_13.leading_zeros (x : i8) : RustM u32 

opaque Core_models.Num.Impl_13.ilog2 (x : i8) : RustM u32 

opaque Core_models.Num.Impl_13.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result i8 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_13.from_be_bytes
  (bytes : (RustArray u8 1))
  : RustM i8


opaque Core_models.Num.Impl_13.from_le_bytes
  (bytes : (RustArray u8 1))
  : RustM i8


opaque Core_models.Num.Impl_13.to_be_bytes
  (bytes : i8)
  : RustM (RustArray u8 1)


opaque Core_models.Num.Impl_13.to_le_bytes
  (bytes : i8)
  : RustM (RustArray u8 1)


def Core_models.Num.Impl_13.rem_euclid (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.rem_euclid_i8 x y)

@[spec]
def Core_models.Num.Impl_13.rem_euclid.spec (x : i8) (y : i8)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : i8)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_13.rem_euclid (x : i8) (y : i8) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_13.rem_euclid] <;> try grind
}

def Core_models.Num.Impl_13.abs (x : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.abs_i8 x)

@[spec]
def Core_models.Num.Impl_13.abs.spec (x : i8)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.gt x Core.Num.Impl.MIN))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_13.abs (x : i8) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_13.abs] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_12.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i8
  where

instance Core_models.Num.Impl_12 : Core_models.Default.Default i8 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i8))

def Core_models.Num.Impl_15.MIN : i16 :=
  RustM.of_isOk (do (pure (-32768 : i16))) (by rfl)

def Core_models.Num.Impl_15.MAX : i16 :=
  RustM.of_isOk (do (pure (32767 : i16))) (by rfl)

def Core_models.Num.Impl_15.BITS : u32 :=
  RustM.of_isOk (do (pure (16 : u32))) (by rfl)

def Core_models.Num.Impl_15.wrapping_add (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.wrapping_add_i16 x y)

def Core_models.Num.Impl_15.saturating_add (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.saturating_add_i16 x y)

def Core_models.Num.Impl_15.overflowing_add
  (x : i16)
  (y : i16)
  : RustM (Rust_primitives.Hax.Tuple2 i16 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_i16 x y)

def Core_models.Num.Impl_15.wrapping_sub (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i16 x y)

def Core_models.Num.Impl_15.saturating_sub (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.saturating_sub_i16 x y)

def Core_models.Num.Impl_15.overflowing_sub
  (x : i16)
  (y : i16)
  : RustM (Rust_primitives.Hax.Tuple2 i16 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_i16 x y)

def Core_models.Num.Impl_15.wrapping_mul (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i16 x y)

def Core_models.Num.Impl_15.saturating_mul (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.saturating_mul_i16 x y)

def Core_models.Num.Impl_15.overflowing_mul
  (x : i16)
  (y : i16)
  : RustM (Rust_primitives.Hax.Tuple2 i16 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_i16 x y)

def Core_models.Num.Impl_15.pow (x : i16) (exp : u32) : RustM i16 := do
  (Rust_primitives.Arithmetic.pow_i16 x exp)

def Core_models.Num.Impl_15.count_ones (x : i16) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_i16 x)

opaque Core_models.Num.Impl_15.rotate_right (x : i16) (n : u32) : RustM i16 

opaque Core_models.Num.Impl_15.rotate_left (x : i16) (n : u32) : RustM i16 

opaque Core_models.Num.Impl_15.leading_zeros (x : i16) : RustM u32 

opaque Core_models.Num.Impl_15.ilog2 (x : i16) : RustM u32 

opaque Core_models.Num.Impl_15.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result i16 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_15.from_be_bytes
  (bytes : (RustArray u8 2))
  : RustM i16


opaque Core_models.Num.Impl_15.from_le_bytes
  (bytes : (RustArray u8 2))
  : RustM i16


opaque Core_models.Num.Impl_15.to_be_bytes
  (bytes : i16)
  : RustM (RustArray u8 2)


opaque Core_models.Num.Impl_15.to_le_bytes
  (bytes : i16)
  : RustM (RustArray u8 2)


def Core_models.Num.Impl_15.rem_euclid (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.rem_euclid_i16 x y)

@[spec]
def Core_models.Num.Impl_15.rem_euclid.spec (x : i16) (y : i16)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : i16)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_15.rem_euclid (x : i16) (y : i16) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_15.rem_euclid] <;> try grind
}

def Core_models.Num.Impl_15.abs (x : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.abs_i16 x)

@[spec]
def Core_models.Num.Impl_15.abs.spec (x : i16)  :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.gt x Core.Num.Impl_1.MIN))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_15.abs (x : i16) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_15.abs] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_14.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i16
  where

instance Core_models.Num.Impl_14 : Core_models.Default.Default i16 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i16))

def Core_models.Num.Impl_17.MIN : i32 :=
  RustM.of_isOk (do (pure (-2147483648 : i32))) (by rfl)

def Core_models.Num.Impl_17.MAX : i32 :=
  RustM.of_isOk (do (pure (2147483647 : i32))) (by rfl)

def Core_models.Num.Impl_17.BITS : u32 :=
  RustM.of_isOk (do (pure (32 : u32))) (by rfl)

def Core_models.Num.Impl_17.wrapping_add (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.wrapping_add_i32 x y)

def Core_models.Num.Impl_17.saturating_add (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.saturating_add_i32 x y)

def Core_models.Num.Impl_17.overflowing_add
  (x : i32)
  (y : i32)
  : RustM (Rust_primitives.Hax.Tuple2 i32 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_i32 x y)

def Core_models.Num.Impl_17.wrapping_sub (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i32 x y)

def Core_models.Num.Impl_17.saturating_sub (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.saturating_sub_i32 x y)

def Core_models.Num.Impl_17.overflowing_sub
  (x : i32)
  (y : i32)
  : RustM (Rust_primitives.Hax.Tuple2 i32 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_i32 x y)

def Core_models.Num.Impl_17.wrapping_mul (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i32 x y)

def Core_models.Num.Impl_17.saturating_mul (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.saturating_mul_i32 x y)

def Core_models.Num.Impl_17.overflowing_mul
  (x : i32)
  (y : i32)
  : RustM (Rust_primitives.Hax.Tuple2 i32 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_i32 x y)

def Core_models.Num.Impl_17.pow (x : i32) (exp : u32) : RustM i32 := do
  (Rust_primitives.Arithmetic.pow_i32 x exp)

def Core_models.Num.Impl_17.count_ones (x : i32) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_i32 x)

opaque Core_models.Num.Impl_17.rotate_right (x : i32) (n : u32) : RustM i32 

opaque Core_models.Num.Impl_17.rotate_left (x : i32) (n : u32) : RustM i32 

opaque Core_models.Num.Impl_17.leading_zeros (x : i32) : RustM u32 

opaque Core_models.Num.Impl_17.ilog2 (x : i32) : RustM u32 

opaque Core_models.Num.Impl_17.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result i32 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_17.from_be_bytes
  (bytes : (RustArray u8 4))
  : RustM i32


opaque Core_models.Num.Impl_17.from_le_bytes
  (bytes : (RustArray u8 4))
  : RustM i32


opaque Core_models.Num.Impl_17.to_be_bytes
  (bytes : i32)
  : RustM (RustArray u8 4)


opaque Core_models.Num.Impl_17.to_le_bytes
  (bytes : i32)
  : RustM (RustArray u8 4)


def Core_models.Num.Impl_17.rem_euclid (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.rem_euclid_i32 x y)

@[spec]
def Core_models.Num.Impl_17.rem_euclid.spec (x : i32) (y : i32)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : i32)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_17.rem_euclid (x : i32) (y : i32) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_17.rem_euclid] <;> try grind
}

def Core_models.Num.Impl_17.abs (x : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.abs_i32 x)

@[spec]
def Core_models.Num.Impl_17.abs.spec (x : i32)  :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.gt x Core.Num.Impl_2.MIN))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_17.abs (x : i32) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_17.abs] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_16.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i32
  where

instance Core_models.Num.Impl_16 : Core_models.Default.Default i32 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i32))

def Core_models.Num.Impl_19.MIN : i64 :=
  RustM.of_isOk (do (pure (-9223372036854775808 : i64))) (by rfl)

def Core_models.Num.Impl_19.MAX : i64 :=
  RustM.of_isOk (do (pure (9223372036854775807 : i64))) (by rfl)

def Core_models.Num.Impl_19.BITS : u32 :=
  RustM.of_isOk (do (pure (64 : u32))) (by rfl)

def Core_models.Num.Impl_19.wrapping_add (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.wrapping_add_i64 x y)

def Core_models.Num.Impl_19.saturating_add (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.saturating_add_i64 x y)

def Core_models.Num.Impl_19.overflowing_add
  (x : i64)
  (y : i64)
  : RustM (Rust_primitives.Hax.Tuple2 i64 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_i64 x y)

def Core_models.Num.Impl_19.wrapping_sub (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i64 x y)

def Core_models.Num.Impl_19.saturating_sub (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.saturating_sub_i64 x y)

def Core_models.Num.Impl_19.overflowing_sub
  (x : i64)
  (y : i64)
  : RustM (Rust_primitives.Hax.Tuple2 i64 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_i64 x y)

def Core_models.Num.Impl_19.wrapping_mul (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i64 x y)

def Core_models.Num.Impl_19.saturating_mul (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.saturating_mul_i64 x y)

def Core_models.Num.Impl_19.overflowing_mul
  (x : i64)
  (y : i64)
  : RustM (Rust_primitives.Hax.Tuple2 i64 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_i64 x y)

def Core_models.Num.Impl_19.pow (x : i64) (exp : u32) : RustM i64 := do
  (Rust_primitives.Arithmetic.pow_i64 x exp)

def Core_models.Num.Impl_19.count_ones (x : i64) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_i64 x)

opaque Core_models.Num.Impl_19.rotate_right (x : i64) (n : u32) : RustM i64 

opaque Core_models.Num.Impl_19.rotate_left (x : i64) (n : u32) : RustM i64 

opaque Core_models.Num.Impl_19.leading_zeros (x : i64) : RustM u32 

opaque Core_models.Num.Impl_19.ilog2 (x : i64) : RustM u32 

opaque Core_models.Num.Impl_19.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result i64 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_19.from_be_bytes
  (bytes : (RustArray u8 8))
  : RustM i64


opaque Core_models.Num.Impl_19.from_le_bytes
  (bytes : (RustArray u8 8))
  : RustM i64


opaque Core_models.Num.Impl_19.to_be_bytes
  (bytes : i64)
  : RustM (RustArray u8 8)


opaque Core_models.Num.Impl_19.to_le_bytes
  (bytes : i64)
  : RustM (RustArray u8 8)


def Core_models.Num.Impl_19.rem_euclid (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.rem_euclid_i64 x y)

@[spec]
def Core_models.Num.Impl_19.rem_euclid.spec (x : i64) (y : i64)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : i64)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_19.rem_euclid (x : i64) (y : i64) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_19.rem_euclid] <;> try grind
}

def Core_models.Num.Impl_19.abs (x : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.abs_i64 x)

@[spec]
def Core_models.Num.Impl_19.abs.spec (x : i64)  :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.gt x Core.Num.Impl_3.MIN))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_19.abs (x : i64) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_19.abs] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_18.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i64
  where

instance Core_models.Num.Impl_18 : Core_models.Default.Default i64 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i64))

def Core_models.Num.Impl_21.MIN : i128 :=
  RustM.of_isOk
    (do (pure (-170141183460469231731687303715884105728 : i128)))
    (by rfl)

def Core_models.Num.Impl_21.MAX : i128 :=
  RustM.of_isOk
    (do (pure (170141183460469231731687303715884105727 : i128)))
    (by rfl)

def Core_models.Num.Impl_21.BITS : u32 :=
  RustM.of_isOk (do (pure (128 : u32))) (by rfl)

def Core_models.Num.Impl_21.wrapping_add
  (x : i128)
  (y : i128)
  : RustM i128
  := do
  (Rust_primitives.Arithmetic.wrapping_add_i128 x y)

def Core_models.Num.Impl_21.saturating_add
  (x : i128)
  (y : i128)
  : RustM i128
  := do
  (Rust_primitives.Arithmetic.saturating_add_i128 x y)

def Core_models.Num.Impl_21.overflowing_add
  (x : i128)
  (y : i128)
  : RustM (Rust_primitives.Hax.Tuple2 i128 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_i128 x y)

def Core_models.Num.Impl_21.wrapping_sub
  (x : i128)
  (y : i128)
  : RustM i128
  := do
  (Rust_primitives.Arithmetic.wrapping_sub_i128 x y)

def Core_models.Num.Impl_21.saturating_sub
  (x : i128)
  (y : i128)
  : RustM i128
  := do
  (Rust_primitives.Arithmetic.saturating_sub_i128 x y)

def Core_models.Num.Impl_21.overflowing_sub
  (x : i128)
  (y : i128)
  : RustM (Rust_primitives.Hax.Tuple2 i128 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_i128 x y)

def Core_models.Num.Impl_21.wrapping_mul
  (x : i128)
  (y : i128)
  : RustM i128
  := do
  (Rust_primitives.Arithmetic.wrapping_mul_i128 x y)

def Core_models.Num.Impl_21.saturating_mul
  (x : i128)
  (y : i128)
  : RustM i128
  := do
  (Rust_primitives.Arithmetic.saturating_mul_i128 x y)

def Core_models.Num.Impl_21.overflowing_mul
  (x : i128)
  (y : i128)
  : RustM (Rust_primitives.Hax.Tuple2 i128 Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_i128 x y)

def Core_models.Num.Impl_21.pow (x : i128) (exp : u32) : RustM i128 := do
  (Rust_primitives.Arithmetic.pow_i128 x exp)

def Core_models.Num.Impl_21.count_ones (x : i128) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_i128 x)

opaque Core_models.Num.Impl_21.rotate_right (x : i128) (n : u32) : RustM i128 

opaque Core_models.Num.Impl_21.rotate_left (x : i128) (n : u32) : RustM i128 

opaque Core_models.Num.Impl_21.leading_zeros (x : i128) : RustM u32 

opaque Core_models.Num.Impl_21.ilog2 (x : i128) : RustM u32 

opaque Core_models.Num.Impl_21.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result i128 Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_21.from_be_bytes
  (bytes : (RustArray u8 16))
  : RustM i128


opaque Core_models.Num.Impl_21.from_le_bytes
  (bytes : (RustArray u8 16))
  : RustM i128


opaque Core_models.Num.Impl_21.to_be_bytes
  (bytes : i128)
  : RustM (RustArray u8 16)


opaque Core_models.Num.Impl_21.to_le_bytes
  (bytes : i128)
  : RustM (RustArray u8 16)


def Core_models.Num.Impl_21.rem_euclid (x : i128) (y : i128) : RustM i128 := do
  (Rust_primitives.Arithmetic.rem_euclid_i128 x y)

@[spec]
def Core_models.Num.Impl_21.rem_euclid.spec (x : i128) (y : i128)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : i128)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_21.rem_euclid (x : i128) (y : i128) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_21.rem_euclid] <;> try grind
}

def Core_models.Num.Impl_21.abs (x : i128) : RustM i128 := do
  (Rust_primitives.Arithmetic.abs_i128 x)

@[spec]
def Core_models.Num.Impl_21.abs.spec (x : i128)  :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.gt x Core.Num.Impl_4.MIN))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_21.abs (x : i128) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_21.abs] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_20.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i128
  where

instance Core_models.Num.Impl_20 : Core_models.Default.Default i128 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i128))

def Core_models.Num.Impl_23.MIN : isize :=
  RustM.of_isOk (do (pure Rust_primitives.Arithmetic.ISIZE_MIN)) (by rfl)

def Core_models.Num.Impl_23.MAX : isize :=
  RustM.of_isOk (do (pure Rust_primitives.Arithmetic.ISIZE_MAX)) (by rfl)

def Core_models.Num.Impl_23.BITS : u32 :=
  RustM.of_isOk (do (pure Rust_primitives.Arithmetic.SIZE_BITS)) (by rfl)

def Core_models.Num.Impl_23.wrapping_add
  (x : isize)
  (y : isize)
  : RustM isize
  := do
  (Rust_primitives.Arithmetic.wrapping_add_isize x y)

def Core_models.Num.Impl_23.saturating_add
  (x : isize)
  (y : isize)
  : RustM isize
  := do
  (Rust_primitives.Arithmetic.saturating_add_isize x y)

def Core_models.Num.Impl_23.overflowing_add
  (x : isize)
  (y : isize)
  : RustM (Rust_primitives.Hax.Tuple2 isize Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_add_isize x y)

def Core_models.Num.Impl_23.wrapping_sub
  (x : isize)
  (y : isize)
  : RustM isize
  := do
  (Rust_primitives.Arithmetic.wrapping_sub_isize x y)

def Core_models.Num.Impl_23.saturating_sub
  (x : isize)
  (y : isize)
  : RustM isize
  := do
  (Rust_primitives.Arithmetic.saturating_sub_isize x y)

def Core_models.Num.Impl_23.overflowing_sub
  (x : isize)
  (y : isize)
  : RustM (Rust_primitives.Hax.Tuple2 isize Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_sub_isize x y)

def Core_models.Num.Impl_23.wrapping_mul
  (x : isize)
  (y : isize)
  : RustM isize
  := do
  (Rust_primitives.Arithmetic.wrapping_mul_isize x y)

def Core_models.Num.Impl_23.saturating_mul
  (x : isize)
  (y : isize)
  : RustM isize
  := do
  (Rust_primitives.Arithmetic.saturating_mul_isize x y)

def Core_models.Num.Impl_23.overflowing_mul
  (x : isize)
  (y : isize)
  : RustM (Rust_primitives.Hax.Tuple2 isize Bool)
  := do
  (Rust_primitives.Arithmetic.overflowing_mul_isize x y)

def Core_models.Num.Impl_23.pow (x : isize) (exp : u32) : RustM isize := do
  (Rust_primitives.Arithmetic.pow_isize x exp)

def Core_models.Num.Impl_23.count_ones (x : isize) : RustM u32 := do
  (Rust_primitives.Arithmetic.count_ones_isize x)

opaque Core_models.Num.Impl_23.rotate_right (x : isize) (n : u32) : RustM isize 

opaque Core_models.Num.Impl_23.rotate_left (x : isize) (n : u32) : RustM isize 

opaque Core_models.Num.Impl_23.leading_zeros (x : isize) : RustM u32 

opaque Core_models.Num.Impl_23.ilog2 (x : isize) : RustM u32 

opaque Core_models.Num.Impl_23.from_str_radix
  (src : String)
  (radix : u32)
  : RustM (Core.Result.Result isize Core_models.Num.Error.ParseIntError)


opaque Core_models.Num.Impl_23.from_be_bytes
  (bytes : (RustArray u8 0))
  : RustM isize


opaque Core_models.Num.Impl_23.from_le_bytes
  (bytes : (RustArray u8 0))
  : RustM isize


opaque Core_models.Num.Impl_23.to_be_bytes
  (bytes : isize)
  : RustM (RustArray u8 0)


opaque Core_models.Num.Impl_23.to_le_bytes
  (bytes : isize)
  : RustM (RustArray u8 0)


def Core_models.Num.Impl_23.rem_euclid
  (x : isize)
  (y : isize)
  : RustM isize
  := do
  (Rust_primitives.Arithmetic.rem_euclid_isize x y)

@[spec]
def Core_models.Num.Impl_23.rem_euclid.spec (x : isize) (y : isize)  :
    Spec
      (requires := do (Rust_primitives.Hax.Machine_int.ne y (0 : isize)))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_23.rem_euclid (x : isize) (y : isize) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_23.rem_euclid] <;> try grind
}

def Core_models.Num.Impl_23.abs (x : isize) : RustM isize := do
  (Rust_primitives.Arithmetic.abs_isize x)

@[spec]
def Core_models.Num.Impl_23.abs.spec (x : isize)  :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.gt x Core.Num.Impl_5.MIN))
      (ensures := fun _ => pure True)
      (Core_models.Num.Impl_23.abs (x : isize) ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Num.Impl_23.abs] <;> try grind
}

@[reducible] instance Core_models.Num.Impl_22.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes isize
  where

instance Core_models.Num.Impl_22 : Core_models.Default.Default isize where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : isize))

class Core_models.Ops.Arith.AddAssign.AssociatedTypes (Self : Type) (Rhs : Type)
  where

class Core_models.Ops.Arith.AddAssign
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.AddAssign.AssociatedTypes
      (Self : Type) (Rhs : Type))]
  where
  add_assign (Self Rhs) : (Self -> Rhs -> RustM Self)

class Core_models.Ops.Arith.SubAssign.AssociatedTypes (Self : Type) (Rhs : Type)
  where

class Core_models.Ops.Arith.SubAssign
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.SubAssign.AssociatedTypes
      (Self : Type) (Rhs : Type))]
  where
  sub_assign (Self Rhs) : (Self -> Rhs -> RustM Self)

class Core_models.Ops.Arith.MulAssign.AssociatedTypes (Self : Type) (Rhs : Type)
  where

class Core_models.Ops.Arith.MulAssign
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.MulAssign.AssociatedTypes
      (Self : Type) (Rhs : Type))]
  where
  mul_assign (Self Rhs) : (Self -> Rhs -> RustM Self)

class Core_models.Ops.Arith.DivAssign.AssociatedTypes (Self : Type) (Rhs : Type)
  where

class Core_models.Ops.Arith.DivAssign
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.DivAssign.AssociatedTypes
      (Self : Type) (Rhs : Type))]
  where
  div_assign (Self Rhs) : (Self -> Rhs -> RustM Self)

@[reducible] instance Core_models.Ops.Arith.Impl.AssociatedTypes :
  Core_models.Ops.Arith.AddAssign.AssociatedTypes u8 u8
  where

instance Core_models.Ops.Arith.Impl :
  Core_models.Ops.Arith.AddAssign u8 u8
  where
  add_assign := fun (self : u8) (rhs : u8) => do
    let self : u8 ← (self +? rhs);
    (pure self)

@[reducible] instance Core_models.Ops.Arith.Impl_1.AssociatedTypes :
  Core_models.Ops.Arith.SubAssign.AssociatedTypes u8 u8
  where

instance Core_models.Ops.Arith.Impl_1 :
  Core_models.Ops.Arith.SubAssign u8 u8
  where
  sub_assign := fun (self : u8) (rhs : u8) => do
    let self : u8 ← (self -? rhs);
    (pure self)

@[reducible] instance Core_models.Ops.Arith.Impl_2.AssociatedTypes :
  Core_models.Ops.Arith.AddAssign.AssociatedTypes u16 u16
  where

instance Core_models.Ops.Arith.Impl_2 :
  Core_models.Ops.Arith.AddAssign u16 u16
  where
  add_assign := fun (self : u16) (rhs : u16) => do
    let self : u16 ← (self +? rhs);
    (pure self)

@[reducible] instance Core_models.Ops.Arith.Impl_3.AssociatedTypes :
  Core_models.Ops.Arith.SubAssign.AssociatedTypes u16 u16
  where

instance Core_models.Ops.Arith.Impl_3 :
  Core_models.Ops.Arith.SubAssign u16 u16
  where
  sub_assign := fun (self : u16) (rhs : u16) => do
    let self : u16 ← (self -? rhs);
    (pure self)

@[reducible] instance Core_models.Ops.Arith.Impl_4.AssociatedTypes :
  Core_models.Ops.Arith.AddAssign.AssociatedTypes u32 u32
  where

instance Core_models.Ops.Arith.Impl_4 :
  Core_models.Ops.Arith.AddAssign u32 u32
  where
  add_assign := fun (self : u32) (rhs : u32) => do
    let self : u32 ← (self +? rhs);
    (pure self)

@[reducible] instance Core_models.Ops.Arith.Impl_5.AssociatedTypes :
  Core_models.Ops.Arith.SubAssign.AssociatedTypes u32 u32
  where

instance Core_models.Ops.Arith.Impl_5 :
  Core_models.Ops.Arith.SubAssign u32 u32
  where
  sub_assign := fun (self : u32) (rhs : u32) => do
    let self : u32 ← (self -? rhs);
    (pure self)

@[reducible] instance Core_models.Ops.Arith.Impl_6.AssociatedTypes :
  Core_models.Ops.Arith.AddAssign.AssociatedTypes u64 u64
  where

instance Core_models.Ops.Arith.Impl_6 :
  Core_models.Ops.Arith.AddAssign u64 u64
  where
  add_assign := fun (self : u64) (rhs : u64) => do
    let self : u64 ← (self +? rhs);
    (pure self)

@[reducible] instance Core_models.Ops.Arith.Impl_7.AssociatedTypes :
  Core_models.Ops.Arith.SubAssign.AssociatedTypes u64 u64
  where

instance Core_models.Ops.Arith.Impl_7 :
  Core_models.Ops.Arith.SubAssign u64 u64
  where
  sub_assign := fun (self : u64) (rhs : u64) => do
    let self : u64 ← (self -? rhs);
    (pure self)

inductive Core_models.Ops.Control_flow.ControlFlow (B : Type) (C : Type) : Type
| Continue : C -> Core_models.Ops.Control_flow.ControlFlow
  (B : Type) (C : Type) 
| Break : B -> Core_models.Ops.Control_flow.ControlFlow (B : Type) (C : Type) 


class Core_models.Ops.Try_trait.FromResidual.AssociatedTypes (Self : Type) (R :
  Type) where

class Core_models.Ops.Try_trait.FromResidual
  (Self : Type)
  (R : Type)
  [associatedTypes : outParam
    (Core_models.Ops.Try_trait.FromResidual.AssociatedTypes (Self : Type) (R :
      Type))]
  where
  from_residual (Self R) : (R -> RustM Self)

class Core_models.Ops.Drop.Drop.AssociatedTypes (Self : Type) where

class Core_models.Ops.Drop.Drop
  (Self : Type)
  [associatedTypes : outParam (Core_models.Ops.Drop.Drop.AssociatedTypes (Self :
      Type))]
  where
  drop (Self) : (Self -> RustM Self)

structure Core_models.Ops.Range.RangeTo (T : Type) where
  _end : T

structure Core_models.Ops.Range.RangeFrom (T : Type) where
  start : T

structure Core_models.Ops.Range.Range (T : Type) where
  start : T
  _end : T

structure Core_models.Ops.Range.RangeFull where


inductive Core_models.Option.Option (T : Type) : Type
| Some : T -> Core_models.Option.Option (T : Type) 
| None : Core_models.Option.Option (T : Type) 


class Core_models.Cmp.PartialOrd.AssociatedTypes (Self : Type) (Rhs : Type)
  where
  [trait_constr_PartialOrd_i0 :
  Core_models.Cmp.PartialEq.AssociatedTypes
  Self
  Rhs]

attribute [instance]
  Core_models.Cmp.PartialOrd.AssociatedTypes.trait_constr_PartialOrd_i0

class Core_models.Cmp.PartialOrd
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Cmp.PartialOrd.AssociatedTypes (Self
      : Type) (Rhs : Type))]
  where
  [trait_constr_PartialOrd_i0 : Core_models.Cmp.PartialEq Self Rhs]
  partial_cmp (Self Rhs)
    :
    (Self -> Rhs -> RustM (Core_models.Option.Option Core_models.Cmp.Ordering))

attribute [instance] Core_models.Cmp.PartialOrd.trait_constr_PartialOrd_i0

class Core_models.Cmp.PartialOrdDefaults.AssociatedTypes (Self : Type) (Rhs :
  Type) where

class Core_models.Cmp.PartialOrdDefaults
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam
    (Core_models.Cmp.PartialOrdDefaults.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  lt (Self Rhs)
    [Core_models.Cmp.PartialOrd.AssociatedTypes Self Rhs]
    [Core_models.Cmp.PartialOrd Self Rhs ]
    :
    (Self -> Rhs -> RustM Bool)
  le (Self Rhs)
    [Core_models.Cmp.PartialOrd.AssociatedTypes Self Rhs]
    [Core_models.Cmp.PartialOrd Self Rhs ]
    :
    (Self -> Rhs -> RustM Bool)
  gt (Self Rhs)
    [Core_models.Cmp.PartialOrd.AssociatedTypes Self Rhs]
    [Core_models.Cmp.PartialOrd Self Rhs ]
    :
    (Self -> Rhs -> RustM Bool)
  ge (Self Rhs)
    [Core_models.Cmp.PartialOrd.AssociatedTypes Self Rhs]
    [Core_models.Cmp.PartialOrd Self Rhs ]
    :
    (Self -> Rhs -> RustM Bool)

@[reducible] instance Core_models.Cmp.Impl_1.AssociatedTypes
  (T : Type)
  [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
  [Core_models.Cmp.PartialOrd T T ]
  :
  Core_models.Cmp.PartialOrdDefaults.AssociatedTypes T T
  where

instance Core_models.Cmp.Impl_1
  (T : Type)
  [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
  [Core_models.Cmp.PartialOrd T T ]
  :
  Core_models.Cmp.PartialOrdDefaults T T
  where
  lt :=
    fun
      [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
      [Core_models.Cmp.PartialOrd T T ]
      (self : T) (y : T) => do
    match (← (Core_models.Cmp.PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some (Core_models.Cmp.Ordering.Less ))
        => (pure true)
      | _ => (pure false)
  le :=
    fun
      [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
      [Core_models.Cmp.PartialOrd T T ]
      (self : T) (y : T) => do
    match (← (Core_models.Cmp.PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some (Core_models.Cmp.Ordering.Less )) |
        (Core_models.Option.Option.Some (Core_models.Cmp.Ordering.Equal ))
        => (pure true)
      | _ => (pure false)
  gt :=
    fun
      [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
      [Core_models.Cmp.PartialOrd T T ]
      (self : T) (y : T) => do
    match (← (Core_models.Cmp.PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some (Core_models.Cmp.Ordering.Greater ))
        => (pure true)
      | _ => (pure false)
  ge :=
    fun
      [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
      [Core_models.Cmp.PartialOrd T T ]
      (self : T) (y : T) => do
    match (← (Core_models.Cmp.PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some (Core_models.Cmp.Ordering.Greater )) |
        (Core_models.Option.Option.Some (Core_models.Cmp.Ordering.Equal ))
        => (pure true)
      | _ => (pure false)

class Core_models.Cmp.Ord.AssociatedTypes (Self : Type) where
  [trait_constr_Ord_i0 : Core_models.Cmp.Eq.AssociatedTypes Self]
  [trait_constr_Ord_i1 : Core_models.Cmp.PartialOrd.AssociatedTypes Self Self]

attribute [instance] Core_models.Cmp.Ord.AssociatedTypes.trait_constr_Ord_i0

attribute [instance] Core_models.Cmp.Ord.AssociatedTypes.trait_constr_Ord_i1

class Core_models.Cmp.Ord
  (Self : Type)
  [associatedTypes : outParam (Core_models.Cmp.Ord.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_Ord_i0 : Core_models.Cmp.Eq Self]
  [trait_constr_Ord_i1 : Core_models.Cmp.PartialOrd Self Self]
  cmp (Self) : (Self -> Self -> RustM Core_models.Cmp.Ordering)

attribute [instance] Core_models.Cmp.Ord.trait_constr_Ord_i0

attribute [instance] Core_models.Cmp.Ord.trait_constr_Ord_i1

def Core_models.Cmp.max
  (T : Type)
  [Core_models.Cmp.Ord.AssociatedTypes T] [Core_models.Cmp.Ord T ]
  (v1 : T)
  (v2 : T)
  : RustM T
  := do
  match (← (Core_models.Cmp.Ord.cmp T v1 v2)) with
    | (Core_models.Cmp.Ordering.Greater ) => (pure v1)
    | _ => (pure v2)

def Core_models.Cmp.min
  (T : Type)
  [Core_models.Cmp.Ord.AssociatedTypes T] [Core_models.Cmp.Ord T ]
  (v1 : T)
  (v2 : T)
  : RustM T
  := do
  match (← (Core_models.Cmp.Ord.cmp T v1 v2)) with
    | (Core_models.Cmp.Ordering.Greater ) => (pure v2)
    | _ => (pure v1)

@[reducible] instance Core_models.Cmp.Impl_2.AssociatedTypes
  (T : Type)
  [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
  [Core_models.Cmp.PartialOrd T T ]
  :
  Core_models.Cmp.PartialOrd.AssociatedTypes
  (Core_models.Cmp.Reverse T)
  (Core_models.Cmp.Reverse T)
  where

instance Core_models.Cmp.Impl_2
  (T : Type)
  [Core_models.Cmp.PartialOrd.AssociatedTypes T T]
  [Core_models.Cmp.PartialOrd T T ]
  :
  Core_models.Cmp.PartialOrd
  (Core_models.Cmp.Reverse T)
  (Core_models.Cmp.Reverse T)
  where
  partial_cmp :=
    fun
      (self : (Core_models.Cmp.Reverse T))
      (other : (Core_models.Cmp.Reverse T))
      => do
    (Core_models.Cmp.PartialOrd.partial_cmp
      T
      T (Core_models.Cmp.Reverse._0 other) (Core_models.Cmp.Reverse._0 self))

@[reducible] instance Core_models.Cmp.Impl_5.AssociatedTypes
  (T : Type) [Core_models.Cmp.Ord.AssociatedTypes T] [Core_models.Cmp.Ord T ] :
  Core_models.Cmp.Ord.AssociatedTypes (Core_models.Cmp.Reverse T)
  where

instance Core_models.Cmp.Impl_5
  (T : Type) [Core_models.Cmp.Ord.AssociatedTypes T] [Core_models.Cmp.Ord T ] :
  Core_models.Cmp.Ord (Core_models.Cmp.Reverse T)
  where
  cmp :=
    fun
      (self : (Core_models.Cmp.Reverse T))
      (other : (Core_models.Cmp.Reverse T))
      => do
    (Core_models.Cmp.Ord.cmp
      T (Core_models.Cmp.Reverse._0 other) (Core_models.Cmp.Reverse._0 self))

@[reducible] instance Core_models.Cmp.Impl_30.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes u8 u8
  where

instance Core_models.Cmp.Impl_30 : Core_models.Cmp.PartialOrd u8 u8 where
  partial_cmp := fun (self : u8) (other : u8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_31.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes u8
  where

instance Core_models.Cmp.Impl_31 : Core_models.Cmp.Ord u8 where
  cmp := fun (self : u8) (other : u8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_32.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes i8 i8
  where

instance Core_models.Cmp.Impl_32 : Core_models.Cmp.PartialOrd i8 i8 where
  partial_cmp := fun (self : i8) (other : i8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_33.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes i8
  where

instance Core_models.Cmp.Impl_33 : Core_models.Cmp.Ord i8 where
  cmp := fun (self : i8) (other : i8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_34.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes u16 u16
  where

instance Core_models.Cmp.Impl_34 : Core_models.Cmp.PartialOrd u16 u16 where
  partial_cmp := fun (self : u16) (other : u16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_35.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes u16
  where

instance Core_models.Cmp.Impl_35 : Core_models.Cmp.Ord u16 where
  cmp := fun (self : u16) (other : u16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_36.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes i16 i16
  where

instance Core_models.Cmp.Impl_36 : Core_models.Cmp.PartialOrd i16 i16 where
  partial_cmp := fun (self : i16) (other : i16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_37.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes i16
  where

instance Core_models.Cmp.Impl_37 : Core_models.Cmp.Ord i16 where
  cmp := fun (self : i16) (other : i16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_38.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes u32 u32
  where

instance Core_models.Cmp.Impl_38 : Core_models.Cmp.PartialOrd u32 u32 where
  partial_cmp := fun (self : u32) (other : u32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_39.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes u32
  where

instance Core_models.Cmp.Impl_39 : Core_models.Cmp.Ord u32 where
  cmp := fun (self : u32) (other : u32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_40.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes i32 i32
  where

instance Core_models.Cmp.Impl_40 : Core_models.Cmp.PartialOrd i32 i32 where
  partial_cmp := fun (self : i32) (other : i32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_41.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes i32
  where

instance Core_models.Cmp.Impl_41 : Core_models.Cmp.Ord i32 where
  cmp := fun (self : i32) (other : i32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_42.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes u64 u64
  where

instance Core_models.Cmp.Impl_42 : Core_models.Cmp.PartialOrd u64 u64 where
  partial_cmp := fun (self : u64) (other : u64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_43.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes u64
  where

instance Core_models.Cmp.Impl_43 : Core_models.Cmp.Ord u64 where
  cmp := fun (self : u64) (other : u64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_44.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes i64 i64
  where

instance Core_models.Cmp.Impl_44 : Core_models.Cmp.PartialOrd i64 i64 where
  partial_cmp := fun (self : i64) (other : i64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_45.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes i64
  where

instance Core_models.Cmp.Impl_45 : Core_models.Cmp.Ord i64 where
  cmp := fun (self : i64) (other : i64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_46.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes u128 u128
  where

instance Core_models.Cmp.Impl_46 : Core_models.Cmp.PartialOrd u128 u128 where
  partial_cmp := fun (self : u128) (other : u128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_47.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes u128
  where

instance Core_models.Cmp.Impl_47 : Core_models.Cmp.Ord u128 where
  cmp := fun (self : u128) (other : u128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_48.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes i128 i128
  where

instance Core_models.Cmp.Impl_48 : Core_models.Cmp.PartialOrd i128 i128 where
  partial_cmp := fun (self : i128) (other : i128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_49.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes i128
  where

instance Core_models.Cmp.Impl_49 : Core_models.Cmp.Ord i128 where
  cmp := fun (self : i128) (other : i128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_50.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes usize usize
  where

instance Core_models.Cmp.Impl_50 : Core_models.Cmp.PartialOrd usize usize where
  partial_cmp := fun (self : usize) (other : usize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_51.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes usize
  where

instance Core_models.Cmp.Impl_51 : Core_models.Cmp.Ord usize where
  cmp := fun (self : usize) (other : usize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

@[reducible] instance Core_models.Cmp.Impl_52.AssociatedTypes :
  Core_models.Cmp.PartialOrd.AssociatedTypes isize isize
  where

instance Core_models.Cmp.Impl_52 : Core_models.Cmp.PartialOrd isize isize where
  partial_cmp := fun (self : isize) (other : isize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Core_models.Cmp.Ordering.Equal))

@[reducible] instance Core_models.Cmp.Impl_53.AssociatedTypes :
  Core_models.Cmp.Ord.AssociatedTypes isize
  where

instance Core_models.Cmp.Impl_53 : Core_models.Cmp.Ord isize where
  cmp := fun (self : isize) (other : isize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Core_models.Cmp.Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Core_models.Cmp.Ordering.Greater)
      else
        (pure Core_models.Cmp.Ordering.Equal)

structure Core_models.Iter.Adapters.Flat_map.FlatMap
  (I : Type) (U : Type) (F : Type) where
  it : I
  f : F
  current : (Core_models.Option.Option U)

def Core_models.Num.Impl_1.checked_add
  (x : u8)
  (y : u8)
  : RustM (Core_models.Option.Option u8)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_1.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_1.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_1.checked_sub
  (x : u8)
  (y : u8)
  : RustM (Core_models.Option.Option u8)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_1.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_1.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_1.checked_mul
  (x : u8)
  (y : u8)
  : RustM (Core_models.Option.Option u8)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_1.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_1.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_3.checked_add
  (x : u16)
  (y : u16)
  : RustM (Core_models.Option.Option u16)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_3.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_3.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_3.checked_sub
  (x : u16)
  (y : u16)
  : RustM (Core_models.Option.Option u16)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_3.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_3.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_3.checked_mul
  (x : u16)
  (y : u16)
  : RustM (Core_models.Option.Option u16)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_3.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_3.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_5.checked_add
  (x : u32)
  (y : u32)
  : RustM (Core_models.Option.Option u32)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_5.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_5.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_5.checked_sub
  (x : u32)
  (y : u32)
  : RustM (Core_models.Option.Option u32)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_5.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_5.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_5.checked_mul
  (x : u32)
  (y : u32)
  : RustM (Core_models.Option.Option u32)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_5.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_5.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_7.checked_add
  (x : u64)
  (y : u64)
  : RustM (Core_models.Option.Option u64)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_7.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_7.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_7.checked_sub
  (x : u64)
  (y : u64)
  : RustM (Core_models.Option.Option u64)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_7.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_7.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_7.checked_mul
  (x : u64)
  (y : u64)
  : RustM (Core_models.Option.Option u64)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_7.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_7.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_9.checked_add
  (x : u128)
  (y : u128)
  : RustM (Core_models.Option.Option u128)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_9.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_9.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_9.checked_sub
  (x : u128)
  (y : u128)
  : RustM (Core_models.Option.Option u128)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_9.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_9.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_9.checked_mul
  (x : u128)
  (y : u128)
  : RustM (Core_models.Option.Option u128)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_9.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_9.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_11.checked_add
  (x : usize)
  (y : usize)
  : RustM (Core_models.Option.Option usize)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_11.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_11.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_11.checked_sub
  (x : usize)
  (y : usize)
  : RustM (Core_models.Option.Option usize)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_11.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_11.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_11.checked_mul
  (x : usize)
  (y : usize)
  : RustM (Core_models.Option.Option usize)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_11.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_11.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_13.checked_add
  (x : i8)
  (y : i8)
  : RustM (Core_models.Option.Option i8)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_13.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_13.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_13.checked_sub
  (x : i8)
  (y : i8)
  : RustM (Core_models.Option.Option i8)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_13.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_13.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_13.checked_mul
  (x : i8)
  (y : i8)
  : RustM (Core_models.Option.Option i8)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_13.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_13.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_15.checked_add
  (x : i16)
  (y : i16)
  : RustM (Core_models.Option.Option i16)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_15.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_15.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_15.checked_sub
  (x : i16)
  (y : i16)
  : RustM (Core_models.Option.Option i16)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_15.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_15.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_15.checked_mul
  (x : i16)
  (y : i16)
  : RustM (Core_models.Option.Option i16)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_15.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_15.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_17.checked_add
  (x : i32)
  (y : i32)
  : RustM (Core_models.Option.Option i32)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_17.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_17.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_17.checked_sub
  (x : i32)
  (y : i32)
  : RustM (Core_models.Option.Option i32)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_17.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_17.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_17.checked_mul
  (x : i32)
  (y : i32)
  : RustM (Core_models.Option.Option i32)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_17.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_17.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_19.checked_add
  (x : i64)
  (y : i64)
  : RustM (Core_models.Option.Option i64)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_19.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_19.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_19.checked_sub
  (x : i64)
  (y : i64)
  : RustM (Core_models.Option.Option i64)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_19.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_19.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_19.checked_mul
  (x : i64)
  (y : i64)
  : RustM (Core_models.Option.Option i64)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_19.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_19.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_21.checked_add
  (x : i128)
  (y : i128)
  : RustM (Core_models.Option.Option i128)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_21.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_21.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_21.checked_sub
  (x : i128)
  (y : i128)
  : RustM (Core_models.Option.Option i128)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_21.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_21.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_21.checked_mul
  (x : i128)
  (y : i128)
  : RustM (Core_models.Option.Option i128)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_21.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_21.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_23.checked_add
  (x : isize)
  (y : isize)
  : RustM (Core_models.Option.Option isize)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_23.MIN))
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.add
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_23.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x +? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_23.checked_sub
  (x : isize)
  (y : isize)
  : RustM (Core_models.Option.Option isize)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_23.MIN))
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.sub
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_23.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x -? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Num.Impl_23.checked_mul
  (x : isize)
  (y : isize)
  : RustM (Core_models.Option.Option isize)
  := do
  if
  (← ((← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_23.MIN))
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))))
    &&? (← (Rust_primitives.Hax.Int.le
      (← (Rust_primitives.Hax.Int.mul
        (← (Rust_primitives.Hax.Int.from_machine x))
        (← (Rust_primitives.Hax.Int.from_machine y))))
      (← (Rust_primitives.Hax.Int.from_machine Core_models.Num.Impl_23.MAX))))))
  then
    (pure (Core_models.Option.Option.Some (← (x *? y))))
  else
    (pure Core_models.Option.Option.None)

def Core_models.Option.Impl.as_ref
  (T : Type) (self : (Core_models.Option.Option T))
  : RustM (Core_models.Option.Option T)
  := do
  match self with
    | (Core_models.Option.Option.Some x)
      => (pure (Core_models.Option.Option.Some x))
    | (Core_models.Option.Option.None ) => (pure Core_models.Option.Option.None)

def Core_models.Option.Impl.unwrap_or
  (T : Type) (self : (Core_models.Option.Option T))
  (default : T)
  : RustM T
  := do
  match self with
    | (Core_models.Option.Option.Some x) => (pure x)
    | (Core_models.Option.Option.None ) => (pure default)

def Core_models.Option.Impl.unwrap_or_default
  (T : Type)
  [Core_models.Default.Default.AssociatedTypes T]
  [Core_models.Default.Default T ]
  (self : (Core_models.Option.Option T))
  : RustM T
  := do
  match self with
    | (Core_models.Option.Option.Some x) => (pure x)
    | (Core_models.Option.Option.None )
      => (Core_models.Default.Default.default T Rust_primitives.Hax.Tuple0.mk)

def Core_models.Option.Impl.take
  (T : Type) (self : (Core_models.Option.Option T))
  : RustM
  (Rust_primitives.Hax.Tuple2
    (Core_models.Option.Option T)
    (Core_models.Option.Option T))
  := do
  (pure (Rust_primitives.Hax.Tuple2.mk Core_models.Option.Option.None self))

def Core_models.Option.Impl.is_some
  (T : Type) (self : (Core_models.Option.Option T))
  : RustM Bool
  := do
  match self with
    | (Core_models.Option.Option.Some _) => (pure true)
    | _ => (pure false)

@[spec]
def
      Core_models.Option.Impl.is_some.spec
      (T : Type) (self : (Core_models.Option.Option T))
       :
    Spec
      (requires := do pure True)
      (ensures := fun
          res => do
          (Hax_lib.Prop.Constructors.implies
            (← (Hax_lib.Prop.Constructors.from_bool res))
            (← (Hax_lib.Prop.Impl.from_bool true))))
      (Core_models.Option.Impl.is_some
        (T : Type) (self : (Core_models.Option.Option T))
        ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Option.Impl.is_some] <;> try grind
}

def Core_models.Option.Impl.is_none
  (T : Type) (self : (Core_models.Option.Option T))
  : RustM Bool
  := do
  (Core.Cmp.PartialEq.eq (← (Core_models.Option.Impl.is_some T self)) false)

opaque Core_models.Panicking.panic_explicit
  (_ : Rust_primitives.Hax.Tuple0)
  : RustM Rust_primitives.Hax.Never


opaque Core_models.Panicking.panic
  (_msg : String)
  : RustM Rust_primitives.Hax.Never


opaque Core_models.Panicking.panic_fmt
  (_fmt : Core_models.Fmt.Arguments)
  : RustM Rust_primitives.Hax.Never


opaque Core_models.Panicking.Internal.panic
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM T


@[reducible] instance Core_models.Hash.Impl.AssociatedTypes (T : Type) :
  Core_models.Hash.Hash.AssociatedTypes T
  where

instance Core_models.Hash.Impl (T : Type) : Core_models.Hash.Hash T where
  hash :=
    fun
      (H : Type)
      [Core_models.Hash.Hasher.AssociatedTypes H] [Core_models.Hash.Hasher H ]
      (self : T) (h : H) => do
    (Core_models.Panicking.Internal.panic H Rust_primitives.Hax.Tuple0.mk)

inductive Core_models.Result.Result (T : Type) (E : Type) : Type
| Ok : T -> Core_models.Result.Result (T : Type) (E : Type) 
| Err : E -> Core_models.Result.Result (T : Type) (E : Type) 


abbrev Core_models.Fmt.Result
  : Type :=
  (Core_models.Result.Result Rust_primitives.Hax.Tuple0 Core_models.Fmt.Error)

class Core_models.Fmt.Display.AssociatedTypes (Self : Type) where

class Core_models.Fmt.Display
  (Self : Type)
  [associatedTypes : outParam (Core_models.Fmt.Display.AssociatedTypes (Self :
      Type))]
  where
  fmt (Self)
    :
    (Self
    -> Core_models.Fmt.Formatter
    -> RustM (Rust_primitives.Hax.Tuple2
      Core_models.Fmt.Formatter
      (Core_models.Result.Result
        Rust_primitives.Hax.Tuple0
        Core_models.Fmt.Error)))

class Core_models.Fmt.Debug.AssociatedTypes (Self : Type) where

class Core_models.Fmt.Debug
  (Self : Type)
  [associatedTypes : outParam (Core_models.Fmt.Debug.AssociatedTypes (Self :
      Type))]
  where
  dbg_fmt (Self)
    :
    (Self
    -> Core_models.Fmt.Formatter
    -> RustM (Rust_primitives.Hax.Tuple2
      Core_models.Fmt.Formatter
      (Core_models.Result.Result
        Rust_primitives.Hax.Tuple0
        Core_models.Fmt.Error)))

class Core_models.Error.Error.AssociatedTypes (Self : Type) where
  [trait_constr_Error_i0 : Core_models.Fmt.Display.AssociatedTypes Self]
  [trait_constr_Error_i1 : Core_models.Fmt.Debug.AssociatedTypes Self]

attribute [instance]
  Core_models.Error.Error.AssociatedTypes.trait_constr_Error_i0

attribute [instance]
  Core_models.Error.Error.AssociatedTypes.trait_constr_Error_i1

class Core_models.Error.Error
  (Self : Type)
  [associatedTypes : outParam (Core_models.Error.Error.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_Error_i0 : Core_models.Fmt.Display Self]
  [trait_constr_Error_i1 : Core_models.Fmt.Debug Self]

attribute [instance] Core_models.Error.Error.trait_constr_Error_i0

attribute [instance] Core_models.Error.Error.trait_constr_Error_i1

@[reducible] instance Core_models.Fmt.Impl.AssociatedTypes (T : Type) :
  Core_models.Fmt.Debug.AssociatedTypes T
  where

instance Core_models.Fmt.Impl (T : Type) : Core_models.Fmt.Debug T where
  dbg_fmt := fun (self : T) (f : Core_models.Fmt.Formatter) => do
    let
      hax_temp_output : (Core_models.Result.Result
        Rust_primitives.Hax.Tuple0
        Core_models.Fmt.Error) :=
      (Core_models.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk);
    (pure (Rust_primitives.Hax.Tuple2.mk f hax_temp_output))

def Core_models.Fmt.Impl_11.write_fmt
  (f : Core_models.Fmt.Formatter)
  (args : Core_models.Fmt.Arguments)
  : RustM
  (Rust_primitives.Hax.Tuple2
    Core_models.Fmt.Formatter
    (Core_models.Result.Result
      Rust_primitives.Hax.Tuple0
      Core_models.Fmt.Error))
  := do
  let
    hax_temp_output : (Core_models.Result.Result
      Rust_primitives.Hax.Tuple0
      Core_models.Fmt.Error) :=
    (Core_models.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk);
  (pure (Rust_primitives.Hax.Tuple2.mk f hax_temp_output))

def Core_models.Option.Impl.ok_or
  (T : Type) (E : Type) (self : (Core_models.Option.Option T))
  (err : E)
  : RustM (Core_models.Result.Result T E)
  := do
  match self with
    | (Core_models.Option.Option.Some v)
      => (pure (Core_models.Result.Result.Ok v))
    | (Core_models.Option.Option.None )
      => (pure (Core_models.Result.Result.Err err))

def Core_models.Result.Impl.is_ok
  (T : Type) (E : Type) (self : (Core_models.Result.Result T E))
  : RustM Bool
  := do
  match self with
    | (Core_models.Result.Result.Ok _) => (pure true)
    | _ => (pure false)

structure Core_models.Slice.Iter.Chunks (T : Type) where
  cs : usize
  elements : (RustSlice T)

def Core_models.Slice.Iter.Impl.new
  (T : Type) (cs : usize)
  (elements : (RustSlice T))
  : RustM (Core_models.Slice.Iter.Chunks T)
  := do
  (pure (Core_models.Slice.Iter.Chunks.mk (cs := cs) (elements := elements)))

structure Core_models.Slice.Iter.ChunksExact (T : Type) where
  cs : usize
  elements : (RustSlice T)

def Core_models.Slice.Iter.Impl_1.new
  (T : Type) (cs : usize)
  (elements : (RustSlice T))
  : RustM (Core_models.Slice.Iter.ChunksExact T)
  := do
  (pure (Core_models.Slice.Iter.ChunksExact.mk
    (cs := cs) (elements := elements)))

structure Core_models.Slice.Iter.Iter (T : Type) where
  _0 : (Rust_primitives.Sequence.Seq T)

def Core_models.Slice.Impl.len
  (T : Type) (s : (RustSlice T))
  : RustM usize
  := do
  (Rust_primitives.Slice.slice_length T s)

def Core_models.Slice.Impl.chunks
  (T : Type) (s : (RustSlice T))
  (cs : usize)
  : RustM (Core_models.Slice.Iter.Chunks T)
  := do
  (Core_models.Slice.Iter.Impl.new T cs s)

def Core_models.Slice.Impl.iter
  (T : Type) (s : (RustSlice T))
  : RustM (Core_models.Slice.Iter.Iter T)
  := do
  (pure (Core_models.Slice.Iter.Iter.mk
    (← (Rust_primitives.Sequence.seq_from_slice T s))))

def Core_models.Slice.Impl.chunks_exact
  (T : Type) (s : (RustSlice T))
  (cs : usize)
  : RustM (Core_models.Slice.Iter.ChunksExact T)
  := do
  (Core_models.Slice.Iter.Impl_1.new T cs s)

def Core_models.Slice.Impl.is_empty
  (T : Type) (s : (RustSlice T))
  : RustM Bool
  := do
  (Rust_primitives.Hax.Machine_int.eq (← (Core.Slice.Impl.len T s)) (0 : usize))

opaque Core_models.Slice.Impl.contains
  (T : Type) (s : (RustSlice T))
  (v : T)
  : RustM Bool


opaque Core_models.Slice.Impl.copy_within
  (T : Type)
  (R : Type)
  [Core.Marker.Copy.AssociatedTypes T] [Core.Marker.Copy T ]
  (s : (RustSlice T))
  (src : R)
  (dest : usize)
  : RustM (RustSlice T)


opaque Core_models.Slice.Impl.binary_search
  (T : Type) (s : (RustSlice T))
  (x : T)
  : RustM (Core.Result.Result usize usize)


def Core_models.Slice.Impl.copy_from_slice
  (T : Type)
  [Core_models.Marker.Copy.AssociatedTypes T] [Core_models.Marker.Copy T ]
  (s : (RustSlice T))
  (src : (RustSlice T))
  : RustM (RustSlice T)
  := do
  let s : (RustSlice T) ← (Rust_primitives.Mem.replace (RustSlice T) s src);
  (pure s)

@[spec]
def
      Core_models.Slice.Impl.copy_from_slice.spec
      (T : Type)
      [Core_models.Marker.Copy.AssociatedTypes T] [Core_models.Marker.Copy T ]
      (s : (RustSlice T))
      (src : (RustSlice T))
       :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.eq
          (← (Core.Slice.Impl.len T s))
          (← (Core.Slice.Impl.len T src))))
      (ensures := fun _ => pure True)
      (Core_models.Slice.Impl.copy_from_slice
        (T : Type)
        [Core_models.Marker.Copy.AssociatedTypes T] [Core_models.Marker.Copy T ]
        (s : (RustSlice T))
        (src : (RustSlice T))
        ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Slice.Impl.copy_from_slice] <;> try grind
}

def Core_models.Slice.Impl.clone_from_slice
  (T : Type)
  [Core_models.Clone.Clone.AssociatedTypes T] [Core_models.Clone.Clone T ]
  (s : (RustSlice T))
  (src : (RustSlice T))
  : RustM (RustSlice T)
  := do
  let s : (RustSlice T) ← (Rust_primitives.Mem.replace (RustSlice T) s src);
  (pure s)

@[spec]
def
      Core_models.Slice.Impl.clone_from_slice.spec
      (T : Type)
      [Core_models.Clone.Clone.AssociatedTypes T] [Core_models.Clone.Clone T ]
      (s : (RustSlice T))
      (src : (RustSlice T))
       :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.eq
          (← (Core.Slice.Impl.len T s))
          (← (Core.Slice.Impl.len T src))))
      (ensures := fun _ => pure True)
      (Core_models.Slice.Impl.clone_from_slice
        (T : Type)
        [Core_models.Clone.Clone.AssociatedTypes T] [Core_models.Clone.Clone T ]
        (s : (RustSlice T))
        (src : (RustSlice T))
        ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Slice.Impl.clone_from_slice] <;> try grind
}

def Core_models.Slice.Impl.split_at
  (T : Type) (s : (RustSlice T))
  (mid : usize)
  : RustM (Rust_primitives.Hax.Tuple2 (RustSlice T) (RustSlice T))
  := do
  (Rust_primitives.Slice.slice_split_at T s mid)

@[spec]
def
      Core_models.Slice.Impl.split_at.spec
      (T : Type) (s : (RustSlice T))
      (mid : usize)
       :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.le mid (← (Core.Slice.Impl.len T s))))
      (ensures := fun _ => pure True)
      (Core_models.Slice.Impl.split_at
        (T : Type) (s : (RustSlice T))
        (mid : usize)
        ) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Core_models.Slice.Impl.split_at] <;> try grind
}

def Core_models.Slice.Impl.split_at_checked
  (T : Type) (s : (RustSlice T))
  (mid : usize)
  : RustM
  (Core_models.Option.Option
    (Rust_primitives.Hax.Tuple2 (RustSlice T) (RustSlice T)))
  := do
  if
  (← (Rust_primitives.Hax.Machine_int.le mid (← (Core.Slice.Impl.len T s))))
  then
    (pure (Core_models.Option.Option.Some
      (← (Core_models.Slice.Impl.split_at T s mid))))
  else
    (pure Core_models.Option.Option.None)

structure Core_models.Str.Error.Utf8Error where


opaque Core_models.Str.Converts.from_utf8
  (s : (RustSlice u8))
  : RustM (Core_models.Result.Result String Core_models.Str.Error.Utf8Error)


structure Core_models.Str.Iter.Split (T : Type) where
  _0 : T

class Core_models.Convert.TryInto.AssociatedTypes (Self : Type) (T : Type) where
  Error : Type

attribute [reducible] Core_models.Convert.TryInto.AssociatedTypes.Error

abbrev Core_models.Convert.TryInto.Error :=
  Core_models.Convert.TryInto.AssociatedTypes.Error

class Core_models.Convert.TryInto
  (Self : Type)
  (T : Type)
  [associatedTypes : outParam (Core_models.Convert.TryInto.AssociatedTypes (Self
      : Type) (T : Type))]
  where
  try_into (Self T)
    :
    (Self -> RustM (Core_models.Result.Result T associatedTypes.Error))

class Core_models.Convert.TryFrom.AssociatedTypes (Self : Type) (T : Type) where
  Error : Type

attribute [reducible] Core_models.Convert.TryFrom.AssociatedTypes.Error

abbrev Core_models.Convert.TryFrom.Error :=
  Core_models.Convert.TryFrom.AssociatedTypes.Error

class Core_models.Convert.TryFrom
  (Self : Type)
  (T : Type)
  [associatedTypes : outParam (Core_models.Convert.TryFrom.AssociatedTypes (Self
      : Type) (T : Type))]
  where
  try_from (Self T)
    :
    (T -> RustM (Core_models.Result.Result Self associatedTypes.Error))

class Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Self : Type)
  where
  Item : Type

attribute [reducible]
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes.Item

abbrev Core_models.Iter.Traits.Iterator.Iterator.Item :=
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes.Item

class Core_models.Iter.Traits.Iterator.Iterator
  (Self : Type)
  [associatedTypes : outParam
    (Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Self : Type))]
  where
  next (Self)
    :
    (Self
    -> RustM (Rust_primitives.Hax.Tuple2
      Self
      (Core_models.Option.Option associatedTypes.Item)))

class Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes (Self : Type)
  where
  IntoIter : Type

attribute [reducible]
  Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes.IntoIter

abbrev Core_models.Iter.Traits.Collect.IntoIterator.IntoIter :=
  Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes.IntoIter

class Core_models.Iter.Traits.Collect.IntoIterator
  (Self : Type)
  [associatedTypes : outParam
    (Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes (Self :
      Type))]
  where
  into_iter (Self) : (Self -> RustM associatedTypes.IntoIter)

class Core_models.Ops.Arith.Add.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Arith.Add.AssociatedTypes.Output

abbrev Core_models.Ops.Arith.Add.Output :=
  Core_models.Ops.Arith.Add.AssociatedTypes.Output

class Core_models.Ops.Arith.Add
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.Add.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  add (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Arith.Sub.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Arith.Sub.AssociatedTypes.Output

abbrev Core_models.Ops.Arith.Sub.Output :=
  Core_models.Ops.Arith.Sub.AssociatedTypes.Output

class Core_models.Ops.Arith.Sub
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.Sub.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  sub (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Arith.Mul.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Arith.Mul.AssociatedTypes.Output

abbrev Core_models.Ops.Arith.Mul.Output :=
  Core_models.Ops.Arith.Mul.AssociatedTypes.Output

class Core_models.Ops.Arith.Mul
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.Mul.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  mul (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Arith.Div.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Arith.Div.AssociatedTypes.Output

abbrev Core_models.Ops.Arith.Div.Output :=
  Core_models.Ops.Arith.Div.AssociatedTypes.Output

class Core_models.Ops.Arith.Div
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.Div.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  div (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Arith.Neg.AssociatedTypes (Self : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Arith.Neg.AssociatedTypes.Output

abbrev Core_models.Ops.Arith.Neg.Output :=
  Core_models.Ops.Arith.Neg.AssociatedTypes.Output

class Core_models.Ops.Arith.Neg
  (Self : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.Neg.AssociatedTypes (Self :
      Type))]
  where
  neg (Self) : (Self -> RustM associatedTypes.Output)

class Core_models.Ops.Arith.Rem.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Arith.Rem.AssociatedTypes.Output

abbrev Core_models.Ops.Arith.Rem.Output :=
  Core_models.Ops.Arith.Rem.AssociatedTypes.Output

class Core_models.Ops.Arith.Rem
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.Rem.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  rem (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Arith.RemAssign.AssociatedTypes (Self : Type) (Rhs : Type)
  where
  Output : Type

attribute [reducible] Core_models.Ops.Arith.RemAssign.AssociatedTypes.Output

abbrev Core_models.Ops.Arith.RemAssign.Output :=
  Core_models.Ops.Arith.RemAssign.AssociatedTypes.Output

class Core_models.Ops.Arith.RemAssign
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Arith.RemAssign.AssociatedTypes
      (Self : Type) (Rhs : Type))]
  where
  rem_assign (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Bit.Shr.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Bit.Shr.AssociatedTypes.Output

abbrev Core_models.Ops.Bit.Shr.Output :=
  Core_models.Ops.Bit.Shr.AssociatedTypes.Output

class Core_models.Ops.Bit.Shr
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Bit.Shr.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  shr (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Bit.Shl.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Bit.Shl.AssociatedTypes.Output

abbrev Core_models.Ops.Bit.Shl.Output :=
  Core_models.Ops.Bit.Shl.AssociatedTypes.Output

class Core_models.Ops.Bit.Shl
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Bit.Shl.AssociatedTypes (Self :
      Type) (Rhs : Type))]
  where
  shl (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Bit.BitXor.AssociatedTypes (Self : Type) (Rhs : Type)
  where
  Output : Type

attribute [reducible] Core_models.Ops.Bit.BitXor.AssociatedTypes.Output

abbrev Core_models.Ops.Bit.BitXor.Output :=
  Core_models.Ops.Bit.BitXor.AssociatedTypes.Output

class Core_models.Ops.Bit.BitXor
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Bit.BitXor.AssociatedTypes (Self
      : Type) (Rhs : Type))]
  where
  bitxor (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Bit.BitAnd.AssociatedTypes (Self : Type) (Rhs : Type)
  where
  Output : Type

attribute [reducible] Core_models.Ops.Bit.BitAnd.AssociatedTypes.Output

abbrev Core_models.Ops.Bit.BitAnd.Output :=
  Core_models.Ops.Bit.BitAnd.AssociatedTypes.Output

class Core_models.Ops.Bit.BitAnd
  (Self : Type)
  (Rhs : Type)
  [associatedTypes : outParam (Core_models.Ops.Bit.BitAnd.AssociatedTypes (Self
      : Type) (Rhs : Type))]
  where
  bitand (Self Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Core_models.Ops.Index.Index.AssociatedTypes (Self : Type) (Idx : Type)
  where
  Output : Type

attribute [reducible] Core_models.Ops.Index.Index.AssociatedTypes.Output

abbrev Core_models.Ops.Index.Index.Output :=
  Core_models.Ops.Index.Index.AssociatedTypes.Output

class Core_models.Ops.Index.Index
  (Self : Type)
  (Idx : Type)
  [associatedTypes : outParam (Core_models.Ops.Index.Index.AssociatedTypes (Self
      : Type) (Idx : Type))]
  where
  index (Self Idx) : (Self -> Idx -> RustM associatedTypes.Output)

class Core_models.Ops.Function.FnOnce.AssociatedTypes (Self : Type) (Args :
  Type) where
  Output : Type

attribute [reducible] Core_models.Ops.Function.FnOnce.AssociatedTypes.Output

abbrev Core_models.Ops.Function.FnOnce.Output :=
  Core_models.Ops.Function.FnOnce.AssociatedTypes.Output

class Core_models.Ops.Function.FnOnce
  (Self : Type)
  (Args : Type)
  [associatedTypes : outParam (Core_models.Ops.Function.FnOnce.AssociatedTypes
      (Self : Type) (Args : Type))]
  where
  call_once (Self Args) : (Self -> Args -> RustM associatedTypes.Output)

class Core_models.Ops.Try_trait.Try.AssociatedTypes (Self : Type) where
  Output : Type
  Residual : Type

attribute [reducible] Core_models.Ops.Try_trait.Try.AssociatedTypes.Output

attribute [reducible] Core_models.Ops.Try_trait.Try.AssociatedTypes.Residual

abbrev Core_models.Ops.Try_trait.Try.Output :=
  Core_models.Ops.Try_trait.Try.AssociatedTypes.Output

abbrev Core_models.Ops.Try_trait.Try.Residual :=
  Core_models.Ops.Try_trait.Try.AssociatedTypes.Residual

class Core_models.Ops.Try_trait.Try
  (Self : Type)
  [associatedTypes : outParam (Core_models.Ops.Try_trait.Try.AssociatedTypes
      (Self : Type))]
  where
  from_output (Self) : (associatedTypes.Output -> RustM Self)
  branch (Self)
    :
    (Self
    -> RustM (Core_models.Ops.Control_flow.ControlFlow
      associatedTypes.Residual
      associatedTypes.Output))

class Core_models.Ops.Deref.Deref.AssociatedTypes (Self : Type) where
  Target : Type

attribute [reducible] Core_models.Ops.Deref.Deref.AssociatedTypes.Target

abbrev Core_models.Ops.Deref.Deref.Target :=
  Core_models.Ops.Deref.Deref.AssociatedTypes.Target

class Core_models.Ops.Deref.Deref
  (Self : Type)
  [associatedTypes : outParam (Core_models.Ops.Deref.Deref.AssociatedTypes (Self
      : Type))]
  where
  deref (Self) : (Self -> RustM associatedTypes.Target)

class Core_models.Slice.SliceIndex.AssociatedTypes (Self : Type) (T : Type)
  where
  Output : Type

attribute [reducible] Core_models.Slice.SliceIndex.AssociatedTypes.Output

abbrev Core_models.Slice.SliceIndex.Output :=
  Core_models.Slice.SliceIndex.AssociatedTypes.Output

class Core_models.Slice.SliceIndex
  (Self : Type)
  (T : Type)
  [associatedTypes : outParam (Core_models.Slice.SliceIndex.AssociatedTypes
      (Self : Type) (T : Type))]
  where
  get (Self T)
    :
    (Self -> T -> RustM (Core_models.Option.Option associatedTypes.Output))

class Core_models.Str.Traits.FromStr.AssociatedTypes (Self : Type) where
  Err : Type

attribute [reducible] Core_models.Str.Traits.FromStr.AssociatedTypes.Err

abbrev Core_models.Str.Traits.FromStr.Err :=
  Core_models.Str.Traits.FromStr.AssociatedTypes.Err

class Core_models.Str.Traits.FromStr
  (Self : Type)
  [associatedTypes : outParam (Core_models.Str.Traits.FromStr.AssociatedTypes
      (Self : Type))]
  where
  from_str (Self)
    :
    (String -> RustM (Core_models.Result.Result Self associatedTypes.Err))

def Core_models.Array.Impl_23.map
  (T : Type)
  (N : usize)
  (F : Type)
  (U : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  (s : (RustArray T N))
  (f : (T -> RustM U))
  : RustM (RustArray U N)
  := do
  (Rust_primitives.Slice.array_map T U (N) (T -> RustM U) s f)

def Core_models.Array.from_fn
  (T : Type)
  (N : usize)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F usize]
  [Core_models.Ops.Function.FnOnce
    F
    usize
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F usize
      by infer_instance
      with Output := T})]
  (f : (usize -> RustM T))
  : RustM (RustArray T N)
  := do
  (Rust_primitives.Slice.array_from_fn T (N) (usize -> RustM T) f)

@[reducible] instance Core_models.Array.Impl_24.AssociatedTypes
  (T : Type) (N : usize) :
  Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes (RustArray T N)
  where
  IntoIter := (Core_models.Array.Iter.IntoIter T (N))

instance Core_models.Array.Impl_24 (T : Type) (N : usize) :
  Core_models.Iter.Traits.Collect.IntoIterator (RustArray T N)
  where
  into_iter := fun (self : (RustArray T N)) => do
    (pure (Core_models.Array.Iter.IntoIter.mk
      (← (Rust_primitives.Sequence.seq_from_array T (N) self))))

@[reducible] instance Core_models.Array.Impl_25.AssociatedTypes
  (T : Type) (N : usize) :
  Core_models.Ops.Index.Index.AssociatedTypes (RustArray T N) usize
  where
  Output := T

instance Core_models.Array.Impl_25 (T : Type) (N : usize) :
  Core_models.Ops.Index.Index (RustArray T N) usize
  where
  index := fun (self : (RustArray T N)) (i : usize) => do
    (Rust_primitives.Slice.array_index T (N) self i)

@[reducible] instance Core_models.Array.Impl_26.AssociatedTypes
  (T : Type) (N : usize) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustArray T N)
  (Core_models.Ops.Range.Range usize)
  where
  Output := (RustSlice T)

instance Core_models.Array.Impl_26 (T : Type) (N : usize) :
  Core_models.Ops.Index.Index
  (RustArray T N)
  (Core_models.Ops.Range.Range usize)
  where
  index :=
    fun (self : (RustArray T N)) (i : (Core_models.Ops.Range.Range usize)) => do
    (Rust_primitives.Slice.array_slice T (N)
      self
      (Core_models.Ops.Range.Range.start i)
      (Core_models.Ops.Range.Range._end i))

@[reducible] instance Core_models.Array.Impl_27.AssociatedTypes
  (T : Type) (N : usize) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustArray T N)
  (Core_models.Ops.Range.RangeTo usize)
  where
  Output := (RustSlice T)

instance Core_models.Array.Impl_27 (T : Type) (N : usize) :
  Core_models.Ops.Index.Index
  (RustArray T N)
  (Core_models.Ops.Range.RangeTo usize)
  where
  index :=
    fun
      (self : (RustArray T N)) (i : (Core_models.Ops.Range.RangeTo usize)) => do
    (Rust_primitives.Slice.array_slice T (N)
      self
      (0 : usize)
      (Core_models.Ops.Range.RangeTo._end i))

@[reducible] instance Core_models.Array.Impl_28.AssociatedTypes
  (T : Type) (N : usize) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustArray T N)
  (Core_models.Ops.Range.RangeFrom usize)
  where
  Output := (RustSlice T)

instance Core_models.Array.Impl_28 (T : Type) (N : usize) :
  Core_models.Ops.Index.Index
  (RustArray T N)
  (Core_models.Ops.Range.RangeFrom usize)
  where
  index :=
    fun
      (self : (RustArray T N)) (i : (Core_models.Ops.Range.RangeFrom usize)) =>
      do
    (Rust_primitives.Slice.array_slice T (N)
      self
      (Core_models.Ops.Range.RangeFrom.start i)
      N)

@[reducible] instance Core_models.Array.Impl_29.AssociatedTypes
  (T : Type) (N : usize) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustArray T N)
  Core_models.Ops.Range.RangeFull
  where
  Output := (RustSlice T)

instance Core_models.Array.Impl_29 (T : Type) (N : usize) :
  Core_models.Ops.Index.Index (RustArray T N) Core_models.Ops.Range.RangeFull
  where
  index :=
    fun (self : (RustArray T N)) (i : Core_models.Ops.Range.RangeFull) => do
    (Rust_primitives.Slice.array_slice T (N) self (0 : usize) N)

@[reducible] instance Core_models.Array.Iter.Impl.AssociatedTypes
  (T : Type) (N : usize) :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Array.Iter.IntoIter T (N))
  where
  Item := T

instance Core_models.Array.Iter.Impl (T : Type) (N : usize) :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Array.Iter.IntoIter T (N))
  where
  next := fun (self : (Core_models.Array.Iter.IntoIter T (N))) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← (Rust_primitives.Sequence.seq_len T
          (Core_models.Array.Iter.IntoIter._0 self)))
        (0 : usize))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : T ←
          (Rust_primitives.Sequence.seq_first T
            (Core_models.Array.Iter.IntoIter._0 self));
        let self : (Core_models.Array.Iter.IntoIter T (N)) :=
          {self
          with _0 := (← (Rust_primitives.Sequence.seq_slice T
            (Core_models.Array.Iter.IntoIter._0 self)
            (1 : usize)
            (← (Rust_primitives.Sequence.seq_len T
              (Core_models.Array.Iter.IntoIter._0 self)))))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Convert.Impl_1.AssociatedTypes
  (T : Type)
  (U : Type)
  [Core_models.Convert.From.AssociatedTypes U T] [Core_models.Convert.From U T ]
  :
  Core_models.Convert.TryFrom.AssociatedTypes U T
  where
  Error := Core_models.Convert.Infallible

instance Core_models.Convert.Impl_1
  (T : Type)
  (U : Type)
  [Core_models.Convert.From.AssociatedTypes U T] [Core_models.Convert.From U T ]
  :
  Core_models.Convert.TryFrom U T
  where
  try_from := fun (x : T) => do
    (pure (Core_models.Result.Result.Ok
      (← (Core_models.Convert.From.__from U T x))))

@[reducible] instance Core_models.Convert.Impl_2.AssociatedTypes
  (T : Type)
  (N : usize)
  [Core.Marker.Copy.AssociatedTypes T] [Core.Marker.Copy T ]
  :
  Core_models.Convert.TryFrom.AssociatedTypes (RustArray T N) (RustSlice T)
  where
  Error := Core_models.Array.TryFromSliceError

instance Core_models.Convert.Impl_2
  (T : Type)
  (N : usize)
  [Core.Marker.Copy.AssociatedTypes T] [Core.Marker.Copy T ]
  :
  Core_models.Convert.TryFrom (RustArray T N) (RustSlice T)
  where
  try_from := fun (x : (RustSlice T)) => do
    if
    (← (Rust_primitives.Hax.Machine_int.eq (← (Core.Slice.Impl.len T x)) N))
    then
      (pure (Core_models.Result.Result.Ok
        (← (Rust_primitives.Slice.array_from_fn T (N) (usize -> RustM T)
          (fun i => (do
            (Rust_primitives.Slice.slice_index T x i) : RustM T))))))
    else
      (pure (Core_models.Result.Result.Err
        Core_models.Array.TryFromSliceError.mk))

@[reducible] instance Core_models.Convert.Impl_3.AssociatedTypes
  (T : Type)
  (U : Type)
  [Core_models.Convert.TryFrom.AssociatedTypes U T]
  [Core_models.Convert.TryFrom U T ]
  :
  Core_models.Convert.TryInto.AssociatedTypes T U
  where
  Error := (Core_models.Convert.TryFrom.Error U T)

instance Core_models.Convert.Impl_3
  (T : Type)
  (U : Type)
  [Core_models.Convert.TryFrom.AssociatedTypes U T]
  [Core_models.Convert.TryFrom U T ]
  :
  Core_models.Convert.TryInto T U
  where
  try_into := fun (self : T) => do
    (Core_models.Convert.TryFrom.try_from U T self)

@[reducible] instance Core_models.Convert.Impl_36.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u8 u16
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_36 : Core_models.Convert.TryFrom u8 u16 where
  try_from := fun (x : u16) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_37.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u8 u32
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_37 : Core_models.Convert.TryFrom u8 u32 where
  try_from := fun (x : u32) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_38.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u16 u32
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_38 : Core_models.Convert.TryFrom u16 u32 where
  try_from := fun (x : u32) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_39.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u8 u64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_39 : Core_models.Convert.TryFrom u8 u64 where
  try_from := fun (x : u64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_40.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u16 u64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_40 : Core_models.Convert.TryFrom u16 u64 where
  try_from := fun (x : u64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_41.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u32 u64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_41 : Core_models.Convert.TryFrom u32 u64 where
  try_from := fun (x : u64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_8.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_8.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_42.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes usize u64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_42 :
  Core_models.Convert.TryFrom usize u64
  where
  try_from := fun (x : u64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_11.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_11.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_43.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u8 u128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_43 : Core_models.Convert.TryFrom u8 u128 where
  try_from := fun (x : u128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_44.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u16 u128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_44 :
  Core_models.Convert.TryFrom u16 u128
  where
  try_from := fun (x : u128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_45.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u32 u128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_45 :
  Core_models.Convert.TryFrom u32 u128
  where
  try_from := fun (x : u128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_8.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_8.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_46.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u64 u128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_46 :
  Core_models.Convert.TryFrom u64 u128
  where
  try_from := fun (x : u128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_9.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_9.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_47.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes usize u128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_47 :
  Core_models.Convert.TryFrom usize u128
  where
  try_from := fun (x : u128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_11.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_11.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_48.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u8 usize
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_48 :
  Core_models.Convert.TryFrom u8 usize
  where
  try_from := fun (x : usize) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_6.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_49.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u16 usize
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_49 :
  Core_models.Convert.TryFrom u16 usize
  where
  try_from := fun (x : usize) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_7.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_50.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes u32 usize
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_50 :
  Core_models.Convert.TryFrom u32 usize
  where
  try_from := fun (x : usize) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_8.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_8.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_51.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i8 i16
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_51 : Core_models.Convert.TryFrom i8 i16 where
  try_from := fun (x : i16) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_52.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i8 i32
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_52 : Core_models.Convert.TryFrom i8 i32 where
  try_from := fun (x : i32) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_53.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i16 i32
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_53 : Core_models.Convert.TryFrom i16 i32 where
  try_from := fun (x : i32) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_54.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i8 i64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_54 : Core_models.Convert.TryFrom i8 i64 where
  try_from := fun (x : i64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_55.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i16 i64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_55 : Core_models.Convert.TryFrom i16 i64 where
  try_from := fun (x : i64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_56.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i32 i64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_56 : Core_models.Convert.TryFrom i32 i64 where
  try_from := fun (x : i64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_2.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_2.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_57.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes isize i64
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_57 :
  Core_models.Convert.TryFrom isize i64
  where
  try_from := fun (x : i64) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_5.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_5.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_58.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i8 i128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_58 : Core_models.Convert.TryFrom i8 i128 where
  try_from := fun (x : i128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_59.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i16 i128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_59 :
  Core_models.Convert.TryFrom i16 i128
  where
  try_from := fun (x : i128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_60.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i32 i128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_60 :
  Core_models.Convert.TryFrom i32 i128
  where
  try_from := fun (x : i128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_2.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_2.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_61.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i64 i128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_61 :
  Core_models.Convert.TryFrom i64 i128
  where
  try_from := fun (x : i128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_3.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_3.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_62.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes isize i128
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_62 :
  Core_models.Convert.TryFrom isize i128
  where
  try_from := fun (x : i128) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_5.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_5.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_63.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i8 isize
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_63 :
  Core_models.Convert.TryFrom i8 isize
  where
  try_from := fun (x : isize) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_64.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i16 isize
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_64 :
  Core_models.Convert.TryFrom i16 isize
  where
  try_from := fun (x : isize) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_1.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Convert.Impl_65.AssociatedTypes :
  Core_models.Convert.TryFrom.AssociatedTypes i32 isize
  where
  Error := Core_models.Num.Error.TryFromIntError

instance Core_models.Convert.Impl_65 :
  Core_models.Convert.TryFrom i32 isize
  where
  try_from := fun (x : isize) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.gt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_2.MAX))))
      ||? (← (Rust_primitives.Hax.Machine_int.lt
        x
        (← (Rust_primitives.Hax.cast_op Core.Num.Impl_2.MIN)))))) then
      (pure (Core_models.Result.Result.Err
        (Core_models.Num.Error.TryFromIntError.mk
          Rust_primitives.Hax.Tuple0.mk)))
    else
      (pure (Core_models.Result.Result.Ok (← (Rust_primitives.Hax.cast_op x))))

@[reducible] instance Core_models.Iter.Traits.Iterator.Impl_1.AssociatedTypes
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes I
  where
  IntoIter := I

instance Core_models.Iter.Traits.Iterator.Impl_1
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Collect.IntoIterator I
  where
  into_iter := fun (self : I) => do (pure self)

class Core_models.Iter.Traits.Collect.FromIterator.AssociatedTypes (Self : Type)
  (A : Type) where

class Core_models.Iter.Traits.Collect.FromIterator
  (Self : Type)
  (A : Type)
  [associatedTypes : outParam
    (Core_models.Iter.Traits.Collect.FromIterator.AssociatedTypes (Self : Type)
      (A : Type))]
  where
  from_iter (Self A)
    (T : Type)
    [Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes T]
    [Core_models.Iter.Traits.Collect.IntoIterator T ]
    :
    (T -> RustM Self)

@[reducible] instance Core_models.Iter.Adapters.Enumerate.Impl_1.AssociatedTypes
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Iter.Adapters.Enumerate.Enumerate I)
  where
  Item := (Rust_primitives.Hax.Tuple2
    usize
    (Core_models.Iter.Traits.Iterator.Iterator.Item I))

instance Core_models.Iter.Adapters.Enumerate.Impl_1
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Iter.Adapters.Enumerate.Enumerate I)
  where
  next := fun (self : (Core_models.Iter.Adapters.Enumerate.Enumerate I)) => do
    let ⟨tmp0, out⟩ ←
      (Core_models.Iter.Traits.Iterator.Iterator.next
        I (Core_models.Iter.Adapters.Enumerate.Enumerate.iter self));
    let self : (Core_models.Iter.Adapters.Enumerate.Enumerate I) :=
      {self with iter := tmp0};
    let ⟨self, hax_temp_output⟩ ←
      match out with
        | (Core_models.Option.Option.Some a)
          =>
            let i : usize :=
              (Core_models.Iter.Adapters.Enumerate.Enumerate.count self);
            let _ ←
              (Hax_lib.assume
                (← (Hax_lib.Prop.Constructors.from_bool
                  (← (Rust_primitives.Hax.Machine_int.lt
                    (Core_models.Iter.Adapters.Enumerate.Enumerate.count self)
                    Core.Num.Impl_11.MAX)))));
            let self : (Core_models.Iter.Adapters.Enumerate.Enumerate I) :=
              {self
              with count := (←
              ((Core_models.Iter.Adapters.Enumerate.Enumerate.count self)
                +? (1 : usize)))};
            (pure (Rust_primitives.Hax.Tuple2.mk
              self
              (Core_models.Option.Option.Some
                (Rust_primitives.Hax.Tuple2.mk i a))))
        | (Core_models.Option.Option.None )
          =>
            (pure (Rust_primitives.Hax.Tuple2.mk
              self Core_models.Option.Option.None));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Iter.Adapters.Step_by.Impl_1.AssociatedTypes
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Iter.Adapters.Step_by.StepBy I)
  where

instance Core_models.Iter.Adapters.Step_by.Impl_1
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Iter.Adapters.Step_by.StepBy I)
  where

@[reducible] instance Core_models.Iter.Adapters.Map.Impl_1.AssociatedTypes
  (I : Type)
  (O : Type)
  (F : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := O})]
  :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Iter.Adapters.Map.Map I F)
  where
  Item := O

instance Core_models.Iter.Adapters.Map.Impl_1
  (I : Type)
  (O : Type)
  (F : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := O})]
  :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Iter.Adapters.Map.Map I F)
  where
  next := fun (self : (Core_models.Iter.Adapters.Map.Map I F)) => do
    let ⟨tmp0, out⟩ ←
      (Core_models.Iter.Traits.Iterator.Iterator.next
        I (Core_models.Iter.Adapters.Map.Map.iter self));
    let self : (Core_models.Iter.Adapters.Map.Map I F) :=
      {self with iter := tmp0};
    let hax_temp_output : (Core_models.Option.Option O) ←
      match out with
        | (Core_models.Option.Option.Some v)
          =>
            (pure (Core_models.Option.Option.Some
              (← (Core_models.Ops.Function.FnOnce.call_once
                F
                (Core_models.Iter.Traits.Iterator.Iterator.Item I)
                (Core_models.Iter.Adapters.Map.Map.f self)
                v))))
        | (Core_models.Option.Option.None )
          => (pure Core_models.Option.Option.None);
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Iter.Adapters.Take.Impl_1.AssociatedTypes
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Iter.Adapters.Take.Take I)
  where
  Item := (Core_models.Iter.Traits.Iterator.Iterator.Item I)

instance Core_models.Iter.Adapters.Take.Impl_1
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Iter.Adapters.Take.Take I)
  where
  next := fun (self : (Core_models.Iter.Adapters.Take.Take I)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ne
        (Core_models.Iter.Adapters.Take.Take.n self)
        (0 : usize))) then
        let self : (Core_models.Iter.Adapters.Take.Take I) :=
          {self
          with n := (← ((Core_models.Iter.Adapters.Take.Take.n self)
            -? (1 : usize)))};
        let ⟨tmp0, out⟩ ←
          (Core_models.Iter.Traits.Iterator.Iterator.next
            I (Core_models.Iter.Adapters.Take.Take.iter self));
        let self : (Core_models.Iter.Adapters.Take.Take I) :=
          {self with iter := tmp0};
        (pure (Rust_primitives.Hax.Tuple2.mk self out))
      else
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

def Core_models.Iter.Adapters.Flat_map.Impl.new
  (I : Type)
  (U : Type)
  (F : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes U]
  [Core_models.Iter.Traits.Iterator.Iterator U ]
  [Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := U})]
  (it : I)
  (f : F)
  : RustM (Core_models.Iter.Adapters.Flat_map.FlatMap I U F)
  := do
  (pure (Core_models.Iter.Adapters.Flat_map.FlatMap.mk
    (it := it) (f := f) (current := Core_models.Option.Option.None)))

@[reducible] instance Core_models.Iter.Adapters.Flat_map.Impl_1.AssociatedTypes
  (I : Type)
  (U : Type)
  (F : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes U]
  [Core_models.Iter.Traits.Iterator.Iterator U ]
  [Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := U})]
  :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Iter.Adapters.Flat_map.FlatMap I U F)
  where

instance Core_models.Iter.Adapters.Flat_map.Impl_1
  (I : Type)
  (U : Type)
  (F : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes U]
  [Core_models.Iter.Traits.Iterator.Iterator U ]
  [Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := U})]
  :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Iter.Adapters.Flat_map.FlatMap I U F)
  where

structure Core_models.Iter.Adapters.Flatten.Flatten
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Iter.Traits.Iterator.Iterator
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    ]
  where
  it : I
  current : (Core_models.Option.Option
      (Core_models.Iter.Traits.Iterator.Iterator.Item I))

def Core_models.Iter.Adapters.Flatten.Impl.new
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Iter.Traits.Iterator.Iterator
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    ]
  (it : I)
  : RustM (Core_models.Iter.Adapters.Flatten.Flatten I)
  := do
  (pure (Core_models.Iter.Adapters.Flatten.Flatten.mk
    (it := it) (current := Core_models.Option.Option.None)))

@[reducible] instance Core_models.Iter.Adapters.Flatten.Impl_1.AssociatedTypes
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Iter.Traits.Iterator.Iterator
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    ]
  :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Iter.Adapters.Flatten.Flatten I)
  where

instance Core_models.Iter.Adapters.Flatten.Impl_1
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [Core_models.Iter.Traits.Iterator.Iterator
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    ]
  :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Iter.Adapters.Flatten.Flatten I)
  where

def Core_models.Iter.Adapters.Zip.Impl.new
  (I1 : Type)
  (I2 : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I1]
  [Core_models.Iter.Traits.Iterator.Iterator I1 ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I2]
  [Core_models.Iter.Traits.Iterator.Iterator I2 ]
  (it1 : I1)
  (it2 : I2)
  : RustM (Core_models.Iter.Adapters.Zip.Zip I1 I2)
  := do
  (pure (Core_models.Iter.Adapters.Zip.Zip.mk (it1 := it1) (it2 := it2)))

@[reducible] instance Core_models.Iter.Traits.Iterator.Impl.AssociatedTypes
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.IteratorMethods.AssociatedTypes I
  where

instance Core_models.Iter.Traits.Iterator.Impl
  (I : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I]
  [Core_models.Iter.Traits.Iterator.Iterator I ]
  :
  Core_models.Iter.Traits.Iterator.IteratorMethods I
  where
  fold :=
    fun
      (B : Type)
      (F : Type)
      [Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Rust_primitives.Hax.Tuple2
          B
          (Core_models.Iter.Traits.Iterator.Iterator.Item I))]
      [Core_models.Ops.Function.FnOnce
        F
        (Rust_primitives.Hax.Tuple2
          B
          (Core_models.Iter.Traits.Iterator.Iterator.Item I))
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Rust_primitives.Hax.Tuple2
              B
              (Core_models.Iter.Traits.Iterator.Iterator.Item I))
          by infer_instance
          with Output := B})]
      (self : I) (init : B) (f : F) => do
    (pure init)
  enumerate := fun (self : I) => do
    (Core_models.Iter.Adapters.Enumerate.Impl.new I self)
  step_by := fun (self : I) (step : usize) => do
    (Core_models.Iter.Adapters.Step_by.Impl.new I self step)
  map :=
    fun
      (O : Type)
      (F : Type)
      [Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
      [Core_models.Ops.Function.FnOnce
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Core_models.Iter.Traits.Iterator.Iterator.Item I)
          by infer_instance
          with Output := O})]
      (self : I) (f : F) => do
    (Core_models.Iter.Adapters.Map.Impl.new I F self f)
  all :=
    fun
      (F : Type)
      [Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
      [Core_models.Ops.Function.FnOnce
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Core_models.Iter.Traits.Iterator.Iterator.Item I)
          by infer_instance
          with Output := Bool})]
      (self : I) (f : F) => do
    (pure true)
  take := fun (self : I) (n : usize) => do
    (Core_models.Iter.Adapters.Take.Impl.new I self n)
  flat_map :=
    fun
      (U : Type)
      (F : Type)
      [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes U]
      [Core_models.Iter.Traits.Iterator.Iterator U ]
      [Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
      [Core_models.Ops.Function.FnOnce
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Core_models.Iter.Traits.Iterator.Iterator.Item I)
          by infer_instance
          with Output := U})]
      (self : I) (f : F) => do
    (Core_models.Iter.Adapters.Flat_map.Impl.new I U F self f)
  flatten :=
    fun
      [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
      [Core_models.Iter.Traits.Iterator.Iterator
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
        ]
      (self : I) => do
    (Core_models.Iter.Adapters.Flatten.Impl.new I self)
  zip :=
    fun
      (I2 : Type)
      [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I2]
      [Core_models.Iter.Traits.Iterator.Iterator I2 ]
      (self : I) (it2 : I2) => do
    (Core_models.Iter.Adapters.Zip.Impl.new I I2 self it2)

@[reducible] instance Core_models.Iter.Adapters.Zip.Impl_1.AssociatedTypes
  (I1 : Type)
  (I2 : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I1]
  [Core_models.Iter.Traits.Iterator.Iterator I1 ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I2]
  [Core_models.Iter.Traits.Iterator.Iterator I2 ]
  :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Iter.Adapters.Zip.Zip I1 I2)
  where

instance Core_models.Iter.Adapters.Zip.Impl_1
  (I1 : Type)
  (I2 : Type)
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I1]
  [Core_models.Iter.Traits.Iterator.Iterator I1 ]
  [Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes I2]
  [Core_models.Iter.Traits.Iterator.Iterator I2 ]
  :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Iter.Adapters.Zip.Zip I1 I2)
  where

@[reducible] instance Core_models.Ops.Function.Impl_2.AssociatedTypes
  (Arg : Type) (Out : Type) :
  Core_models.Ops.Function.FnOnce.AssociatedTypes (Arg -> RustM Out) Arg
  where
  Output := Out

instance Core_models.Ops.Function.Impl_2 (Arg : Type) (Out : Type) :
  Core_models.Ops.Function.FnOnce (Arg -> RustM Out) Arg
  where
  call_once := fun (self : (Arg -> RustM Out)) (arg : Arg) => do (self arg)

@[reducible] instance Core_models.Ops.Function.Impl.AssociatedTypes
  (Arg1 : Type) (Arg2 : Type) (Out : Type) :
  Core_models.Ops.Function.FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> RustM Out)
  (Rust_primitives.Hax.Tuple2 Arg1 Arg2)
  where
  Output := Out

instance Core_models.Ops.Function.Impl
  (Arg1 : Type) (Arg2 : Type) (Out : Type) :
  Core_models.Ops.Function.FnOnce
  (Arg1 -> Arg2 -> RustM Out)
  (Rust_primitives.Hax.Tuple2 Arg1 Arg2)
  where
  call_once :=
    fun
      (self : (Arg1 -> Arg2 -> RustM Out))
      (arg : (Rust_primitives.Hax.Tuple2 Arg1 Arg2))
      => do
    (self
      (Rust_primitives.Hax.Tuple2._0 arg)
      (Rust_primitives.Hax.Tuple2._1 arg))

@[reducible] instance Core_models.Ops.Function.Impl_1.AssociatedTypes
  (Arg1 : Type) (Arg2 : Type) (Arg3 : Type) (Out : Type) :
  Core_models.Ops.Function.FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (Rust_primitives.Hax.Tuple3 Arg1 Arg2 Arg3)
  where
  Output := Out

instance Core_models.Ops.Function.Impl_1
  (Arg1 : Type) (Arg2 : Type) (Arg3 : Type) (Out : Type) :
  Core_models.Ops.Function.FnOnce
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (Rust_primitives.Hax.Tuple3 Arg1 Arg2 Arg3)
  where
  call_once :=
    fun
      (self : (Arg1 -> Arg2 -> Arg3 -> RustM Out))
      (arg : (Rust_primitives.Hax.Tuple3 Arg1 Arg2 Arg3))
      => do
    (self
      (Rust_primitives.Hax.Tuple3._0 arg)
      (Rust_primitives.Hax.Tuple3._1 arg)
      (Rust_primitives.Hax.Tuple3._2 arg))

@[reducible] instance Core_models.Ops.Deref.Impl.AssociatedTypes (T : Type) :
  Core_models.Ops.Deref.Deref.AssociatedTypes T
  where
  Target := T

instance Core_models.Ops.Deref.Impl (T : Type) :
  Core_models.Ops.Deref.Deref T
  where
  deref := fun (self : T) => do (pure self)

@[reducible] instance Core_models.Ops.Range.Impl.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range u8)
  where
  Item := u8

instance Core_models.Ops.Range.Impl :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range u8)
  where
  next := fun (self : (Core_models.Ops.Range.Range u8)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : u8 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range u8) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : u8)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_1.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range u16)
  where
  Item := u16

instance Core_models.Ops.Range.Impl_1 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range u16)
  where
  next := fun (self : (Core_models.Ops.Range.Range u16)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : u16 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range u16) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : u16)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_2.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range u32)
  where
  Item := u32

instance Core_models.Ops.Range.Impl_2 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range u32)
  where
  next := fun (self : (Core_models.Ops.Range.Range u32)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : u32 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range u32) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : u32)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_3.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range u64)
  where
  Item := u64

instance Core_models.Ops.Range.Impl_3 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range u64)
  where
  next := fun (self : (Core_models.Ops.Range.Range u64)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : u64 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range u64) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : u64)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_4.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range u128)
  where
  Item := u128

instance Core_models.Ops.Range.Impl_4 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range u128)
  where
  next := fun (self : (Core_models.Ops.Range.Range u128)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : u128 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range u128) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : u128)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_5.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range usize)
  where
  Item := usize

instance Core_models.Ops.Range.Impl_5 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range usize)
  where
  next := fun (self : (Core_models.Ops.Range.Range usize)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : usize := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range usize) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : usize)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_6.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range i8)
  where
  Item := i8

instance Core_models.Ops.Range.Impl_6 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range i8)
  where
  next := fun (self : (Core_models.Ops.Range.Range i8)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : i8 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range i8) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : i8)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_7.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range i16)
  where
  Item := i16

instance Core_models.Ops.Range.Impl_7 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range i16)
  where
  next := fun (self : (Core_models.Ops.Range.Range i16)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : i16 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range i16) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : i16)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_8.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range i32)
  where
  Item := i32

instance Core_models.Ops.Range.Impl_8 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range i32)
  where
  next := fun (self : (Core_models.Ops.Range.Range i32)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : i32 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range i32) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : i32)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_9.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range i64)
  where
  Item := i64

instance Core_models.Ops.Range.Impl_9 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range i64)
  where
  next := fun (self : (Core_models.Ops.Range.Range i64)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : i64 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range i64) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : i64)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_10.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range i128)
  where
  Item := i128

instance Core_models.Ops.Range.Impl_10 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range i128)
  where
  next := fun (self : (Core_models.Ops.Range.Range i128)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : i128 := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range i128) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : i128)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Ops.Range.Impl_11.AssociatedTypes :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Ops.Range.Range isize)
  where
  Item := isize

instance Core_models.Ops.Range.Impl_11 :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Ops.Range.Range isize)
  where
  next := fun (self : (Core_models.Ops.Range.Range isize)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.ge
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : isize := (Core_models.Ops.Range.Range.start self);
        let self : (Core_models.Ops.Range.Range isize) :=
          {self
          with start := (← ((Core_models.Ops.Range.Range.start self)
            +? (1 : isize)))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

def Core_models.Option.Impl.is_some_and
  (T : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := Bool})]
  (self : (Core_models.Option.Option T))
  (f : F)
  : RustM Bool
  := do
  match self with
    | (Core_models.Option.Option.None ) => (pure false)
    | (Core_models.Option.Option.Some x)
      => (Core_models.Ops.Function.FnOnce.call_once F T f x)

def Core_models.Option.Impl.is_none_or
  (T : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := Bool})]
  (self : (Core_models.Option.Option T))
  (f : F)
  : RustM Bool
  := do
  match self with
    | (Core_models.Option.Option.None ) => (pure true)
    | (Core_models.Option.Option.Some x)
      => (Core_models.Ops.Function.FnOnce.call_once F T f x)

def Core_models.Option.Impl.unwrap_or_else
  (T : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F Rust_primitives.Hax.Tuple0]
  [Core_models.Ops.Function.FnOnce
    F
    Rust_primitives.Hax.Tuple0
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        Rust_primitives.Hax.Tuple0
      by infer_instance
      with Output := T})]
  (self : (Core_models.Option.Option T))
  (f : F)
  : RustM T
  := do
  match self with
    | (Core_models.Option.Option.Some x) => (pure x)
    | (Core_models.Option.Option.None )
      =>
        (Core_models.Ops.Function.FnOnce.call_once
          F
          Rust_primitives.Hax.Tuple0 f Rust_primitives.Hax.Tuple0.mk)

def Core_models.Option.Impl.map
  (T : Type)
  (U : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  (self : (Core_models.Option.Option T))
  (f : F)
  : RustM (Core_models.Option.Option U)
  := do
  match self with
    | (Core_models.Option.Option.Some x)
      =>
        (pure (Core_models.Option.Option.Some
          (← (Core_models.Ops.Function.FnOnce.call_once F T f x))))
    | (Core_models.Option.Option.None ) => (pure Core_models.Option.Option.None)

def Core_models.Option.Impl.map_or
  (T : Type)
  (U : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  (self : (Core_models.Option.Option T))
  (default : U)
  (f : F)
  : RustM U
  := do
  match self with
    | (Core_models.Option.Option.Some t)
      => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Core_models.Option.Option.None ) => (pure default)

def Core_models.Option.Impl.map_or_else
  (T : Type)
  (U : Type)
  (D : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  [Core_models.Ops.Function.FnOnce.AssociatedTypes D Rust_primitives.Hax.Tuple0]
  [Core_models.Ops.Function.FnOnce
    D
    Rust_primitives.Hax.Tuple0
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        D
        Rust_primitives.Hax.Tuple0
      by infer_instance
      with Output := U})]
  (self : (Core_models.Option.Option T))
  (default : D)
  (f : F)
  : RustM U
  := do
  match self with
    | (Core_models.Option.Option.Some t)
      => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Core_models.Option.Option.None )
      =>
        (Core_models.Ops.Function.FnOnce.call_once
          D
          Rust_primitives.Hax.Tuple0 default Rust_primitives.Hax.Tuple0.mk)

def Core_models.Option.Impl.map_or_default
  (T : Type)
  (U : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  [Core_models.Default.Default.AssociatedTypes U]
  [Core_models.Default.Default U ]
  (self : (Core_models.Option.Option T))
  (f : F)
  : RustM U
  := do
  match self with
    | (Core_models.Option.Option.Some t)
      => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Core_models.Option.Option.None )
      => (Core_models.Default.Default.default U Rust_primitives.Hax.Tuple0.mk)

def Core_models.Option.Impl.ok_or_else
  (T : Type)
  (E : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F Rust_primitives.Hax.Tuple0]
  [Core_models.Ops.Function.FnOnce
    F
    Rust_primitives.Hax.Tuple0
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        Rust_primitives.Hax.Tuple0
      by infer_instance
      with Output := E})]
  (self : (Core_models.Option.Option T))
  (err : F)
  : RustM (Core_models.Result.Result T E)
  := do
  match self with
    | (Core_models.Option.Option.Some v)
      => (pure (Core_models.Result.Result.Ok v))
    | (Core_models.Option.Option.None )
      =>
        (pure (Core_models.Result.Result.Err
          (← (Core_models.Ops.Function.FnOnce.call_once
            F
            Rust_primitives.Hax.Tuple0 err Rust_primitives.Hax.Tuple0.mk))))

def Core_models.Option.Impl.and_then
  (T : Type)
  (U : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := (Core_models.Option.Option U)})]
  (self : (Core_models.Option.Option T))
  (f : F)
  : RustM (Core_models.Option.Option U)
  := do
  match self with
    | (Core_models.Option.Option.Some x)
      => (Core_models.Ops.Function.FnOnce.call_once F T f x)
    | (Core_models.Option.Option.None ) => (pure Core_models.Option.Option.None)

def Core_models.Result.Impl.map
  (T : Type)
  (E : Type)
  (U : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  (self : (Core_models.Result.Result T E))
  (op : F)
  : RustM (Core_models.Result.Result U E)
  := do
  match self with
    | (Core_models.Result.Result.Ok t)
      =>
        (pure (Core_models.Result.Result.Ok
          (← (Core_models.Ops.Function.FnOnce.call_once F T op t))))
    | (Core_models.Result.Result.Err e)
      => (pure (Core_models.Result.Result.Err e))

def Core_models.Result.Impl.map_or
  (T : Type)
  (E : Type)
  (U : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  (self : (Core_models.Result.Result T E))
  (default : U)
  (f : F)
  : RustM U
  := do
  match self with
    | (Core_models.Result.Result.Ok t)
      => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Core_models.Result.Result.Err _e) => (pure default)

def Core_models.Result.Impl.map_or_else
  (T : Type)
  (E : Type)
  (U : Type)
  (D : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := U})]
  [Core_models.Ops.Function.FnOnce.AssociatedTypes D E]
  [Core_models.Ops.Function.FnOnce
    D
    E
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes D E
      by infer_instance
      with Output := U})]
  (self : (Core_models.Result.Result T E))
  (default : D)
  (f : F)
  : RustM U
  := do
  match self with
    | (Core_models.Result.Result.Ok t)
      => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Core_models.Result.Result.Err e)
      => (Core_models.Ops.Function.FnOnce.call_once D E default e)

def Core_models.Result.Impl.map_err
  (T : Type)
  (E : Type)
  (F : Type)
  (O : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes O E]
  [Core_models.Ops.Function.FnOnce
    O
    E
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes O E
      by infer_instance
      with Output := F})]
  (self : (Core_models.Result.Result T E))
  (op : O)
  : RustM (Core_models.Result.Result T F)
  := do
  match self with
    | (Core_models.Result.Result.Ok t)
      => (pure (Core_models.Result.Result.Ok t))
    | (Core_models.Result.Result.Err e)
      =>
        (pure (Core_models.Result.Result.Err
          (← (Core_models.Ops.Function.FnOnce.call_once O E op e))))

def Core_models.Result.Impl.and_then
  (T : Type)
  (E : Type)
  (U : Type)
  (F : Type)
  [Core_models.Ops.Function.FnOnce.AssociatedTypes F T]
  [Core_models.Ops.Function.FnOnce
    F
    T
    (associatedTypes := {
      show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
      by infer_instance
      with Output := (Core_models.Result.Result U E)})]
  (self : (Core_models.Result.Result T E))
  (op : F)
  : RustM (Core_models.Result.Result U E)
  := do
  match self with
    | (Core_models.Result.Result.Ok t)
      => (Core_models.Ops.Function.FnOnce.call_once F T op t)
    | (Core_models.Result.Result.Err e)
      => (pure (Core_models.Result.Result.Err e))

@[reducible] instance Core_models.Slice.Iter.Impl_2.AssociatedTypes (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Slice.Iter.Iter T)
  where
  Item := T

instance Core_models.Slice.Iter.Impl_2 (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Slice.Iter.Iter T)
  where
  next := fun (self : (Core_models.Slice.Iter.Iter T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← (Rust_primitives.Sequence.seq_len T
          (Core_models.Slice.Iter.Iter._0 self)))
        (0 : usize))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let res : T ←
          (Rust_primitives.Sequence.seq_first T
            (Core_models.Slice.Iter.Iter._0 self));
        let self : (Core_models.Slice.Iter.Iter T) :=
          {self
          with _0 := (← (Rust_primitives.Sequence.seq_slice T
            (Core_models.Slice.Iter.Iter._0 self)
            (1 : usize)
            (← (Rust_primitives.Sequence.seq_len T
              (Core_models.Slice.Iter.Iter._0 self)))))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Slice.Iter.Impl_3.AssociatedTypes (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Slice.Iter.Chunks T)
  where
  Item := (RustSlice T)

instance Core_models.Slice.Iter.Impl_3 (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator (Core_models.Slice.Iter.Chunks T)
  where
  next := fun (self : (Core_models.Slice.Iter.Chunks T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← (Rust_primitives.Slice.slice_length T
          (Core_models.Slice.Iter.Chunks.elements self)))
        (0 : usize))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        if
        (← (Rust_primitives.Hax.Machine_int.lt
          (← (Rust_primitives.Slice.slice_length T
            (Core_models.Slice.Iter.Chunks.elements self)))
          (Core_models.Slice.Iter.Chunks.cs self))) then
          let res : (RustSlice T) :=
            (Core_models.Slice.Iter.Chunks.elements self);
          let self : (Core_models.Slice.Iter.Chunks T) :=
            {self
            with elements := (← (Rust_primitives.Slice.slice_slice T
              (Core_models.Slice.Iter.Chunks.elements self)
              (0 : usize)
              (0 : usize)))};
          (pure (Rust_primitives.Hax.Tuple2.mk
            self (Core_models.Option.Option.Some res)))
        else
          let ⟨res, new_elements⟩ ←
            (Rust_primitives.Slice.slice_split_at T
              (Core_models.Slice.Iter.Chunks.elements self)
              (Core_models.Slice.Iter.Chunks.cs self));
          let self : (Core_models.Slice.Iter.Chunks T) :=
            {self with elements := new_elements};
          (pure (Rust_primitives.Hax.Tuple2.mk
            self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Core_models.Slice.Iter.Impl_4.AssociatedTypes (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
  (Core_models.Slice.Iter.ChunksExact T)
  where
  Item := (RustSlice T)

instance Core_models.Slice.Iter.Impl_4 (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator
  (Core_models.Slice.Iter.ChunksExact T)
  where
  next := fun (self : (Core_models.Slice.Iter.ChunksExact T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.lt
        (← (Rust_primitives.Slice.slice_length T
          (Core_models.Slice.Iter.ChunksExact.elements self)))
        (Core_models.Slice.Iter.ChunksExact.cs self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self Core_models.Option.Option.None))
      else
        let ⟨res, new_elements⟩ ←
          (Rust_primitives.Slice.slice_split_at T
            (Core_models.Slice.Iter.ChunksExact.elements self)
            (Core_models.Slice.Iter.ChunksExact.cs self));
        let self : (Core_models.Slice.Iter.ChunksExact T) :=
          {self with elements := new_elements};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

def Core_models.Slice.Impl.get
  (T : Type)
  (I : Type)
  [Core_models.Slice.SliceIndex.AssociatedTypes I (RustSlice T)]
  [Core_models.Slice.SliceIndex I (RustSlice T) ]
  (s : (RustSlice T))
  (index : I)
  : RustM
  (Core_models.Option.Option
    (Core_models.Slice.SliceIndex.Output I (RustSlice T)))
  := do
  (Core_models.Slice.SliceIndex.get I (RustSlice T) index s)

@[reducible] instance Core_models.Slice.Impl_1.AssociatedTypes (T : Type) :
  Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes (RustSlice T)
  where
  IntoIter := (Core_models.Slice.Iter.Iter T)

instance Core_models.Slice.Impl_1 (T : Type) :
  Core_models.Iter.Traits.Collect.IntoIterator (RustSlice T)
  where
  into_iter := fun (self : (RustSlice T)) => do
    (Core_models.Slice.Impl.iter T self)

@[reducible] instance Core_models.Slice.Impl_2.AssociatedTypes (T : Type) :
  Core_models.Slice.SliceIndex.AssociatedTypes usize (RustSlice T)
  where
  Output := T

instance Core_models.Slice.Impl_2 (T : Type) :
  Core_models.Slice.SliceIndex usize (RustSlice T)
  where
  get := fun (self : usize) (slice : (RustSlice T)) => do
    if
    (← (Rust_primitives.Hax.Machine_int.lt
      self
      (← (Core.Slice.Impl.len T slice)))) then
      (pure (Core_models.Option.Option.Some
        (← (Rust_primitives.Slice.slice_index T slice self))))
    else
      (pure Core_models.Option.Option.None)

@[reducible] instance Core_models.Slice.Impl_3.AssociatedTypes (T : Type) :
  Core_models.Slice.SliceIndex.AssociatedTypes
  Core_models.Ops.Range.RangeFull
  (RustSlice T)
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_3 (T : Type) :
  Core_models.Slice.SliceIndex Core_models.Ops.Range.RangeFull (RustSlice T)
  where
  get :=
    fun (self : Core_models.Ops.Range.RangeFull) (slice : (RustSlice T)) => do
    (pure (Core_models.Option.Option.Some slice))

@[reducible] instance Core_models.Slice.Impl_4.AssociatedTypes (T : Type) :
  Core_models.Slice.SliceIndex.AssociatedTypes
  (Core_models.Ops.Range.RangeFrom usize)
  (RustSlice T)
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_4 (T : Type) :
  Core_models.Slice.SliceIndex
  (Core_models.Ops.Range.RangeFrom usize)
  (RustSlice T)
  where
  get :=
    fun
      (self : (Core_models.Ops.Range.RangeFrom usize))
      (slice : (RustSlice T))
      => do
    if
    (← (Rust_primitives.Hax.Machine_int.lt
      (Core_models.Ops.Range.RangeFrom.start self)
      (← (Core.Slice.Impl.len T slice)))) then
      (pure (Core_models.Option.Option.Some
        (← (Rust_primitives.Slice.slice_slice T
          slice
          (Core_models.Ops.Range.RangeFrom.start self)
          (← (Core.Slice.Impl.len T slice))))))
    else
      (pure Core_models.Option.Option.None)

@[reducible] instance Core_models.Slice.Impl_5.AssociatedTypes (T : Type) :
  Core_models.Slice.SliceIndex.AssociatedTypes
  (Core_models.Ops.Range.RangeTo usize)
  (RustSlice T)
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_5 (T : Type) :
  Core_models.Slice.SliceIndex
  (Core_models.Ops.Range.RangeTo usize)
  (RustSlice T)
  where
  get :=
    fun
      (self : (Core_models.Ops.Range.RangeTo usize)) (slice : (RustSlice T)) =>
      do
    if
    (← (Rust_primitives.Hax.Machine_int.le
      (Core_models.Ops.Range.RangeTo._end self)
      (← (Core.Slice.Impl.len T slice)))) then
      (pure (Core_models.Option.Option.Some
        (← (Rust_primitives.Slice.slice_slice T
          slice
          (0 : usize)
          (Core_models.Ops.Range.RangeTo._end self)))))
    else
      (pure Core_models.Option.Option.None)

@[reducible] instance Core_models.Slice.Impl_6.AssociatedTypes (T : Type) :
  Core_models.Slice.SliceIndex.AssociatedTypes
  (Core_models.Ops.Range.Range usize)
  (RustSlice T)
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_6 (T : Type) :
  Core_models.Slice.SliceIndex (Core_models.Ops.Range.Range usize) (RustSlice T)
  where
  get :=
    fun
      (self : (Core_models.Ops.Range.Range usize)) (slice : (RustSlice T)) => do
    if
    (← ((← (Rust_primitives.Hax.Machine_int.lt
        (Core_models.Ops.Range.Range.start self)
        (Core_models.Ops.Range.Range._end self)))
      &&? (← (Rust_primitives.Hax.Machine_int.le
        (Core_models.Ops.Range.Range._end self)
        (← (Core.Slice.Impl.len T slice)))))) then
      (pure (Core_models.Option.Option.Some
        (← (Rust_primitives.Slice.slice_slice T
          slice
          (Core_models.Ops.Range.Range.start self)
          (Core_models.Ops.Range.Range._end self)))))
    else
      (pure Core_models.Option.Option.None)

@[reducible] instance Core_models.Slice.Impl_7.AssociatedTypes (T : Type) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustSlice T)
  (Core_models.Ops.Range.Range usize)
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_7 (T : Type) :
  Core_models.Ops.Index.Index (RustSlice T) (Core_models.Ops.Range.Range usize)
  where
  index :=
    fun (self : (RustSlice T)) (i : (Core_models.Ops.Range.Range usize)) => do
    (Rust_primitives.Slice.slice_slice T
      self
      (Core_models.Ops.Range.Range.start i)
      (Core_models.Ops.Range.Range._end i))

@[reducible] instance Core_models.Slice.Impl_8.AssociatedTypes (T : Type) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustSlice T)
  (Core_models.Ops.Range.RangeTo usize)
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_8 (T : Type) :
  Core_models.Ops.Index.Index
  (RustSlice T)
  (Core_models.Ops.Range.RangeTo usize)
  where
  index :=
    fun (self : (RustSlice T)) (i : (Core_models.Ops.Range.RangeTo usize)) => do
    (Rust_primitives.Slice.slice_slice T
      self
      (0 : usize)
      (Core_models.Ops.Range.RangeTo._end i))

@[reducible] instance Core_models.Slice.Impl_9.AssociatedTypes (T : Type) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustSlice T)
  (Core_models.Ops.Range.RangeFrom usize)
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_9 (T : Type) :
  Core_models.Ops.Index.Index
  (RustSlice T)
  (Core_models.Ops.Range.RangeFrom usize)
  where
  index :=
    fun
      (self : (RustSlice T)) (i : (Core_models.Ops.Range.RangeFrom usize)) => do
    (Rust_primitives.Slice.slice_slice T
      self
      (Core_models.Ops.Range.RangeFrom.start i)
      (← (Rust_primitives.Slice.slice_length T self)))

@[reducible] instance Core_models.Slice.Impl_10.AssociatedTypes (T : Type) :
  Core_models.Ops.Index.Index.AssociatedTypes
  (RustSlice T)
  Core_models.Ops.Range.RangeFull
  where
  Output := (RustSlice T)

instance Core_models.Slice.Impl_10 (T : Type) :
  Core_models.Ops.Index.Index (RustSlice T) Core_models.Ops.Range.RangeFull
  where
  index :=
    fun (self : (RustSlice T)) (i : Core_models.Ops.Range.RangeFull) => do
    (Rust_primitives.Slice.slice_slice T
      self
      (0 : usize)
      (← (Rust_primitives.Slice.slice_length T self)))

@[reducible] instance Core_models.Slice.Impl_11.AssociatedTypes (T : Type) :
  Core_models.Ops.Index.Index.AssociatedTypes (RustSlice T) usize
  where
  Output := T

instance Core_models.Slice.Impl_11 (T : Type) :
  Core_models.Ops.Index.Index (RustSlice T) usize
  where
  index := fun (self : (RustSlice T)) (i : usize) => do
    (Rust_primitives.Slice.slice_index T self i)

@[reducible] instance Core_models.Str.Traits.Impl.AssociatedTypes :
  Core_models.Str.Traits.FromStr.AssociatedTypes u64
  where

instance Core_models.Str.Traits.Impl : Core_models.Str.Traits.FromStr u64 where