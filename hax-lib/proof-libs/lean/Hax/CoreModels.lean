
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
  _from (Self T) : (T -> RustM Self)

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
  into := fun (self : T) => do (Core_models.Convert.From._from U T self)

structure Core_models.Convert.Infallible where


@[reducible] instance Core_models.Convert.Impl_3.AssociatedTypes (T : Type) :
  Core_models.Convert.From.AssociatedTypes T T
  where

instance Core_models.Convert.Impl_3 (T : Type) :
  Core_models.Convert.From T T
  where
  _from := fun (x : T) => do (pure x)

class Core_models.Convert.AsRef.AssociatedTypes (Self : Type) (T : Type) where

class Core_models.Convert.AsRef
  (Self : Type)
  (T : Type)
  [associatedTypes : outParam (Core_models.Convert.AsRef.AssociatedTypes (Self :
      Type) (T : Type))]
  where
  as_ref (Self T) : (Self -> RustM T)

@[reducible] instance Core_models.Convert.Impl_4.AssociatedTypes (T : Type) :
  Core_models.Convert.AsRef.AssociatedTypes T T
  where

instance Core_models.Convert.Impl_4 (T : Type) :
  Core_models.Convert.AsRef T T
  where
  as_ref := fun (self : T) => do (pure self)

class Core_models.Default.Default.AssociatedTypes (Self : Type) where

class Core_models.Default.Default
  (Self : Type)
  [associatedTypes : outParam (Core_models.Default.Default.AssociatedTypes (Self
      : Type))]
  where
  default (Self) : (Rust_primitives.Hax.Tuple0 -> RustM Self)

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

opaque Core_models.Num.Impl_1.rotate_right (x : u8) (n : u32) : RustM u8 

opaque Core_models.Num.Impl_1.rotate_left (x : u8) (n : u32) : RustM u8 

opaque Core_models.Num.Impl_1.leading_zeros (x : u8) : RustM u32 

opaque Core_models.Num.Impl_1.ilog2 (x : u8) : RustM u32 

opaque Core_models.Num.Impl_1.from_be_bytes
  (bytes : (RustArray u8 1))
  : RustM u8


opaque Core_models.Num.Impl_1.from_le_bytes
  (bytes : (RustArray u8 1))
  : RustM u8


opaque Core_models.Num.Impl_1.to_be_bytes (bytes : u8) : RustM (RustArray u8 1) 

opaque Core_models.Num.Impl_1.to_le_bytes (bytes : u8) : RustM (RustArray u8 1) 

@[reducible] instance Core_models.Num.Impl.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u8
  where

instance Core_models.Num.Impl : Core_models.Default.Default u8 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u8))

opaque Core_models.Num.Impl_3.rotate_right (x : u16) (n : u32) : RustM u16 

opaque Core_models.Num.Impl_3.rotate_left (x : u16) (n : u32) : RustM u16 

opaque Core_models.Num.Impl_3.leading_zeros (x : u16) : RustM u32 

opaque Core_models.Num.Impl_3.ilog2 (x : u16) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_2.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u16
  where

instance Core_models.Num.Impl_2 : Core_models.Default.Default u16 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u16))

opaque Core_models.Num.Impl_5.rotate_right (x : u32) (n : u32) : RustM u32 

opaque Core_models.Num.Impl_5.rotate_left (x : u32) (n : u32) : RustM u32 

opaque Core_models.Num.Impl_5.leading_zeros (x : u32) : RustM u32 

opaque Core_models.Num.Impl_5.ilog2 (x : u32) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_4.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u32
  where

instance Core_models.Num.Impl_4 : Core_models.Default.Default u32 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u32))

opaque Core_models.Num.Impl_7.rotate_right (x : u64) (n : u32) : RustM u64 

opaque Core_models.Num.Impl_7.rotate_left (x : u64) (n : u32) : RustM u64 

opaque Core_models.Num.Impl_7.leading_zeros (x : u64) : RustM u32 

opaque Core_models.Num.Impl_7.ilog2 (x : u64) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_6.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u64
  where

instance Core_models.Num.Impl_6 : Core_models.Default.Default u64 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u64))

opaque Core_models.Num.Impl_9.rotate_right (x : u128) (n : u32) : RustM u128 

opaque Core_models.Num.Impl_9.rotate_left (x : u128) (n : u32) : RustM u128 

opaque Core_models.Num.Impl_9.leading_zeros (x : u128) : RustM u32 

opaque Core_models.Num.Impl_9.ilog2 (x : u128) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_8.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u128
  where

instance Core_models.Num.Impl_8 : Core_models.Default.Default u128 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u128))

opaque Core_models.Num.Impl_11.rotate_right (x : usize) (n : u32) : RustM usize 

opaque Core_models.Num.Impl_11.rotate_left (x : usize) (n : u32) : RustM usize 

opaque Core_models.Num.Impl_11.leading_zeros (x : usize) : RustM u32 

opaque Core_models.Num.Impl_11.ilog2 (x : usize) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_10.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes usize
  where

instance Core_models.Num.Impl_10 : Core_models.Default.Default usize where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : usize))

opaque Core_models.Num.Impl_13.rotate_right (x : i8) (n : u32) : RustM i8 

opaque Core_models.Num.Impl_13.rotate_left (x : i8) (n : u32) : RustM i8 

opaque Core_models.Num.Impl_13.leading_zeros (x : i8) : RustM u32 

opaque Core_models.Num.Impl_13.ilog2 (x : i8) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_12.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i8
  where

instance Core_models.Num.Impl_12 : Core_models.Default.Default i8 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i8))

opaque Core_models.Num.Impl_15.rotate_right (x : i16) (n : u32) : RustM i16 

opaque Core_models.Num.Impl_15.rotate_left (x : i16) (n : u32) : RustM i16 

opaque Core_models.Num.Impl_15.leading_zeros (x : i16) : RustM u32 

opaque Core_models.Num.Impl_15.ilog2 (x : i16) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_14.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i16
  where

instance Core_models.Num.Impl_14 : Core_models.Default.Default i16 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i16))

opaque Core_models.Num.Impl_17.rotate_right (x : i32) (n : u32) : RustM i32 

opaque Core_models.Num.Impl_17.rotate_left (x : i32) (n : u32) : RustM i32 

opaque Core_models.Num.Impl_17.leading_zeros (x : i32) : RustM u32 

opaque Core_models.Num.Impl_17.ilog2 (x : i32) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_16.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i32
  where

instance Core_models.Num.Impl_16 : Core_models.Default.Default i32 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i32))

opaque Core_models.Num.Impl_19.rotate_right (x : i64) (n : u32) : RustM i64 

opaque Core_models.Num.Impl_19.rotate_left (x : i64) (n : u32) : RustM i64 

opaque Core_models.Num.Impl_19.leading_zeros (x : i64) : RustM u32 

opaque Core_models.Num.Impl_19.ilog2 (x : i64) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_18.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i64
  where

instance Core_models.Num.Impl_18 : Core_models.Default.Default i64 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i64))

opaque Core_models.Num.Impl_21.rotate_right (x : i128) (n : u32) : RustM i128 

opaque Core_models.Num.Impl_21.rotate_left (x : i128) (n : u32) : RustM i128 

opaque Core_models.Num.Impl_21.leading_zeros (x : i128) : RustM u32 

opaque Core_models.Num.Impl_21.ilog2 (x : i128) : RustM u32 

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


@[reducible] instance Core_models.Num.Impl_20.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i128
  where

instance Core_models.Num.Impl_20 : Core_models.Default.Default i128 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i128))

opaque Core_models.Num.Impl_23.rotate_right (x : isize) (n : u32) : RustM isize 

opaque Core_models.Num.Impl_23.rotate_left (x : isize) (n : u32) : RustM isize 

opaque Core_models.Num.Impl_23.leading_zeros (x : isize) : RustM u32 

opaque Core_models.Num.Impl_23.ilog2 (x : isize) : RustM u32 

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
      (← (Core_models.Convert.From._from U T x))))

@[reducible] instance Core_models.Convert.Impl_2.AssociatedTypes
  (T : Type)
  (U : Type)
  [Core_models.Convert.TryFrom.AssociatedTypes U T]
  [Core_models.Convert.TryFrom U T ]
  :
  Core_models.Convert.TryInto.AssociatedTypes T U
  where
  Error := (Core_models.Convert.TryFrom.Error U T)

instance Core_models.Convert.Impl_2
  (T : Type)
  (U : Type)
  [Core_models.Convert.TryFrom.AssociatedTypes U T]
  [Core_models.Convert.TryFrom U T ]
  :
  Core_models.Convert.TryInto T U
  where
  try_into := fun (self : T) => do
    (Core_models.Convert.TryFrom.try_from U T self)

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