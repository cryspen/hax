
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax.MissingCore
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace Core_models.Array

structure TryFromSliceError where
  -- no fields

def Impl_23.as_slice (T : Type) (N : usize) (s : (RustArray T N)) :
    RustM (RustSlice T) := do
  (Rust_primitives.Slice.array_as_slice T (N) s)

end Core_models.Array


namespace Core_models.Array.Iter

structure IntoIter (T : Type) (N : usize) where
  _0 : (Rust_primitives.Sequence.Seq T)

end Core_models.Array.Iter


namespace Core_models.Borrow

class Borrow.AssociatedTypes (Self : Type) (Borrowed : Type) where

class Borrow (Self : Type) (Borrowed : Type)
  [associatedTypes : outParam (Borrow.AssociatedTypes (Self : Type) (Borrowed :
      Type))]
  where
  borrow (Self) (Borrowed) : (Self -> RustM Borrowed)

end Core_models.Borrow


namespace Core_models.Clone

class Clone.AssociatedTypes (Self : Type) where

class Clone (Self : Type)
  [associatedTypes : outParam (Clone.AssociatedTypes (Self : Type))]
  where
  clone (Self) : (Self -> RustM Self)

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Clone.AssociatedTypes T
  where

instance Impl (T : Type) : Clone T where
  clone := fun (self : T) => do (pure self)

end Core_models.Clone


namespace Core_models.Cmp

class PartialEq.AssociatedTypes (Self : Type) (Rhs : Type) where

class PartialEq (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialEq.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  eq (Self) (Rhs) : (Self -> Rhs -> RustM Bool)

class Eq.AssociatedTypes (Self : Type) where
  [trait_constr_Eq_i0 : PartialEq.AssociatedTypes Self Self]

attribute [instance] Eq.AssociatedTypes.trait_constr_Eq_i0

class Eq (Self : Type)
  [associatedTypes : outParam (Eq.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Eq_i0 : PartialEq Self Self]

attribute [instance] Eq.trait_constr_Eq_i0

inductive Ordering : Type
| Less : Ordering
| Equal : Ordering
| Greater : Ordering

def Ordering.Less.AnonConst : isize := (-1 : isize)

def Ordering.Equal.AnonConst : isize := (0 : isize)

def Ordering.Greater.AnonConst : isize := (1 : isize)

def Ordering_ (x : Ordering) : RustM isize := do
  match x with
    | (Ordering.Less ) => (pure Ordering.Less.AnonConst)
    | (Ordering.Equal ) => (pure Ordering.Equal.AnonConst)
    | (Ordering.Greater ) => (pure Ordering.Greater.AnonConst)

class Neq.AssociatedTypes (Self : Type) (Rhs : Type) where

class Neq (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Neq.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  neq (Self) (Rhs) : (Self -> Rhs -> RustM Bool)

@[reducible] instance Impl.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_i0 : PartialEq T T ] :
  Neq.AssociatedTypes T T
  where

instance Impl
  (T : Type)
  [trait_constr_Impl_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_i0 : PartialEq T T ] :
  Neq T T
  where
  neq := fun (self : T) (y : T) => do
    (Core.Cmp.PartialEq.eq (← (PartialEq.eq T T self y)) false)

structure Reverse (T : Type) where
  _0 : T

@[reducible] instance Impl_3.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_3_i0 : PartialEq T T ] :
  PartialEq.AssociatedTypes (Reverse T) (Reverse T)
  where

instance Impl_3
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_3_i0 : PartialEq T T ] :
  PartialEq (Reverse T) (Reverse T)
  where
  eq := fun (self : (Reverse T)) (other : (Reverse T)) => do
    (PartialEq.eq T T (Reverse._0 other) (Reverse._0 self))

@[reducible] instance Impl_4.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 : Eq.AssociatedTypes T]
  [trait_constr_Impl_4_i0 : Eq T ] :
  Eq.AssociatedTypes (Reverse T)
  where

instance Impl_4
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 : Eq.AssociatedTypes T]
  [trait_constr_Impl_4_i0 : Eq T ] :
  Eq (Reverse T)
  where

@[reducible] instance Impl_6.AssociatedTypes :
  PartialEq.AssociatedTypes u8 u8
  where

instance Impl_6 : PartialEq u8 u8 where
  eq := fun (self : u8) (other : u8) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_7.AssociatedTypes : Eq.AssociatedTypes u8 where

instance Impl_7 : Eq u8 where

@[reducible] instance Impl_8.AssociatedTypes :
  PartialEq.AssociatedTypes i8 i8
  where

instance Impl_8 : PartialEq i8 i8 where
  eq := fun (self : i8) (other : i8) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_9.AssociatedTypes : Eq.AssociatedTypes i8 where

instance Impl_9 : Eq i8 where

@[reducible] instance Impl_10.AssociatedTypes :
  PartialEq.AssociatedTypes u16 u16
  where

instance Impl_10 : PartialEq u16 u16 where
  eq := fun (self : u16) (other : u16) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_11.AssociatedTypes : Eq.AssociatedTypes u16 where

instance Impl_11 : Eq u16 where

@[reducible] instance Impl_12.AssociatedTypes :
  PartialEq.AssociatedTypes i16 i16
  where

instance Impl_12 : PartialEq i16 i16 where
  eq := fun (self : i16) (other : i16) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_13.AssociatedTypes : Eq.AssociatedTypes i16 where

instance Impl_13 : Eq i16 where

@[reducible] instance Impl_14.AssociatedTypes :
  PartialEq.AssociatedTypes u32 u32
  where

instance Impl_14 : PartialEq u32 u32 where
  eq := fun (self : u32) (other : u32) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_15.AssociatedTypes : Eq.AssociatedTypes u32 where

instance Impl_15 : Eq u32 where

@[reducible] instance Impl_16.AssociatedTypes :
  PartialEq.AssociatedTypes i32 i32
  where

instance Impl_16 : PartialEq i32 i32 where
  eq := fun (self : i32) (other : i32) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_17.AssociatedTypes : Eq.AssociatedTypes i32 where

instance Impl_17 : Eq i32 where

@[reducible] instance Impl_18.AssociatedTypes :
  PartialEq.AssociatedTypes u64 u64
  where

instance Impl_18 : PartialEq u64 u64 where
  eq := fun (self : u64) (other : u64) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_19.AssociatedTypes : Eq.AssociatedTypes u64 where

instance Impl_19 : Eq u64 where

@[reducible] instance Impl_20.AssociatedTypes :
  PartialEq.AssociatedTypes i64 i64
  where

instance Impl_20 : PartialEq i64 i64 where
  eq := fun (self : i64) (other : i64) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_21.AssociatedTypes : Eq.AssociatedTypes i64 where

instance Impl_21 : Eq i64 where

@[reducible] instance Impl_22.AssociatedTypes :
  PartialEq.AssociatedTypes u128 u128
  where

instance Impl_22 : PartialEq u128 u128 where
  eq := fun (self : u128) (other : u128) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_23.AssociatedTypes : Eq.AssociatedTypes u128 where

instance Impl_23 : Eq u128 where

@[reducible] instance Impl_24.AssociatedTypes :
  PartialEq.AssociatedTypes i128 i128
  where

instance Impl_24 : PartialEq i128 i128 where
  eq := fun (self : i128) (other : i128) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_25.AssociatedTypes : Eq.AssociatedTypes i128 where

instance Impl_25 : Eq i128 where

@[reducible] instance Impl_26.AssociatedTypes :
  PartialEq.AssociatedTypes usize usize
  where

instance Impl_26 : PartialEq usize usize where
  eq := fun (self : usize) (other : usize) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_27.AssociatedTypes : Eq.AssociatedTypes usize where

instance Impl_27 : Eq usize where

@[reducible] instance Impl_28.AssociatedTypes :
  PartialEq.AssociatedTypes isize isize
  where

instance Impl_28 : PartialEq isize isize where
  eq := fun (self : isize) (other : isize) => do
    (Rust_primitives.Hax.Machine_int.eq self other)

@[reducible] instance Impl_29.AssociatedTypes : Eq.AssociatedTypes isize where

instance Impl_29 : Eq isize where

end Core_models.Cmp


namespace Core_models.Convert

class Into.AssociatedTypes (Self : Type) (T : Type) where

class Into (Self : Type) (T : Type)
  [associatedTypes : outParam (Into.AssociatedTypes (Self : Type) (T : Type))]
  where
  into (Self) (T) : (Self -> RustM T)

class From.AssociatedTypes (Self : Type) (T : Type) where

class From (Self : Type) (T : Type)
  [associatedTypes : outParam (From.AssociatedTypes (Self : Type) (T : Type))]
  where
  _from (Self) (T) : (T -> RustM Self)

@[reducible] instance Impl.AssociatedTypes
  (T : Type)
  (U : Type)
  [trait_constr_Impl_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_i0 : From U T ] :
  Into.AssociatedTypes T U
  where

instance Impl
  (T : Type)
  (U : Type)
  [trait_constr_Impl_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_i0 : From U T ] :
  Into T U
  where
  into := fun (self : T) => do (From._from U T self)

structure Infallible where
  -- no fields

@[reducible] instance Impl_3.AssociatedTypes (T : Type) :
  From.AssociatedTypes T T
  where

instance Impl_3 (T : Type) : From T T where
  _from := fun (x : T) => do (pure x)

class AsRef.AssociatedTypes (Self : Type) (T : Type) where

class AsRef (Self : Type) (T : Type)
  [associatedTypes : outParam (AsRef.AssociatedTypes (Self : Type) (T : Type))]
  where
  as_ref (Self) (T) : (Self -> RustM T)

@[reducible] instance Impl_4.AssociatedTypes (T : Type) :
  AsRef.AssociatedTypes T T
  where

instance Impl_4 (T : Type) : AsRef T T where
  as_ref := fun (self : T) => do (pure self)

end Core_models.Convert


namespace Core_models.Default

class Default.AssociatedTypes (Self : Type) where

class Default (Self : Type)
  [associatedTypes : outParam (Default.AssociatedTypes (Self : Type))]
  where
  default (Self) : (Rust_primitives.Hax.Tuple0 -> RustM Self)

end Core_models.Default


namespace Core_models.F32

opaque Impl.abs (x : f64) : RustM f64 

end Core_models.F32


namespace Core_models.Fmt

structure Error where
  -- no fields

structure Formatter where
  -- no fields

structure Arguments where
  _0 : Rust_primitives.Hax.Tuple0

end Core_models.Fmt


namespace Core_models.Fmt.Rt

opaque ArgumentType : Type

structure Argument where
  ty : ArgumentType

opaque Impl.new_display (T : Type) (x : T) : RustM Argument 

opaque Impl.new_debug (T : Type) (x : T) : RustM Argument 

opaque Impl.new_lower_hex (T : Type) (x : T) : RustM Argument 

opaque Impl_1.new_binary (T : Type) (x : T) : RustM Argument 

opaque Impl_1.new_const (T : Type) (U : Type) (x : T) (y : U) :
    RustM Core_models.Fmt.Arguments 

opaque Impl_1.new_v1 (T : Type) (U : Type) (V : Type) (W : Type)
    (x : T)
    (y : U)
    (z : V)
    (t : W) :
    RustM Core_models.Fmt.Arguments 

def Impl_1.none (_ : Rust_primitives.Hax.Tuple0) :
    RustM (RustArray Argument 0) := do
  (pure #v[])

opaque Impl_1.new_v1_formatted (T : Type) (U : Type) (V : Type)
    (x : T)
    (y : U)
    (z : V) :
    RustM Core_models.Fmt.Arguments 

inductive Count : Type
| Is : u16 -> Count
| Param : u16 -> Count
| Implied : Count

structure Placeholder where
  position : usize
  flags : u32
  precision : Count
  width : Count

structure UnsafeArg where
  -- no fields

end Core_models.Fmt.Rt


namespace Core_models.Hash

class Hasher.AssociatedTypes (Self : Type) where

class Hasher (Self : Type)
  [associatedTypes : outParam (Hasher.AssociatedTypes (Self : Type))]
  where

class Hash.AssociatedTypes (Self : Type) where

class Hash (Self : Type)
  [associatedTypes : outParam (Hash.AssociatedTypes (Self : Type))]
  where
  hash (Self)
    (H : Type)
    [trait_constr_hash_associated_type_i1 : Hasher.AssociatedTypes H]
    [trait_constr_hash_i1 : Hasher H ] :
    (Self -> H -> RustM H)

end Core_models.Hash


namespace Core_models.Hint

def black_box (T : Type) (dummy : T) : RustM T := do (pure dummy)

@[spec]
def black_box.spec (T : Type) (dummy : T) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (Hax_lib.Prop.Impl.from_bool true))
      (black_box (T : Type) (dummy : T)) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[black_box] <;> try grind
}

def must_use (T : Type) (value : T) : RustM T := do (pure value)

@[spec]
def must_use.spec (T : Type) (value : T) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (Hax_lib.Prop.Impl.from_bool true))
      (must_use (T : Type) (value : T)) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[must_use] <;> try grind
}

end Core_models.Hint


namespace Core_models.Iter.Adapters.Enumerate

structure Enumerate (I : Type) where
  iter : I
  count : usize

def Impl.new (I : Type) (iter : I) : RustM (Enumerate I) := do
  (pure (Enumerate.mk (iter := iter) (count := (0 : usize))))

end Core_models.Iter.Adapters.Enumerate


namespace Core_models.Iter.Adapters.Step_by

structure StepBy (I : Type) where
  iter : I
  step : usize

def Impl.new (I : Type) (iter : I) (step : usize) : RustM (StepBy I) := do
  (pure (StepBy.mk (iter := iter) (step := step)))

end Core_models.Iter.Adapters.Step_by


namespace Core_models.Iter.Adapters.Map

structure Map (I : Type) (F : Type) where
  iter : I
  f : F

def Impl.new (I : Type) (F : Type) (iter : I) (f : F) : RustM (Map I F) := do
  (pure (Map.mk (iter := iter) (f := f)))

end Core_models.Iter.Adapters.Map


namespace Core_models.Iter.Adapters.Take

structure Take (I : Type) where
  iter : I
  n : usize

def Impl.new (I : Type) (iter : I) (n : usize) : RustM (Take I) := do
  (pure (Take.mk (iter := iter) (n := n)))

end Core_models.Iter.Adapters.Take


namespace Core_models.Iter.Adapters.Zip

structure Zip (I1 : Type) (I2 : Type) where
  it1 : I1
  it2 : I2

end Core_models.Iter.Adapters.Zip


namespace Core_models.Marker

class Copy.AssociatedTypes (Self : Type) where
  [trait_constr_Copy_i0 : Core_models.Clone.Clone.AssociatedTypes Self]

attribute [instance] Copy.AssociatedTypes.trait_constr_Copy_i0

class Copy (Self : Type)
  [associatedTypes : outParam (Copy.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Copy_i0 : Core_models.Clone.Clone Self]

attribute [instance] Copy.trait_constr_Copy_i0

class Send.AssociatedTypes (Self : Type) where

class Send (Self : Type)
  [associatedTypes : outParam (Send.AssociatedTypes (Self : Type))]
  where

class Sync.AssociatedTypes (Self : Type) where

class Sync (Self : Type)
  [associatedTypes : outParam (Sync.AssociatedTypes (Self : Type))]
  where

class Sized.AssociatedTypes (Self : Type) where

class Sized (Self : Type)
  [associatedTypes : outParam (Sized.AssociatedTypes (Self : Type))]
  where

class StructuralPartialEq.AssociatedTypes (Self : Type) where

class StructuralPartialEq (Self : Type)
  [associatedTypes : outParam (StructuralPartialEq.AssociatedTypes (Self :
      Type))]
  where

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Send.AssociatedTypes T
  where

instance Impl (T : Type) : Send T where

@[reducible] instance Impl_1.AssociatedTypes (T : Type) :
  Sync.AssociatedTypes T
  where

instance Impl_1 (T : Type) : Sync T where

@[reducible] instance Impl_2.AssociatedTypes (T : Type) :
  Sized.AssociatedTypes T
  where

instance Impl_2 (T : Type) : Sized T where

@[reducible] instance Impl_3.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    Core_models.Clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_3_i0 : Core_models.Clone.Clone T ] :
  Copy.AssociatedTypes T
  where

instance Impl_3
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    Core_models.Clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_3_i0 : Core_models.Clone.Clone T ] :
  Copy T
  where

structure PhantomData (T : Type) where
  _0 : T

end Core_models.Marker


namespace Core_models.Mem

opaque forget (T : Type) (t : T) : RustM Rust_primitives.Hax.Tuple0 

opaque forget_unsized (T : Type) (t : T) : RustM Rust_primitives.Hax.Tuple0 

opaque size_of (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM usize 

opaque size_of_val (T : Type) (val : T) : RustM usize 

opaque min_align_of (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM usize 

opaque min_align_of_val (T : Type) (val : T) : RustM usize 

opaque align_of (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM usize 

opaque align_of_val (T : Type) (val : T) : RustM usize 

opaque align_of_val_raw (T : Type) (val : T) : RustM usize 

opaque needs_drop (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM Bool 

opaque uninitialized (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM T 

opaque swap (T : Type) (x : T) (y : T) : RustM (Rust_primitives.Hax.Tuple2 T T) 

opaque replace (T : Type) (dest : T) (src : T) :
    RustM (Rust_primitives.Hax.Tuple2 T T) 

opaque drop (T : Type) (_x : T) : RustM Rust_primitives.Hax.Tuple0 

def copy
    (T : Type)
    [trait_constr_copy_associated_type_i0 : Core.Marker.Copy.AssociatedTypes T]
    [trait_constr_copy_i0 : Core.Marker.Copy T ]
    (x : T) :
    RustM T := do
  (pure x)

opaque take (T : Type) (x : T) : RustM (Rust_primitives.Hax.Tuple2 T T) 

opaque transmute_copy (Src : Type) (Dst : Type) (src : Src) : RustM Dst 

opaque variant_count (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM usize 

opaque zeroed (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM T 

opaque transmute (Src : Type) (Dst : Type) (src : Src) : RustM Dst 

end Core_models.Mem


namespace Core_models.Mem.Manually_drop

structure ManuallyDrop (T : Type) where
  value : T

end Core_models.Mem.Manually_drop


namespace Core_models.Num.Error

structure TryFromIntError where
  _0 : Rust_primitives.Hax.Tuple0

structure IntErrorKind where
  -- no fields

structure ParseIntError where
  kind : IntErrorKind

end Core_models.Num.Error


namespace Core_models.Num

def Impl_6.wrapping_add (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.wrapping_add_u8 x y)

def Impl_6.wrapping_sub (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u8 x y)

def Impl_6.wrapping_mul (x : u8) (y : u8) : RustM u8 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u8 x y)

def Impl_6.pow (x : u8) (exp : u32) : RustM u8 := do
  (Rust_primitives.Arithmetic.pow_u8 x exp)

opaque Impl_6.leading_zeros (x : u8) : RustM u32 

opaque Impl_6.ilog2 (x : u8) : RustM u32 

def Impl_7.wrapping_add (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.wrapping_add_u16 x y)

def Impl_7.wrapping_sub (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u16 x y)

def Impl_7.wrapping_mul (x : u16) (y : u16) : RustM u16 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u16 x y)

def Impl_7.pow (x : u16) (exp : u32) : RustM u16 := do
  (Rust_primitives.Arithmetic.pow_u16 x exp)

opaque Impl_7.leading_zeros (x : u16) : RustM u32 

opaque Impl_7.ilog2 (x : u16) : RustM u32 

def Impl_8.wrapping_add (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.wrapping_add_u32 x y)

def Impl_8.wrapping_sub (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u32 x y)

def Impl_8.wrapping_mul (x : u32) (y : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u32 x y)

def Impl_8.pow (x : u32) (exp : u32) : RustM u32 := do
  (Rust_primitives.Arithmetic.pow_u32 x exp)

opaque Impl_8.leading_zeros (x : u32) : RustM u32 

opaque Impl_8.ilog2 (x : u32) : RustM u32 

def Impl_9.wrapping_add (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.wrapping_add_u64 x y)

def Impl_9.wrapping_sub (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u64 x y)

def Impl_9.wrapping_mul (x : u64) (y : u64) : RustM u64 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u64 x y)

def Impl_9.pow (x : u64) (exp : u32) : RustM u64 := do
  (Rust_primitives.Arithmetic.pow_u64 x exp)

opaque Impl_9.leading_zeros (x : u64) : RustM u32 

opaque Impl_9.ilog2 (x : u64) : RustM u32 

def Impl_10.wrapping_add (x : u128) (y : u128) : RustM u128 := do
  (Rust_primitives.Arithmetic.wrapping_add_u128 x y)

def Impl_10.wrapping_sub (x : u128) (y : u128) : RustM u128 := do
  (Rust_primitives.Arithmetic.wrapping_sub_u128 x y)

def Impl_10.wrapping_mul (x : u128) (y : u128) : RustM u128 := do
  (Rust_primitives.Arithmetic.wrapping_mul_u128 x y)

def Impl_10.pow (x : u128) (exp : u32) : RustM u128 := do
  (Rust_primitives.Arithmetic.pow_u128 x exp)

opaque Impl_10.leading_zeros (x : u128) : RustM u32 

opaque Impl_10.ilog2 (x : u128) : RustM u32 

def Impl_11.wrapping_add (x : usize) (y : usize) : RustM usize := do
  (Rust_primitives.Arithmetic.wrapping_add_usize x y)

def Impl_11.wrapping_sub (x : usize) (y : usize) : RustM usize := do
  (Rust_primitives.Arithmetic.wrapping_sub_usize x y)

def Impl_11.wrapping_mul (x : usize) (y : usize) : RustM usize := do
  (Rust_primitives.Arithmetic.wrapping_mul_usize x y)

def Impl_11.pow (x : usize) (exp : u32) : RustM usize := do
  (Rust_primitives.Arithmetic.pow_usize x exp)

opaque Impl_11.leading_zeros (x : usize) : RustM u32 

opaque Impl_11.ilog2 (x : usize) : RustM u32 

def Impl_12.wrapping_add (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.wrapping_add_i8 x y)

def Impl_12.wrapping_sub (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i8 x y)

def Impl_12.wrapping_mul (x : i8) (y : i8) : RustM i8 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i8 x y)

def Impl_12.pow (x : i8) (exp : u32) : RustM i8 := do
  (Rust_primitives.Arithmetic.pow_i8 x exp)

opaque Impl_12.leading_zeros (x : i8) : RustM u32 

opaque Impl_12.ilog2 (x : i8) : RustM u32 

def Impl_13.wrapping_add (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.wrapping_add_i16 x y)

def Impl_13.wrapping_sub (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i16 x y)

def Impl_13.wrapping_mul (x : i16) (y : i16) : RustM i16 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i16 x y)

def Impl_13.pow (x : i16) (exp : u32) : RustM i16 := do
  (Rust_primitives.Arithmetic.pow_i16 x exp)

opaque Impl_13.leading_zeros (x : i16) : RustM u32 

opaque Impl_13.ilog2 (x : i16) : RustM u32 

def Impl_14.wrapping_add (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.wrapping_add_i32 x y)

def Impl_14.wrapping_sub (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i32 x y)

def Impl_14.wrapping_mul (x : i32) (y : i32) : RustM i32 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i32 x y)

def Impl_14.pow (x : i32) (exp : u32) : RustM i32 := do
  (Rust_primitives.Arithmetic.pow_i32 x exp)

opaque Impl_14.leading_zeros (x : i32) : RustM u32 

opaque Impl_14.ilog2 (x : i32) : RustM u32 

def Impl_15.wrapping_add (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.wrapping_add_i64 x y)

def Impl_15.wrapping_sub (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i64 x y)

def Impl_15.wrapping_mul (x : i64) (y : i64) : RustM i64 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i64 x y)

def Impl_15.pow (x : i64) (exp : u32) : RustM i64 := do
  (Rust_primitives.Arithmetic.pow_i64 x exp)

opaque Impl_15.leading_zeros (x : i64) : RustM u32 

opaque Impl_15.ilog2 (x : i64) : RustM u32 

def Impl_16.wrapping_add (x : i128) (y : i128) : RustM i128 := do
  (Rust_primitives.Arithmetic.wrapping_add_i128 x y)

def Impl_16.wrapping_sub (x : i128) (y : i128) : RustM i128 := do
  (Rust_primitives.Arithmetic.wrapping_sub_i128 x y)

def Impl_16.wrapping_mul (x : i128) (y : i128) : RustM i128 := do
  (Rust_primitives.Arithmetic.wrapping_mul_i128 x y)

def Impl_16.pow (x : i128) (exp : u32) : RustM i128 := do
  (Rust_primitives.Arithmetic.pow_i128 x exp)

opaque Impl_16.leading_zeros (x : i128) : RustM u32 

opaque Impl_16.ilog2 (x : i128) : RustM u32 

def Impl_17.wrapping_add (x : isize) (y : isize) : RustM isize := do
  (Rust_primitives.Arithmetic.wrapping_add_isize x y)

def Impl_17.wrapping_sub (x : isize) (y : isize) : RustM isize := do
  (Rust_primitives.Arithmetic.wrapping_sub_isize x y)

def Impl_17.wrapping_mul (x : isize) (y : isize) : RustM isize := do
  (Rust_primitives.Arithmetic.wrapping_mul_isize x y)

def Impl_17.pow (x : isize) (exp : u32) : RustM isize := do
  (Rust_primitives.Arithmetic.pow_isize x exp)

opaque Impl_17.leading_zeros (x : isize) : RustM u32 

opaque Impl_17.ilog2 (x : isize) : RustM u32 

@[reducible] instance Impl_18.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u8
  where

instance Impl_18 : Core_models.Default.Default u8 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u8))

@[reducible] instance Impl_19.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u16
  where

instance Impl_19 : Core_models.Default.Default u16 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u16))

@[reducible] instance Impl_20.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u32
  where

instance Impl_20 : Core_models.Default.Default u32 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u32))

@[reducible] instance Impl_21.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u64
  where

instance Impl_21 : Core_models.Default.Default u64 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u64))

@[reducible] instance Impl_22.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes u128
  where

instance Impl_22 : Core_models.Default.Default u128 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : u128))

@[reducible] instance Impl_23.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes usize
  where

instance Impl_23 : Core_models.Default.Default usize where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : usize))

@[reducible] instance Impl_24.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i8
  where

instance Impl_24 : Core_models.Default.Default i8 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i8))

@[reducible] instance Impl_25.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i16
  where

instance Impl_25 : Core_models.Default.Default i16 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i16))

@[reducible] instance Impl_26.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i32
  where

instance Impl_26 : Core_models.Default.Default i32 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i32))

@[reducible] instance Impl_27.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i64
  where

instance Impl_27 : Core_models.Default.Default i64 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i64))

@[reducible] instance Impl_28.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes i128
  where

instance Impl_28 : Core_models.Default.Default i128 where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : i128))

@[reducible] instance Impl_29.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes isize
  where

instance Impl_29 : Core_models.Default.Default isize where
  default := fun (_ : Rust_primitives.Hax.Tuple0) => do (pure (0 : isize))

end Core_models.Num


namespace Core_models.Ops.Arith

class AddAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class AddAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (AddAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  add_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class SubAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class SubAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (SubAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  sub_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class MulAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class MulAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (MulAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  mul_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class DivAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class DivAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (DivAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  div_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class RemAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class RemAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (RemAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  rem_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

end Core_models.Ops.Arith


namespace Core_models.Ops.Control_flow

inductive ControlFlow (B : Type) (C : Type) : Type
| Continue : C -> ControlFlow (B : Type) (C : Type)
| Break : B -> ControlFlow (B : Type) (C : Type)

end Core_models.Ops.Control_flow


namespace Core_models.Ops.Try_trait

class FromResidual.AssociatedTypes (Self : Type) (R : Type) where

class FromResidual (Self : Type) (R : Type)
  [associatedTypes : outParam (FromResidual.AssociatedTypes (Self : Type) (R :
      Type))]
  where
  from_residual (Self) (R) : (R -> RustM Self)

end Core_models.Ops.Try_trait


namespace Core_models.Ops.Drop

class Drop.AssociatedTypes (Self : Type) where

class Drop (Self : Type)
  [associatedTypes : outParam (Drop.AssociatedTypes (Self : Type))]
  where
  drop (Self) : (Self -> RustM Self)

end Core_models.Ops.Drop


namespace Core_models.Ops.Range

structure RangeTo (T : Type) where
  _end : T

structure RangeFrom (T : Type) where
  start : T

structure Range (T : Type) where
  start : T
  _end : T

structure RangeFull where
  -- no fields

end Core_models.Ops.Range


namespace Core_models.Option

inductive Option (T : Type) : Type
| Some : T -> Option (T : Type)
| None : Option (T : Type)

end Core_models.Option


namespace Core_models.Cmp

class PartialOrd.AssociatedTypes (Self : Type) (Rhs : Type) where
  [trait_constr_PartialOrd_i0 : PartialEq.AssociatedTypes Self Rhs]

attribute [instance] PartialOrd.AssociatedTypes.trait_constr_PartialOrd_i0

class PartialOrd (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialOrd.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  [trait_constr_PartialOrd_i0 : PartialEq Self Rhs]
  partial_cmp (Self) (Rhs) :
    (Self -> Rhs -> RustM (Core_models.Option.Option Ordering))

attribute [instance] PartialOrd.trait_constr_PartialOrd_i0

class PartialOrdDefaults.AssociatedTypes (Self : Type) (Rhs : Type) where

class PartialOrdDefaults (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialOrdDefaults.AssociatedTypes (Self : Type)
      (Rhs : Type))]
  where
  lt (Self) (Rhs)
    [trait_constr_lt_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_lt_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)
  le (Self) (Rhs)
    [trait_constr_le_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_le_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)
  gt (Self) (Rhs)
    [trait_constr_gt_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_gt_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)
  ge (Self) (Rhs)
    [trait_constr_ge_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_ge_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)

@[reducible] instance Impl_1.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_1_i0 : PartialOrd T T ] :
  PartialOrdDefaults.AssociatedTypes T T
  where

instance Impl_1
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_1_i0 : PartialOrd T T ] :
  PartialOrdDefaults T T
  where
  lt :=
    fun
      [trait_constr_lt_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_lt_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some  (Ordering.Less )) => (pure true)
      | _ => (pure false)
  le :=
    fun
      [trait_constr_le_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_le_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some  (Ordering.Less )) |
        (Core_models.Option.Option.Some  (Ordering.Equal )) =>
        (pure true)
      | _ => (pure false)
  gt :=
    fun
      [trait_constr_gt_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_gt_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some  (Ordering.Greater )) => (pure true)
      | _ => (pure false)
  ge :=
    fun
      [trait_constr_ge_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_ge_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (Core_models.Option.Option.Some  (Ordering.Greater )) |
        (Core_models.Option.Option.Some  (Ordering.Equal )) =>
        (pure true)
      | _ => (pure false)

class Ord.AssociatedTypes (Self : Type) where
  [trait_constr_Ord_i0 : Eq.AssociatedTypes Self]
  [trait_constr_Ord_i1 : PartialOrd.AssociatedTypes Self Self]

attribute [instance] Ord.AssociatedTypes.trait_constr_Ord_i0

attribute [instance] Ord.AssociatedTypes.trait_constr_Ord_i1

class Ord (Self : Type)
  [associatedTypes : outParam (Ord.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Ord_i0 : Eq Self]
  [trait_constr_Ord_i1 : PartialOrd Self Self]
  cmp (Self) : (Self -> Self -> RustM Ordering)

attribute [instance] Ord.trait_constr_Ord_i0

attribute [instance] Ord.trait_constr_Ord_i1

def max
    (T : Type)
    [trait_constr_max_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_max_i0 : Ord T ]
    (v1 : T)
    (v2 : T) :
    RustM T := do
  match (← (Ord.cmp T v1 v2)) with
    | (Ordering.Greater ) => (pure v1)
    | _ => (pure v2)

def min
    (T : Type)
    [trait_constr_min_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_min_i0 : Ord T ]
    (v1 : T)
    (v2 : T) :
    RustM T := do
  match (← (Ord.cmp T v1 v2)) with
    | (Ordering.Greater ) => (pure v2)
    | _ => (pure v1)

@[reducible] instance Impl_2.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_2_i0 : PartialOrd T T ] :
  PartialOrd.AssociatedTypes (Reverse T) (Reverse T)
  where

instance Impl_2
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_2_i0 : PartialOrd T T ] :
  PartialOrd (Reverse T) (Reverse T)
  where
  partial_cmp := fun (self : (Reverse T)) (other : (Reverse T)) => do
    (PartialOrd.partial_cmp T T (Reverse._0 other) (Reverse._0 self))

@[reducible] instance Impl_5.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_5_associated_type_i0 : Ord.AssociatedTypes T]
  [trait_constr_Impl_5_i0 : Ord T ] :
  Ord.AssociatedTypes (Reverse T)
  where

instance Impl_5
  (T : Type)
  [trait_constr_Impl_5_associated_type_i0 : Ord.AssociatedTypes T]
  [trait_constr_Impl_5_i0 : Ord T ] :
  Ord (Reverse T)
  where
  cmp := fun (self : (Reverse T)) (other : (Reverse T)) => do
    (Ord.cmp T (Reverse._0 other) (Reverse._0 self))

@[reducible] instance Impl_30.AssociatedTypes :
  PartialOrd.AssociatedTypes u8 u8
  where

instance Impl_30 : PartialOrd u8 u8 where
  partial_cmp := fun (self : u8) (other : u8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_31.AssociatedTypes : Ord.AssociatedTypes u8 where

instance Impl_31 : Ord u8 where
  cmp := fun (self : u8) (other : u8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_32.AssociatedTypes :
  PartialOrd.AssociatedTypes i8 i8
  where

instance Impl_32 : PartialOrd i8 i8 where
  partial_cmp := fun (self : i8) (other : i8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_33.AssociatedTypes : Ord.AssociatedTypes i8 where

instance Impl_33 : Ord i8 where
  cmp := fun (self : i8) (other : i8) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_34.AssociatedTypes :
  PartialOrd.AssociatedTypes u16 u16
  where

instance Impl_34 : PartialOrd u16 u16 where
  partial_cmp := fun (self : u16) (other : u16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_35.AssociatedTypes : Ord.AssociatedTypes u16 where

instance Impl_35 : Ord u16 where
  cmp := fun (self : u16) (other : u16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_36.AssociatedTypes :
  PartialOrd.AssociatedTypes i16 i16
  where

instance Impl_36 : PartialOrd i16 i16 where
  partial_cmp := fun (self : i16) (other : i16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_37.AssociatedTypes : Ord.AssociatedTypes i16 where

instance Impl_37 : Ord i16 where
  cmp := fun (self : i16) (other : i16) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_38.AssociatedTypes :
  PartialOrd.AssociatedTypes u32 u32
  where

instance Impl_38 : PartialOrd u32 u32 where
  partial_cmp := fun (self : u32) (other : u32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_39.AssociatedTypes : Ord.AssociatedTypes u32 where

instance Impl_39 : Ord u32 where
  cmp := fun (self : u32) (other : u32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_40.AssociatedTypes :
  PartialOrd.AssociatedTypes i32 i32
  where

instance Impl_40 : PartialOrd i32 i32 where
  partial_cmp := fun (self : i32) (other : i32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_41.AssociatedTypes : Ord.AssociatedTypes i32 where

instance Impl_41 : Ord i32 where
  cmp := fun (self : i32) (other : i32) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_42.AssociatedTypes :
  PartialOrd.AssociatedTypes u64 u64
  where

instance Impl_42 : PartialOrd u64 u64 where
  partial_cmp := fun (self : u64) (other : u64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_43.AssociatedTypes : Ord.AssociatedTypes u64 where

instance Impl_43 : Ord u64 where
  cmp := fun (self : u64) (other : u64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_44.AssociatedTypes :
  PartialOrd.AssociatedTypes i64 i64
  where

instance Impl_44 : PartialOrd i64 i64 where
  partial_cmp := fun (self : i64) (other : i64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_45.AssociatedTypes : Ord.AssociatedTypes i64 where

instance Impl_45 : Ord i64 where
  cmp := fun (self : i64) (other : i64) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_46.AssociatedTypes :
  PartialOrd.AssociatedTypes u128 u128
  where

instance Impl_46 : PartialOrd u128 u128 where
  partial_cmp := fun (self : u128) (other : u128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_47.AssociatedTypes : Ord.AssociatedTypes u128 where

instance Impl_47 : Ord u128 where
  cmp := fun (self : u128) (other : u128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_48.AssociatedTypes :
  PartialOrd.AssociatedTypes i128 i128
  where

instance Impl_48 : PartialOrd i128 i128 where
  partial_cmp := fun (self : i128) (other : i128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_49.AssociatedTypes : Ord.AssociatedTypes i128 where

instance Impl_49 : Ord i128 where
  cmp := fun (self : i128) (other : i128) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_50.AssociatedTypes :
  PartialOrd.AssociatedTypes usize usize
  where

instance Impl_50 : PartialOrd usize usize where
  partial_cmp := fun (self : usize) (other : usize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_51.AssociatedTypes : Ord.AssociatedTypes usize where

instance Impl_51 : Ord usize where
  cmp := fun (self : usize) (other : usize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

@[reducible] instance Impl_52.AssociatedTypes :
  PartialOrd.AssociatedTypes isize isize
  where

instance Impl_52 : PartialOrd isize isize where
  partial_cmp := fun (self : isize) (other : isize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure (Core_models.Option.Option.Some Ordering.Less))
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure (Core_models.Option.Option.Some Ordering.Greater))
      else
        (pure (Core_models.Option.Option.Some Ordering.Equal))

@[reducible] instance Impl_53.AssociatedTypes : Ord.AssociatedTypes isize where

instance Impl_53 : Ord isize where
  cmp := fun (self : isize) (other : isize) => do
    if (← (Rust_primitives.Hax.Machine_int.lt self other)) then
      (pure Ordering.Less)
    else
      if (← (Rust_primitives.Hax.Machine_int.gt self other)) then
        (pure Ordering.Greater)
      else
        (pure Ordering.Equal)

end Core_models.Cmp


namespace Core_models.Iter.Adapters.Flat_map

structure FlatMap (I : Type) (U : Type) (F : Type) where
  it : I
  f : F
  current : (Core_models.Option.Option U)

end Core_models.Iter.Adapters.Flat_map


namespace Core_models.Option

def Impl.as_ref (T : Type) (self : (Option T)) : RustM (Option T) := do
  match self with
    | (Option.Some  x) => (pure (Option.Some x))
    | (Option.None ) => (pure Option.None)

def Impl.unwrap_or (T : Type) (self : (Option T)) (default : T) : RustM T := do
  match self with
    | (Option.Some  x) => (pure x)
    | (Option.None ) => (pure default)

def Impl.unwrap_or_default
    (T : Type)
    [trait_constr_unwrap_or_default_associated_type_i0 :
      Core_models.Default.Default.AssociatedTypes
      T]
    [trait_constr_unwrap_or_default_i0 : Core_models.Default.Default T ]
    (self : (Option T)) :
    RustM T := do
  match self with
    | (Option.Some  x) => (pure x)
    | (Option.None ) =>
      (Core_models.Default.Default.default T Rust_primitives.Hax.Tuple0.mk)

def Impl.take (T : Type) (self : (Option T)) :
    RustM (Rust_primitives.Hax.Tuple2 (Option T) (Option T)) := do
  (pure (Rust_primitives.Hax.Tuple2.mk Option.None self))

def Impl.is_some (T : Type) (self : (Option T)) : RustM Bool := do
  match self with | (Option.Some  _) => (pure true) | _ => (pure false)

@[spec]
def Impl.is_some.spec (T : Type) (self : (Option T)) :
    Spec
      (requires := do pure True)
      (ensures := fun
          res => do
          (Hax_lib.Prop.Constructors.implies
            (← (Hax_lib.Prop.Constructors.from_bool res))
            (← (Hax_lib.Prop.Impl.from_bool true))))
      (Impl.is_some (T : Type) (self : (Option T))) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Impl.is_some] <;> try grind
}

def Impl.is_none (T : Type) (self : (Option T)) : RustM Bool := do
  (Core.Cmp.PartialEq.eq (← (Impl.is_some T self)) false)

end Core_models.Option


namespace Core_models.Panicking

opaque panic_explicit (_ : Rust_primitives.Hax.Tuple0) :
    RustM Rust_primitives.Hax.Never 

opaque panic (_msg : String) : RustM Rust_primitives.Hax.Never 

opaque panic_fmt (_fmt : Core_models.Fmt.Arguments) :
    RustM Rust_primitives.Hax.Never 

end Core_models.Panicking


namespace Core_models.Panicking.Internal

opaque panic (T : Type) (_ : Rust_primitives.Hax.Tuple0) : RustM T 

end Core_models.Panicking.Internal


namespace Core_models.Hash

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Hash.AssociatedTypes T
  where

instance Impl (T : Type) : Hash T where
  hash :=
    fun
      (H : Type)
      [trait_constr_hash_associated_type_i0 : Hasher.AssociatedTypes H]
      [trait_constr_hash_i0 : Hasher H ] (self : T) (h : H) => do
    (Core_models.Panicking.Internal.panic H Rust_primitives.Hax.Tuple0.mk)

end Core_models.Hash


namespace Core_models.Result

inductive Result (T : Type) (E : Type) : Type
| Ok : T -> Result (T : Type) (E : Type)
| Err : E -> Result (T : Type) (E : Type)

end Core_models.Result


namespace Core_models.Fmt

abbrev Result :
  Type :=
  (Core_models.Result.Result Rust_primitives.Hax.Tuple0 Error)

class Display.AssociatedTypes (Self : Type) where

class Display (Self : Type)
  [associatedTypes : outParam (Display.AssociatedTypes (Self : Type))]
  where
  fmt (Self) :
    (Self ->
    Formatter ->
    RustM (Rust_primitives.Hax.Tuple2
      Formatter
      (Core_models.Result.Result Rust_primitives.Hax.Tuple0 Error)))

class Debug.AssociatedTypes (Self : Type) where

class Debug (Self : Type)
  [associatedTypes : outParam (Debug.AssociatedTypes (Self : Type))]
  where
  dbg_fmt (Self) :
    (Self ->
    Formatter ->
    RustM (Rust_primitives.Hax.Tuple2
      Formatter
      (Core_models.Result.Result Rust_primitives.Hax.Tuple0 Error)))

end Core_models.Fmt


namespace Core_models.Error

class Error.AssociatedTypes (Self : Type) where
  [trait_constr_Error_i0 : Core_models.Fmt.Display.AssociatedTypes Self]
  [trait_constr_Error_i1 : Core_models.Fmt.Debug.AssociatedTypes Self]

attribute [instance] Error.AssociatedTypes.trait_constr_Error_i0

attribute [instance] Error.AssociatedTypes.trait_constr_Error_i1

class Error (Self : Type)
  [associatedTypes : outParam (Error.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Error_i0 : Core_models.Fmt.Display Self]
  [trait_constr_Error_i1 : Core_models.Fmt.Debug Self]

attribute [instance] Error.trait_constr_Error_i0

attribute [instance] Error.trait_constr_Error_i1

end Core_models.Error


namespace Core_models.Fmt

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Debug.AssociatedTypes T
  where

instance Impl (T : Type) : Debug T where
  dbg_fmt := fun (self : T) (f : Formatter) => do
    let
      hax_temp_output : (Core_models.Result.Result
        Rust_primitives.Hax.Tuple0
        Error) :=
      (Core_models.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk);
    (pure (Rust_primitives.Hax.Tuple2.mk f hax_temp_output))

def Impl_11.write_fmt (f : Formatter) (args : Arguments) :
    RustM
    (Rust_primitives.Hax.Tuple2
      Formatter
      (Core_models.Result.Result Rust_primitives.Hax.Tuple0 Error))
    := do
  let
    hax_temp_output : (Core_models.Result.Result
      Rust_primitives.Hax.Tuple0
      Error) :=
    (Core_models.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk);
  (pure (Rust_primitives.Hax.Tuple2.mk f hax_temp_output))

end Core_models.Fmt


namespace Core_models.Num

opaque Impl_6.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result u8 Core_models.Num.Error.ParseIntError) 

opaque Impl_7.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result u16 Core_models.Num.Error.ParseIntError) 

opaque Impl_8.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result u32 Core_models.Num.Error.ParseIntError) 

opaque Impl_9.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result u64 Core_models.Num.Error.ParseIntError) 

opaque Impl_10.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result u128 Core_models.Num.Error.ParseIntError) 

opaque Impl_11.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result usize Core_models.Num.Error.ParseIntError) 

opaque Impl_12.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result i8 Core_models.Num.Error.ParseIntError) 

opaque Impl_13.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result i16 Core_models.Num.Error.ParseIntError) 

opaque Impl_14.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result i32 Core_models.Num.Error.ParseIntError) 

opaque Impl_15.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result i64 Core_models.Num.Error.ParseIntError) 

opaque Impl_16.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result i128 Core_models.Num.Error.ParseIntError) 

opaque Impl_17.from_str_radix (src : String) (radix : u32) :
    RustM (Core_models.Result.Result isize Core_models.Num.Error.ParseIntError) 

end Core_models.Num


namespace Core_models.Option

def Impl.ok_or (T : Type) (E : Type) (self : (Option T)) (err : E) :
    RustM (Core_models.Result.Result T E) := do
  match self with
    | (Option.Some  v) => (pure (Core_models.Result.Result.Ok v))
    | (Option.None ) => (pure (Core_models.Result.Result.Err err))

end Core_models.Option


namespace Core_models.Result

def Impl.unwrap_or (T : Type) (E : Type) (self : (Result T E)) (default : T) :
    RustM T := do
  match self with
    | (Result.Ok  t) => (pure t)
    | (Result.Err  _) => (pure default)

def Impl.is_ok (T : Type) (E : Type) (self : (Result T E)) : RustM Bool := do
  match self with | (Result.Ok  _) => (pure true) | _ => (pure false)

def Impl.ok (T : Type) (E : Type) (self : (Result T E)) :
    RustM (Core_models.Option.Option T) := do
  match self with
    | (Result.Ok  x) => (pure (Core_models.Option.Option.Some x))
    | (Result.Err  _) => (pure Core_models.Option.Option.None)

end Core_models.Result


namespace Core_models.Slice.Iter

structure Chunks (T : Type) where
  cs : usize
  elements : (RustSlice T)

def Impl.new (T : Type) (cs : usize) (elements : (RustSlice T)) :
    RustM (Chunks T) := do
  (pure (Chunks.mk (cs := cs) (elements := elements)))

structure ChunksExact (T : Type) where
  cs : usize
  elements : (RustSlice T)

def Impl_1.new (T : Type) (cs : usize) (elements : (RustSlice T)) :
    RustM (ChunksExact T) := do
  (pure (ChunksExact.mk (cs := cs) (elements := elements)))

structure Iter (T : Type) where
  _0 : (Rust_primitives.Sequence.Seq T)

end Core_models.Slice.Iter


namespace Core_models.Slice

def Impl.len (T : Type) (s : (RustSlice T)) : RustM usize := do
  (Rust_primitives.Slice.slice_length T s)

def Impl.chunks (T : Type) (s : (RustSlice T)) (cs : usize) :
    RustM (Core_models.Slice.Iter.Chunks T) := do
  (Core_models.Slice.Iter.Impl.new T cs s)

def Impl.iter (T : Type) (s : (RustSlice T)) :
    RustM (Core_models.Slice.Iter.Iter T) := do
  (pure (Core_models.Slice.Iter.Iter.mk
    (← (Rust_primitives.Sequence.seq_from_slice T s))))

def Impl.chunks_exact (T : Type) (s : (RustSlice T)) (cs : usize) :
    RustM (Core_models.Slice.Iter.ChunksExact T) := do
  (Core_models.Slice.Iter.Impl_1.new T cs s)

def Impl.is_empty (T : Type) (s : (RustSlice T)) : RustM Bool := do
  (Rust_primitives.Hax.Machine_int.eq (← (Impl.len T s)) (0 : usize))

opaque Impl.contains (T : Type) (s : (RustSlice T)) (v : T) : RustM Bool 

opaque Impl.copy_within
    (T : Type)
    (R : Type)
    [trait_constr_copy_within_associated_type_i0 :
      Core.Marker.Copy.AssociatedTypes
      T]
    [trait_constr_copy_within_i0 : Core.Marker.Copy T ]
    (s : (RustSlice T))
    (src : R)
    (dest : usize) :
    RustM (RustSlice T) 

opaque Impl.binary_search (T : Type) (s : (RustSlice T)) (x : T) :
    RustM (Core_models.Result.Result usize usize) 

def Impl.copy_from_slice
    (T : Type)
    [trait_constr_copy_from_slice_associated_type_i0 :
      Core_models.Marker.Copy.AssociatedTypes
      T]
    [trait_constr_copy_from_slice_i0 : Core_models.Marker.Copy T ]
    (s : (RustSlice T))
    (src : (RustSlice T)) :
    RustM (RustSlice T) := do
  let ⟨tmp0, out⟩ ← (Rust_primitives.Mem.replace (RustSlice T) s src);
  let s : (RustSlice T) := tmp0;
  let _ := out;
  (pure s)

@[spec]
def
      Impl.copy_from_slice.spec
      (T : Type)
      [trait_constr_copy_from_slice_associated_type_i0 :
        Core_models.Marker.Copy.AssociatedTypes
        T]
      [trait_constr_copy_from_slice_i0 : Core_models.Marker.Copy T ]
      (s : (RustSlice T))
      (src : (RustSlice T)) :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.eq
          (← (Impl.len T s))
          (← (Impl.len T src))))
      (ensures := fun _ => pure True)
      (Impl.copy_from_slice
        (T : Type)
        (s : (RustSlice T))
        (src : (RustSlice T))) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Impl.copy_from_slice] <;> try grind
}

def Impl.clone_from_slice
    (T : Type)
    [trait_constr_clone_from_slice_associated_type_i0 :
      Core_models.Clone.Clone.AssociatedTypes
      T]
    [trait_constr_clone_from_slice_i0 : Core_models.Clone.Clone T ]
    (s : (RustSlice T))
    (src : (RustSlice T)) :
    RustM (RustSlice T) := do
  let ⟨tmp0, out⟩ ← (Rust_primitives.Mem.replace (RustSlice T) s src);
  let s : (RustSlice T) := tmp0;
  let _ := out;
  (pure s)

@[spec]
def
      Impl.clone_from_slice.spec
      (T : Type)
      [trait_constr_clone_from_slice_associated_type_i0 :
        Core_models.Clone.Clone.AssociatedTypes
        T]
      [trait_constr_clone_from_slice_i0 : Core_models.Clone.Clone T ]
      (s : (RustSlice T))
      (src : (RustSlice T)) :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.eq
          (← (Impl.len T s))
          (← (Impl.len T src))))
      (ensures := fun _ => pure True)
      (Impl.clone_from_slice
        (T : Type)
        (s : (RustSlice T))
        (src : (RustSlice T))) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Impl.clone_from_slice] <;> try grind
}

def Impl.split_at (T : Type) (s : (RustSlice T)) (mid : usize) :
    RustM (Rust_primitives.Hax.Tuple2 (RustSlice T) (RustSlice T)) := do
  (Rust_primitives.Slice.slice_split_at T s mid)

@[spec]
def Impl.split_at.spec (T : Type) (s : (RustSlice T)) (mid : usize) :
    Spec
      (requires := do
        (Rust_primitives.Hax.Machine_int.le mid (← (Impl.len T s))))
      (ensures := fun _ => pure True)
      (Impl.split_at (T : Type) (s : (RustSlice T)) (mid : usize)) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[Impl.split_at] <;> try grind
}

def Impl.split_at_checked (T : Type) (s : (RustSlice T)) (mid : usize) :
    RustM
    (Core_models.Option.Option
      (Rust_primitives.Hax.Tuple2 (RustSlice T) (RustSlice T)))
    := do
  if (← (Rust_primitives.Hax.Machine_int.le mid (← (Impl.len T s)))) then
    (pure (Core_models.Option.Option.Some (← (Impl.split_at T s mid))))
  else
    (pure Core_models.Option.Option.None)

end Core_models.Slice


namespace Core_models.Str.Error

structure Utf8Error where
  -- no fields

end Core_models.Str.Error


namespace Core_models.Str.Converts

opaque from_utf8 (s : (RustSlice u8)) :
    RustM (Core_models.Result.Result String Core_models.Str.Error.Utf8Error) 

end Core_models.Str.Converts


namespace Core_models.Str.Iter

structure Split (T : Type) where
  _0 : T

end Core_models.Str.Iter


namespace Core_models.Convert

class TryInto.AssociatedTypes (Self : Type) (T : Type) where
  Error : Type

attribute [reducible] TryInto.AssociatedTypes.Error

abbrev TryInto.Error :=
  TryInto.AssociatedTypes.Error

class TryInto (Self : Type) (T : Type)
  [associatedTypes : outParam (TryInto.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  try_into (Self) (T) :
    (Self -> RustM (Core_models.Result.Result T associatedTypes.Error))

class TryFrom.AssociatedTypes (Self : Type) (T : Type) where
  Error : Type

attribute [reducible] TryFrom.AssociatedTypes.Error

abbrev TryFrom.Error :=
  TryFrom.AssociatedTypes.Error

class TryFrom (Self : Type) (T : Type)
  [associatedTypes : outParam (TryFrom.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  try_from (Self) (T) :
    (T -> RustM (Core_models.Result.Result Self associatedTypes.Error))

end Core_models.Convert


namespace Core_models.Iter.Traits.Iterator

class Iterator.AssociatedTypes (Self : Type) where
  Item : Type

attribute [reducible] Iterator.AssociatedTypes.Item

abbrev Iterator.Item :=
  Iterator.AssociatedTypes.Item

class Iterator (Self : Type)
  [associatedTypes : outParam (Iterator.AssociatedTypes (Self : Type))]
  where
  next (Self) :
    (Self ->
    RustM (Rust_primitives.Hax.Tuple2
      Self
      (Core_models.Option.Option associatedTypes.Item)))

end Core_models.Iter.Traits.Iterator


namespace Core_models.Iter.Traits.Collect

class IntoIterator.AssociatedTypes (Self : Type) where
  IntoIter : Type

attribute [reducible] IntoIterator.AssociatedTypes.IntoIter

abbrev IntoIterator.IntoIter :=
  IntoIterator.AssociatedTypes.IntoIter

class IntoIterator (Self : Type)
  [associatedTypes : outParam (IntoIterator.AssociatedTypes (Self : Type))]
  where
  into_iter (Self) : (Self -> RustM associatedTypes.IntoIter)

end Core_models.Iter.Traits.Collect


namespace Core_models.Ops.Arith

class Add.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Add.AssociatedTypes.Output

abbrev Add.Output :=
  Add.AssociatedTypes.Output

class Add (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Add.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  add (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Sub.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Sub.AssociatedTypes.Output

abbrev Sub.Output :=
  Sub.AssociatedTypes.Output

class Sub (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Sub.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  sub (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Mul.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Mul.AssociatedTypes.Output

abbrev Mul.Output :=
  Mul.AssociatedTypes.Output

class Mul (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Mul.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  mul (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Div.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Div.AssociatedTypes.Output

abbrev Div.Output :=
  Div.AssociatedTypes.Output

class Div (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Div.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  div (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Neg.AssociatedTypes (Self : Type) where
  Output : Type

attribute [reducible] Neg.AssociatedTypes.Output

abbrev Neg.Output :=
  Neg.AssociatedTypes.Output

class Neg (Self : Type)
  [associatedTypes : outParam (Neg.AssociatedTypes (Self : Type))]
  where
  neg (Self) : (Self -> RustM associatedTypes.Output)

class Rem.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Rem.AssociatedTypes.Output

abbrev Rem.Output :=
  Rem.AssociatedTypes.Output

class Rem (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Rem.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  rem (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

end Core_models.Ops.Arith


namespace Core_models.Ops.Bit

class Shr.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Shr.AssociatedTypes.Output

abbrev Shr.Output :=
  Shr.AssociatedTypes.Output

class Shr (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Shr.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  shr (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Shl.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Shl.AssociatedTypes.Output

abbrev Shl.Output :=
  Shl.AssociatedTypes.Output

class Shl (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Shl.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  shl (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class BitXor.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] BitXor.AssociatedTypes.Output

abbrev BitXor.Output :=
  BitXor.AssociatedTypes.Output

class BitXor (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitXor.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitxor (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class BitAnd.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] BitAnd.AssociatedTypes.Output

abbrev BitAnd.Output :=
  BitAnd.AssociatedTypes.Output

class BitAnd (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitAnd.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitand (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

end Core_models.Ops.Bit


namespace Core_models.Ops.Index

class Index.AssociatedTypes (Self : Type) (Idx : Type) where
  Output : Type

attribute [reducible] Index.AssociatedTypes.Output

abbrev Index.Output :=
  Index.AssociatedTypes.Output

class Index (Self : Type) (Idx : Type)
  [associatedTypes : outParam (Index.AssociatedTypes (Self : Type) (Idx :
      Type))]
  where
  index (Self) (Idx) : (Self -> Idx -> RustM associatedTypes.Output)

end Core_models.Ops.Index


namespace Core_models.Ops.Function

class FnOnce.AssociatedTypes (Self : Type) (Args : Type) where
  Output : Type

attribute [reducible] FnOnce.AssociatedTypes.Output

abbrev FnOnce.Output :=
  FnOnce.AssociatedTypes.Output

class FnOnce (Self : Type) (Args : Type)
  [associatedTypes : outParam (FnOnce.AssociatedTypes (Self : Type) (Args :
      Type))]
  where
  call_once (Self) (Args) : (Self -> Args -> RustM associatedTypes.Output)

end Core_models.Ops.Function


namespace Core_models.Ops.Try_trait

class Try.AssociatedTypes (Self : Type) where
  Output : Type
  Residual : Type

attribute [reducible] Try.AssociatedTypes.Output

attribute [reducible] Try.AssociatedTypes.Residual

abbrev Try.Output :=
  Try.AssociatedTypes.Output

abbrev Try.Residual :=
  Try.AssociatedTypes.Residual

class Try (Self : Type)
  [associatedTypes : outParam (Try.AssociatedTypes (Self : Type))]
  where
  from_output (Self) : (associatedTypes.Output -> RustM Self)
  branch (Self) :
    (Self ->
    RustM (Core_models.Ops.Control_flow.ControlFlow
      associatedTypes.Residual
      associatedTypes.Output))

end Core_models.Ops.Try_trait


namespace Core_models.Ops.Deref

class Deref.AssociatedTypes (Self : Type) where
  Target : Type

attribute [reducible] Deref.AssociatedTypes.Target

abbrev Deref.Target :=
  Deref.AssociatedTypes.Target

class Deref (Self : Type)
  [associatedTypes : outParam (Deref.AssociatedTypes (Self : Type))]
  where
  deref (Self) : (Self -> RustM associatedTypes.Target)

end Core_models.Ops.Deref


namespace Core_models.Slice

class SliceIndex.AssociatedTypes (Self : Type) (T : Type) where
  Output : Type

attribute [reducible] SliceIndex.AssociatedTypes.Output

abbrev SliceIndex.Output :=
  SliceIndex.AssociatedTypes.Output

class SliceIndex (Self : Type) (T : Type)
  [associatedTypes : outParam (SliceIndex.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  get (Self) (T) :
    (Self -> T -> RustM (Core_models.Option.Option associatedTypes.Output))

end Core_models.Slice


namespace Core_models.Str.Traits

class FromStr.AssociatedTypes (Self : Type) where
  Err : Type

attribute [reducible] FromStr.AssociatedTypes.Err

abbrev FromStr.Err :=
  FromStr.AssociatedTypes.Err

class FromStr (Self : Type)
  [associatedTypes : outParam (FromStr.AssociatedTypes (Self : Type))]
  where
  from_str (Self) :
    (String -> RustM (Core_models.Result.Result Self associatedTypes.Err))

end Core_models.Str.Traits


namespace Core_models.Array

def Impl_23.map
    (T : Type)
    (N : usize)
    (F : Type)
    (U : Type)
    [trait_constr_map_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (s : (RustArray T N))
    (f : (T -> RustM U)) :
    RustM (RustArray U N) := do
  (Rust_primitives.Slice.array_map T U (N) (T -> RustM U) s f)

def from_fn
    (T : Type)
    (N : usize)
    (F : Type)
    [trait_constr_from_fn_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      usize]
    [trait_constr_from_fn_i0 : Core_models.Ops.Function.FnOnce
      F
      usize
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F usize
        by infer_instance
        with Output := T})]
    (f : (usize -> RustM T)) :
    RustM (RustArray T N) := do
  (Rust_primitives.Slice.array_from_fn T (N) (usize -> RustM T) f)

end Core_models.Array


namespace Core_models.Convert

@[reducible] instance Impl_1.AssociatedTypes
  (T : Type)
  (U : Type)
  [trait_constr_Impl_1_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_1_i0 : From U T ] :
  TryFrom.AssociatedTypes U T
  where
  Error := Infallible

instance Impl_1
  (T : Type)
  (U : Type)
  [trait_constr_Impl_1_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_1_i0 : From U T ] :
  TryFrom U T
  where
  try_from := fun (x : T) => do
    (pure (Core_models.Result.Result.Ok (← (From._from U T x))))

@[reducible] instance Impl_2.AssociatedTypes
  (T : Type)
  (U : Type)
  [trait_constr_Impl_2_associated_type_i0 : TryFrom.AssociatedTypes U T]
  [trait_constr_Impl_2_i0 : TryFrom U T ] :
  TryInto.AssociatedTypes T U
  where
  Error := (TryFrom.Error U T)

instance Impl_2
  (T : Type)
  (U : Type)
  [trait_constr_Impl_2_associated_type_i0 : TryFrom.AssociatedTypes U T]
  [trait_constr_Impl_2_i0 : TryFrom U T ] :
  TryInto T U
  where
  try_into := fun (self : T) => do (TryFrom.try_from U T self)

end Core_models.Convert


namespace Core_models.Iter.Traits.Iterator

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_1_i0 : Iterator I ] :
  Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes I
  where
  IntoIter := I

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_1_i0 : Iterator I ] :
  Core_models.Iter.Traits.Collect.IntoIterator I
  where
  into_iter := fun (self : I) => do (pure self)

end Core_models.Iter.Traits.Iterator


namespace Core_models.Iter.Traits.Collect

class FromIterator.AssociatedTypes (Self : Type) (A : Type) where

class FromIterator (Self : Type) (A : Type)
  [associatedTypes : outParam (FromIterator.AssociatedTypes (Self : Type) (A :
      Type))]
  where
  from_iter (Self) (A)
    (T : Type)
    [trait_constr_from_iter_associated_type_i1 : IntoIterator.AssociatedTypes T]
    [trait_constr_from_iter_i1 : IntoIterator T ] :
    (T -> RustM Self)

end Core_models.Iter.Traits.Collect


namespace Core_models.Iter.Adapters.Enumerate

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ] :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Enumerate I)
  where
  Item := (Rust_primitives.Hax.Tuple2
    usize
    (Core_models.Iter.Traits.Iterator.Iterator.Item I))

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ] :
  Core_models.Iter.Traits.Iterator.Iterator (Enumerate I)
  where
  next := fun (self : (Enumerate I)) => do
    let ⟨tmp0, out⟩ ←
      (Core_models.Iter.Traits.Iterator.Iterator.next I (Enumerate.iter self));
    let self : (Enumerate I) := {self with iter := tmp0};
    let ⟨self, hax_temp_output⟩ ←
      match out with
        | (Core_models.Option.Option.Some  a) =>
          let i : usize := (Enumerate.count self);
          let _ ←
            (Hax_lib.assume
              (← (Hax_lib.Prop.Constructors.from_bool
                (← (Rust_primitives.Hax.Machine_int.lt
                  (Enumerate.count self)
                  Core.Num.Impl_11.MAX)))));
          let self : (Enumerate I) :=
            {self with count := (← ((Enumerate.count self) +? (1 : usize)))};
          (pure (Rust_primitives.Hax.Tuple2.mk
            self
            (Core_models.Option.Option.Some
              (Rust_primitives.Hax.Tuple2.mk i a))))
        | (Core_models.Option.Option.None ) =>
          (pure (Rust_primitives.Hax.Tuple2.mk
            self
            Core_models.Option.Option.None));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

end Core_models.Iter.Adapters.Enumerate


namespace Core_models.Iter.Adapters.Step_by

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ] :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (StepBy I) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ] :
  Core_models.Iter.Traits.Iterator.Iterator (StepBy I) :=
  by constructor <;> exact Inhabited.default

end Core_models.Iter.Adapters.Step_by


namespace Core_models.Iter.Adapters.Map

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  (O : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := O})] :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Map I F)
  where
  Item := O

instance Impl_1
  (I : Type)
  (O : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := O})] :
  Core_models.Iter.Traits.Iterator.Iterator (Map I F)
  where
  next := fun (self : (Map I F)) => do
    let ⟨tmp0, out⟩ ←
      (Core_models.Iter.Traits.Iterator.Iterator.next I (Map.iter self));
    let self : (Map I F) := {self with iter := tmp0};
    let hax_temp_output : (Core_models.Option.Option O) ←
      match out with
        | (Core_models.Option.Option.Some  v) =>
          (pure (Core_models.Option.Option.Some
            (← (Core_models.Ops.Function.FnOnce.call_once
              F
              (Core_models.Iter.Traits.Iterator.Iterator.Item I)
              (Map.f self)
              v))))
        | (Core_models.Option.Option.None ) =>
          (pure Core_models.Option.Option.None);
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

end Core_models.Iter.Adapters.Map


namespace Core_models.Iter.Adapters.Take

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ] :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Take I)
  where
  Item := (Core_models.Iter.Traits.Iterator.Iterator.Item I)

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ] :
  Core_models.Iter.Traits.Iterator.Iterator (Take I)
  where
  next := fun (self : (Take I)) => do
    let ⟨self, hax_temp_output⟩ ←
      if (← (Rust_primitives.Hax.Machine_int.ne (Take.n self) (0 : usize))) then
        let self : (Take I) :=
          {self with n := (← ((Take.n self) -? (1 : usize)))};
        let ⟨tmp0, out⟩ ←
          (Core_models.Iter.Traits.Iterator.Iterator.next I (Take.iter self));
        let self : (Take I) := {self with iter := tmp0};
        (pure (Rust_primitives.Hax.Tuple2.mk self out))
      else
        (pure (Rust_primitives.Hax.Tuple2.mk
          self
          Core_models.Option.Option.None));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

end Core_models.Iter.Adapters.Take


namespace Core_models.Iter.Adapters.Flat_map

def Impl.new
    (I : Type)
    (U : Type)
    (F : Type)
    [trait_constr_new_associated_type_i0 :
      Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
      I]
    [trait_constr_new_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
    [trait_constr_new_associated_type_i1 :
      Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
      U]
    [trait_constr_new_i1 : Core_models.Iter.Traits.Iterator.Iterator U ]
    [trait_constr_new_associated_type_i2 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
    [trait_constr_new_i2 : Core_models.Ops.Function.FnOnce
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
    (f : F) :
    RustM (FlatMap I U F) := do
  (pure (FlatMap.mk
    (it := it)
    (f := f)
    (current := Core_models.Option.Option.None)))

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  (U : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    U]
  [trait_constr_Impl_1_i1 : Core_models.Iter.Traits.Iterator.Iterator U ]
  [trait_constr_Impl_1_associated_type_i2 :
    Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i2 : Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := U})] :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (FlatMap I U F) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  (U : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    U]
  [trait_constr_Impl_1_i1 : Core_models.Iter.Traits.Iterator.Iterator U ]
  [trait_constr_Impl_1_associated_type_i2 :
    Core_models.Ops.Function.FnOnce.AssociatedTypes
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i2 : Core_models.Ops.Function.FnOnce
    F
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    (associatedTypes := {
      show
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      by infer_instance
      with Output := U})] :
  Core_models.Iter.Traits.Iterator.Iterator (FlatMap I U F) :=
  by constructor <;> exact Inhabited.default

end Core_models.Iter.Adapters.Flat_map


namespace Core_models.Iter.Adapters.Flatten

structure Flatten
  (I : Type)
  [trait_constr_Flatten_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Flatten_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
  [trait_constr_Flatten_associated_type_i1 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [trait_constr_Flatten_i1 : Core_models.Iter.Traits.Iterator.Iterator
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    ]
  where
  it : I
  current : (Core_models.Option.Option
      (Core_models.Iter.Traits.Iterator.Iterator.Item I))

end Core_models.Iter.Adapters.Flatten


namespace Core_models.Iter.Traits.Iterator

class IteratorMethods.AssociatedTypes (Self : Type) where
  [trait_constr_IteratorMethods_i0 : Iterator.AssociatedTypes Self]

attribute [instance]
  IteratorMethods.AssociatedTypes.trait_constr_IteratorMethods_i0

class IteratorMethods (Self : Type)
  [associatedTypes : outParam (IteratorMethods.AssociatedTypes (Self : Type))]
  where
  [trait_constr_IteratorMethods_i0 : Iterator Self]
  fold (Self)
    (B : Type)
    (F : Type)
    [trait_constr_fold_associated_type_i1 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      (Rust_primitives.Hax.Tuple2 B (Iterator.Item Self))]
    [trait_constr_fold_i1 : Core_models.Ops.Function.FnOnce
      F
      (Rust_primitives.Hax.Tuple2 B (Iterator.Item Self))
      (associatedTypes := {
        show
          Core_models.Ops.Function.FnOnce.AssociatedTypes
          F
          (Rust_primitives.Hax.Tuple2 B (Iterator.Item Self))
        by infer_instance
        with Output := B})] :
    (Self -> B -> F -> RustM B)
  enumerate (Self) :
    (Self -> RustM (Core_models.Iter.Adapters.Enumerate.Enumerate Self))
  step_by (Self) :
    (Self -> usize -> RustM (Core_models.Iter.Adapters.Step_by.StepBy Self))
  map (Self)
    (O : Type)
    (F : Type)
    [trait_constr_map_associated_type_i1 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      (Iterator.Item Self)]
    [trait_constr_map_i1 : Core_models.Ops.Function.FnOnce
      F
      (Iterator.Item Self)
      (associatedTypes := {
        show
          Core_models.Ops.Function.FnOnce.AssociatedTypes
          F
          (Iterator.Item Self)
        by infer_instance
        with Output := O})] :
    (Self -> F -> RustM (Core_models.Iter.Adapters.Map.Map Self F))
  all (Self)
    (F : Type)
    [trait_constr_all_associated_type_i1 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      (Iterator.Item Self)]
    [trait_constr_all_i1 : Core_models.Ops.Function.FnOnce
      F
      (Iterator.Item Self)
      (associatedTypes := {
        show
          Core_models.Ops.Function.FnOnce.AssociatedTypes
          F
          (Iterator.Item Self)
        by infer_instance
        with Output := Bool})] :
    (Self -> F -> RustM Bool)
  take (Self) :
    (Self -> usize -> RustM (Core_models.Iter.Adapters.Take.Take Self))
  flat_map (Self)
    (U : Type)
    (F : Type)
    [trait_constr_flat_map_associated_type_i1 : Iterator.AssociatedTypes U]
    [trait_constr_flat_map_i1 : Iterator U ]
    [trait_constr_flat_map_associated_type_i2 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      (Iterator.Item Self)]
    [trait_constr_flat_map_i2 : Core_models.Ops.Function.FnOnce
      F
      (Iterator.Item Self)
      (associatedTypes := {
        show
          Core_models.Ops.Function.FnOnce.AssociatedTypes
          F
          (Iterator.Item Self)
        by infer_instance
        with Output := U})] :
    (Self -> F -> RustM (Core_models.Iter.Adapters.Flat_map.FlatMap Self U F))
  flatten (Self)
    [trait_constr_flatten_associated_type_i1 : Iterator.AssociatedTypes
      (Iterator.Item Self)]
    [trait_constr_flatten_i1 : Iterator (Iterator.Item Self) ] :
    (Self -> RustM (Core_models.Iter.Adapters.Flatten.Flatten Self))
  zip (Self)
    (I2 : Type)
    [trait_constr_zip_associated_type_i1 : Iterator.AssociatedTypes I2]
    [trait_constr_zip_i1 : Iterator I2 ] :
    (Self -> I2 -> RustM (Core_models.Iter.Adapters.Zip.Zip Self I2))

attribute [instance] IteratorMethods.trait_constr_IteratorMethods_i0

end Core_models.Iter.Traits.Iterator


namespace Core_models.Iter.Adapters.Flatten

def Impl.new
    (I : Type)
    [trait_constr_new_associated_type_i0 :
      Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
      I]
    [trait_constr_new_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
    [trait_constr_new_associated_type_i1 :
      Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
      (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
    [trait_constr_new_i1 : Core_models.Iter.Traits.Iterator.Iterator
      (Core_models.Iter.Traits.Iterator.Iterator.Item I)
      ]
    (it : I) :
    RustM (Flatten I) := do
  (pure (Flatten.mk (it := it) (current := Core_models.Option.Option.None)))

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : Core_models.Iter.Traits.Iterator.Iterator
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    ] :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Flatten I) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : Core_models.Iter.Traits.Iterator.Iterator
    (Core_models.Iter.Traits.Iterator.Iterator.Item I)
    ] :
  Core_models.Iter.Traits.Iterator.Iterator (Flatten I) :=
  by constructor <;> exact Inhabited.default

end Core_models.Iter.Adapters.Flatten


namespace Core_models.Iter.Adapters.Zip

def Impl.new
    (I1 : Type)
    (I2 : Type)
    [trait_constr_new_associated_type_i0 :
      Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
      I1]
    [trait_constr_new_i0 : Core_models.Iter.Traits.Iterator.Iterator I1 ]
    [trait_constr_new_associated_type_i1 :
      Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
      I2]
    [trait_constr_new_i1 : Core_models.Iter.Traits.Iterator.Iterator I2 ]
    (it1 : I1)
    (it2 : I2) :
    RustM (Zip I1 I2) := do
  (pure (Zip.mk (it1 := it1) (it2 := it2)))

end Core_models.Iter.Adapters.Zip


namespace Core_models.Iter.Traits.Iterator

@[reducible] instance Impl.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_i0 : Iterator I ] :
  IteratorMethods.AssociatedTypes I
  where

instance Impl
  (I : Type)
  [trait_constr_Impl_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_i0 : Iterator I ] :
  IteratorMethods I
  where
  fold :=
    fun
      (B : Type)
      (F : Type)
      [trait_constr_fold_associated_type_i1 :
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Rust_primitives.Hax.Tuple2 B (Iterator.Item I))]
      [trait_constr_fold_i1 : Core_models.Ops.Function.FnOnce
        F
        (Rust_primitives.Hax.Tuple2 B (Iterator.Item I))
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Rust_primitives.Hax.Tuple2 B (Iterator.Item I))
          by infer_instance
          with Output := B})] (self : I) (init : B) (f : F) => do
    (pure init)
  enumerate := fun (self : I) => do
    (Core_models.Iter.Adapters.Enumerate.Impl.new I self)
  step_by := fun (self : I) (step : usize) => do
    (Core_models.Iter.Adapters.Step_by.Impl.new I self step)
  map :=
    fun
      (O : Type)
      (F : Type)
      [trait_constr_map_associated_type_i1 :
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Iterator.Item I)]
      [trait_constr_map_i1 : Core_models.Ops.Function.FnOnce
        F
        (Iterator.Item I)
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Iterator.Item I)
          by infer_instance
          with Output := O})] (self : I) (f : F) => do
    (Core_models.Iter.Adapters.Map.Impl.new I F self f)
  all :=
    fun
      (F : Type)
      [trait_constr_all_associated_type_i1 :
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Iterator.Item I)]
      [trait_constr_all_i1 : Core_models.Ops.Function.FnOnce
        F
        (Iterator.Item I)
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Iterator.Item I)
          by infer_instance
          with Output := Bool})] (self : I) (f : F) => do
    (pure true)
  take := fun (self : I) (n : usize) => do
    (Core_models.Iter.Adapters.Take.Impl.new I self n)
  flat_map :=
    fun
      (U : Type)
      (F : Type)
      [trait_constr_flat_map_associated_type_i1 : Iterator.AssociatedTypes U]
      [trait_constr_flat_map_i1 : Iterator U ]
      [trait_constr_flat_map_associated_type_i2 :
        Core_models.Ops.Function.FnOnce.AssociatedTypes
        F
        (Iterator.Item I)]
      [trait_constr_flat_map_i2 : Core_models.Ops.Function.FnOnce
        F
        (Iterator.Item I)
        (associatedTypes := {
          show
            Core_models.Ops.Function.FnOnce.AssociatedTypes
            F
            (Iterator.Item I)
          by infer_instance
          with Output := U})] (self : I) (f : F) => do
    (Core_models.Iter.Adapters.Flat_map.Impl.new I U F self f)
  flatten :=
    fun
      [trait_constr_flatten_associated_type_i1 : Iterator.AssociatedTypes
        (Iterator.Item I)]
      [trait_constr_flatten_i1 : Iterator (Iterator.Item I) ] (self : I) => do
    (Core_models.Iter.Adapters.Flatten.Impl.new I self)
  zip :=
    fun
      (I2 : Type)
      [trait_constr_zip_associated_type_i1 : Iterator.AssociatedTypes I2]
      [trait_constr_zip_i1 : Iterator I2 ] (self : I) (it2 : I2) => do
    (Core_models.Iter.Adapters.Zip.Impl.new I I2 self it2)

end Core_models.Iter.Traits.Iterator


namespace Core_models.Iter.Adapters.Zip

@[instance] opaque Impl_1.AssociatedTypes
  (I1 : Type)
  (I2 : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I1]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I1 ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I2]
  [trait_constr_Impl_1_i1 : Core_models.Iter.Traits.Iterator.Iterator I2 ] :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Zip I1 I2) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I1 : Type)
  (I2 : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I1]
  [trait_constr_Impl_1_i0 : Core_models.Iter.Traits.Iterator.Iterator I1 ]
  [trait_constr_Impl_1_associated_type_i1 :
    Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes
    I2]
  [trait_constr_Impl_1_i1 : Core_models.Iter.Traits.Iterator.Iterator I2 ] :
  Core_models.Iter.Traits.Iterator.Iterator (Zip I1 I2) :=
  by constructor <;> exact Inhabited.default

end Core_models.Iter.Adapters.Zip


namespace Core_models.Ops.Function

class Fn.AssociatedTypes (Self : Type) (Args : Type) where
  [trait_constr_Fn_i0 : FnOnce.AssociatedTypes Self Args]

attribute [instance] Fn.AssociatedTypes.trait_constr_Fn_i0

class Fn (Self : Type) (Args : Type)
  [associatedTypes : outParam (Fn.AssociatedTypes (Self : Type) (Args : Type))]
  where
  [trait_constr_Fn_i0 : FnOnce Self Args]
  call (Self) (Args) : (Self -> Args -> RustM (FnOnce.Output Self Args))

attribute [instance] Fn.trait_constr_Fn_i0

@[reducible] instance Impl_2.AssociatedTypes (Arg : Type) (Out : Type) :
  FnOnce.AssociatedTypes (Arg -> RustM Out) Arg
  where
  Output := Out

instance Impl_2 (Arg : Type) (Out : Type) : FnOnce (Arg -> RustM Out) Arg where
  call_once := fun (self : (Arg -> RustM Out)) (arg : Arg) => do (self arg)

@[reducible] instance Impl.AssociatedTypes
  (Arg1 : Type)
  (Arg2 : Type)
  (Out : Type) :
  FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> RustM Out)
  (Rust_primitives.Hax.Tuple2 Arg1 Arg2)
  where
  Output := Out

instance Impl (Arg1 : Type) (Arg2 : Type) (Out : Type) :
  FnOnce (Arg1 -> Arg2 -> RustM Out) (Rust_primitives.Hax.Tuple2 Arg1 Arg2)
  where
  call_once :=
    fun
      (self : (Arg1 -> Arg2 -> RustM Out))
      (arg : (Rust_primitives.Hax.Tuple2 Arg1 Arg2)) => do
    (self
      (Rust_primitives.Hax.Tuple2._0 arg)
      (Rust_primitives.Hax.Tuple2._1 arg))

@[reducible] instance Impl_1.AssociatedTypes
  (Arg1 : Type)
  (Arg2 : Type)
  (Arg3 : Type)
  (Out : Type) :
  FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (Rust_primitives.Hax.Tuple3 Arg1 Arg2 Arg3)
  where
  Output := Out

instance Impl_1 (Arg1 : Type) (Arg2 : Type) (Arg3 : Type) (Out : Type) :
  FnOnce
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (Rust_primitives.Hax.Tuple3 Arg1 Arg2 Arg3)
  where
  call_once :=
    fun
      (self : (Arg1 -> Arg2 -> Arg3 -> RustM Out))
      (arg : (Rust_primitives.Hax.Tuple3 Arg1 Arg2 Arg3)) => do
    (self
      (Rust_primitives.Hax.Tuple3._0 arg)
      (Rust_primitives.Hax.Tuple3._1 arg)
      (Rust_primitives.Hax.Tuple3._2 arg))

end Core_models.Ops.Function


namespace Core_models.Ops.Deref

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Deref.AssociatedTypes T
  where
  Target := T

instance Impl (T : Type) : Deref T where
  deref := fun (self : T) => do (pure self)

end Core_models.Ops.Deref


namespace Core_models.Option

def Impl.is_some_and
    (T : Type)
    (F : Type)
    [trait_constr_is_some_and_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_is_some_and_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => (pure false)
    | (Option.Some  x) => (Core_models.Ops.Function.FnOnce.call_once F T f x)

def Impl.is_none_or
    (T : Type)
    (F : Type)
    [trait_constr_is_none_or_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_is_none_or_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => (pure true)
    | (Option.Some  x) => (Core_models.Ops.Function.FnOnce.call_once F T f x)

def Impl.unwrap_or_else
    (T : Type)
    (F : Type)
    [trait_constr_unwrap_or_else_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      Rust_primitives.Hax.Tuple0]
    [trait_constr_unwrap_or_else_i0 : Core_models.Ops.Function.FnOnce
      F
      Rust_primitives.Hax.Tuple0
      (associatedTypes := {
        show
          Core_models.Ops.Function.FnOnce.AssociatedTypes
          F
          Rust_primitives.Hax.Tuple0
        by infer_instance
        with Output := T})]
    (self : (Option T))
    (f : F) :
    RustM T := do
  match self with
    | (Option.Some  x) => (pure x)
    | (Option.None ) =>
      (Core_models.Ops.Function.FnOnce.call_once
        F
        Rust_primitives.Hax.Tuple0 f Rust_primitives.Hax.Tuple0.mk)

def Impl.map
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) =>
      (pure (Option.Some
        (← (Core_models.Ops.Function.FnOnce.call_once F T f x))))
    | (Option.None ) => (pure Option.None)

def Impl.map_or
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Option.None ) => (pure default)

def Impl.map_or_else
    (T : Type)
    (U : Type)
    (D : Type)
    (F : Type)
    [trait_constr_map_or_else_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_else_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      D
      Rust_primitives.Hax.Tuple0]
    [trait_constr_map_or_else_i1 : Core_models.Ops.Function.FnOnce
      D
      Rust_primitives.Hax.Tuple0
      (associatedTypes := {
        show
          Core_models.Ops.Function.FnOnce.AssociatedTypes
          D
          Rust_primitives.Hax.Tuple0
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Option.None ) =>
      (Core_models.Ops.Function.FnOnce.call_once
        D
        Rust_primitives.Hax.Tuple0 default Rust_primitives.Hax.Tuple0.mk)

def Impl.map_or_default
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_default_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_default_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_default_associated_type_i1 :
      Core_models.Default.Default.AssociatedTypes
      U]
    [trait_constr_map_or_default_i1 : Core_models.Default.Default U ]
    (self : (Option T))
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Option.None ) =>
      (Core_models.Default.Default.default U Rust_primitives.Hax.Tuple0.mk)

def Impl.ok_or_else
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      Rust_primitives.Hax.Tuple0]
    [trait_constr_ok_or_else_i0 : Core_models.Ops.Function.FnOnce
      F
      Rust_primitives.Hax.Tuple0
      (associatedTypes := {
        show
          Core_models.Ops.Function.FnOnce.AssociatedTypes
          F
          Rust_primitives.Hax.Tuple0
        by infer_instance
        with Output := E})]
    (self : (Option T))
    (err : F) :
    RustM (Core_models.Result.Result T E) := do
  match self with
    | (Option.Some  v) => (pure (Core_models.Result.Result.Ok v))
    | (Option.None ) =>
      (pure (Core_models.Result.Result.Err
        (← (Core_models.Ops.Function.FnOnce.call_once
          F
          Rust_primitives.Hax.Tuple0 err Rust_primitives.Hax.Tuple0.mk))))

def Impl.and_then
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_and_then_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := (Option U)})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) => (Core_models.Ops.Function.FnOnce.call_once F T f x)
    | (Option.None ) => (pure Option.None)

end Core_models.Option


namespace Core_models.Result

def Impl.map
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) =>
      (pure (Result.Ok
        (← (Core_models.Ops.Function.FnOnce.call_once F T op t))))
    | (Result.Err  e) => (pure (Result.Err e))

def Impl.map_or
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Result.Err  _e) => (pure default)

def Impl.map_or_else
    (T : Type)
    (E : Type)
    (U : Type)
    (D : Type)
    (F : Type)
    [trait_constr_map_or_else_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_else_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      D
      E]
    [trait_constr_map_or_else_i1 : Core_models.Ops.Function.FnOnce
      D
      E
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes D E
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => (Core_models.Ops.Function.FnOnce.call_once F T f t)
    | (Result.Err  e) =>
      (Core_models.Ops.Function.FnOnce.call_once D E default e)

def Impl.map_err
    (T : Type)
    (E : Type)
    (F : Type)
    (O : Type)
    [trait_constr_map_err_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      O
      E]
    [trait_constr_map_err_i0 : Core_models.Ops.Function.FnOnce
      O
      E
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes O E
        by infer_instance
        with Output := F})]
    (self : (Result T E))
    (op : O) :
    RustM (Result T F) := do
  match self with
    | (Result.Ok  t) => (pure (Result.Ok t))
    | (Result.Err  e) =>
      (pure (Result.Err
        (← (Core_models.Ops.Function.FnOnce.call_once O E op e))))

def Impl.and_then
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      Core_models.Ops.Function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_and_then_i0 : Core_models.Ops.Function.FnOnce
      F
      T
      (associatedTypes := {
        show Core_models.Ops.Function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := (Result U E)})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) => (Core_models.Ops.Function.FnOnce.call_once F T op t)
    | (Result.Err  e) => (pure (Result.Err e))

end Core_models.Result


namespace Core_models.Slice.Iter

@[reducible] instance Impl_2.AssociatedTypes (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Iter T)
  where
  Item := T

instance Impl_2 (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator (Iter T)
  where
  next := fun (self : (Iter T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← (Rust_primitives.Sequence.seq_len T (Iter._0 self)))
        (0 : usize))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self
          Core_models.Option.Option.None))
      else
        let res : T ← (Rust_primitives.Sequence.seq_first T (Iter._0 self));
        let self : (Iter T) :=
          {self
          with _0 := (← (Rust_primitives.Sequence.seq_slice T
            (Iter._0 self)
            (1 : usize)
            (← (Rust_primitives.Sequence.seq_len T (Iter._0 self)))))};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self
          (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl_3.AssociatedTypes (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (Chunks T)
  where
  Item := (RustSlice T)

instance Impl_3 (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator (Chunks T)
  where
  next := fun (self : (Chunks T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← (Rust_primitives.Slice.slice_length T (Chunks.elements self)))
        (0 : usize))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self
          Core_models.Option.Option.None))
      else
        if
        (← (Rust_primitives.Hax.Machine_int.lt
          (← (Rust_primitives.Slice.slice_length T (Chunks.elements self)))
          (Chunks.cs self))) then
          let res : (RustSlice T) := (Chunks.elements self);
          let self : (Chunks T) :=
            {self
            with elements := (← (Rust_primitives.Slice.slice_slice T
              (Chunks.elements self)
              (0 : usize)
              (0 : usize)))};
          (pure (Rust_primitives.Hax.Tuple2.mk
            self
            (Core_models.Option.Option.Some res)))
        else
          let ⟨res, new_elements⟩ ←
            (Rust_primitives.Slice.slice_split_at T
              (Chunks.elements self)
              (Chunks.cs self));
          let self : (Chunks T) := {self with elements := new_elements};
          (pure (Rust_primitives.Hax.Tuple2.mk
            self
            (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl_4.AssociatedTypes (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator.AssociatedTypes (ChunksExact T)
  where
  Item := (RustSlice T)

instance Impl_4 (T : Type) :
  Core_models.Iter.Traits.Iterator.Iterator (ChunksExact T)
  where
  next := fun (self : (ChunksExact T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (Rust_primitives.Hax.Machine_int.lt
        (← (Rust_primitives.Slice.slice_length T (ChunksExact.elements self)))
        (ChunksExact.cs self))) then
        (pure (Rust_primitives.Hax.Tuple2.mk
          self
          Core_models.Option.Option.None))
      else
        let ⟨res, new_elements⟩ ←
          (Rust_primitives.Slice.slice_split_at T
            (ChunksExact.elements self)
            (ChunksExact.cs self));
        let self : (ChunksExact T) := {self with elements := new_elements};
        (pure (Rust_primitives.Hax.Tuple2.mk
          self
          (Core_models.Option.Option.Some res)));
    (pure (Rust_primitives.Hax.Tuple2.mk self hax_temp_output))

end Core_models.Slice.Iter


namespace Core_models.Slice

def Impl.get
    (T : Type)
    (I : Type)
    [trait_constr_get_associated_type_i0 : SliceIndex.AssociatedTypes
      I
      (RustSlice T)]
    [trait_constr_get_i0 : SliceIndex I (RustSlice T) ]
    (s : (RustSlice T))
    (index : I) :
    RustM (Core_models.Option.Option (SliceIndex.Output I (RustSlice T))) := do
  (SliceIndex.get I (RustSlice T) index s)

end Core_models.Slice

