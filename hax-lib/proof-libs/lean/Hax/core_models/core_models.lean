
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax.core_models.prologue
import Hax.Tactic.HaxSpec
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace core_models.borrow

--  See [`std::borrow::Borrow`]
class Borrow.AssociatedTypes (Self : Type) (Borrowed : Type) where

class Borrow (Self : Type) (Borrowed : Type)
  [associatedTypes : outParam (Borrow.AssociatedTypes (Self : Type) (Borrowed :
      Type))]
  where
  borrow (Self) (Borrowed) : (Self -> RustM Borrowed)

end core_models.borrow


namespace core_models.clone

--  See [`std::clone::Clone`]
class Clone.AssociatedTypes (Self : Type) where

class Clone (Self : Type)
  [associatedTypes : outParam (Clone.AssociatedTypes (Self : Type))]
  where
  clone (Self) : (Self -> RustM Self)

@[spec]
def Impl.clone_hoisted (T : Type) (self : T) : RustM T := do (pure self)

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Clone.AssociatedTypes T
  where

instance Impl (T : Type) : Clone T where
  clone := (Impl.clone_hoisted T)

end core_models.clone


namespace core_models.cmp

--  See [`std::cmp::PartialEq`]
class PartialEq.AssociatedTypes (Self : Type) (Rhs : Type) where

class PartialEq (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialEq.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  eq (Self) (Rhs) : (Self -> Rhs -> RustM Bool)

--  See [`std::cmp::Eq`]
class Eq.AssociatedTypes (Self : Type) where
  [trait_constr_Eq_i0 : PartialEq.AssociatedTypes Self Self]

attribute [instance_reducible, instance] Eq.AssociatedTypes.trait_constr_Eq_i0

class Eq (Self : Type)
  [associatedTypes : outParam (Eq.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Eq_i0 : PartialEq Self Self]

attribute [instance_reducible, instance] Eq.trait_constr_Eq_i0

--  See [`std::cmp::Ordering`]
inductive Ordering : Type
| --  See [`std::cmp::Ordering::Less`]
    Less : Ordering
| --  See [`std::cmp::Ordering::Equal`]
    Equal : Ordering
| --  See [`std::cmp::Ordering::Greater`]
    Greater : Ordering

def Ordering.Less.AnonConst : isize := (-1 : isize)

def Ordering.Equal.AnonConst : isize := (0 : isize)

def Ordering.Greater.AnonConst : isize := (1 : isize)

@[spec]
def Ordering_cast_to_repr (x : Ordering) : RustM isize := do
  match x with
    | (Ordering.Less ) => do (pure Ordering.Less.AnonConst)
    | (Ordering.Equal ) => do (pure Ordering.Equal.AnonConst)
    | (Ordering.Greater ) => do (pure Ordering.Greater.AnonConst)

class Neq.AssociatedTypes (Self : Type) (Rhs : Type) where

class Neq (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Neq.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  neq (Self) (Rhs) : (Self -> Rhs -> RustM Bool)

@[spec]
def Impl.neq_hoisted
    (T : Type)
    [trait_constr_neq_hoisted_associated_type_i0 : PartialEq.AssociatedTypes
      T
      T]
    [trait_constr_neq_hoisted_i0 : PartialEq T T ]
    (self : T)
    (y : T) :
    RustM Bool := do
  ((← (PartialEq.eq T T self y)) ==? false)

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
  neq := (Impl.neq_hoisted T)

--  See [`std::cmp::Reverse`]
structure Reverse (T : Type) where
  _0 : T

@[spec]
def Impl_3.eq_hoisted
    (T : Type)
    [trait_constr_eq_hoisted_associated_type_i0 : PartialEq.AssociatedTypes T T]
    [trait_constr_eq_hoisted_i0 : PartialEq T T ]
    (self : (Reverse T))
    (other : (Reverse T)) :
    RustM Bool := do
  (PartialEq.eq T T (Reverse._0 other) (Reverse._0 self))

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
  eq := (Impl_3.eq_hoisted T)

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

end core_models.cmp


namespace core_models.convert

--  See [`std::convert::Into`]
class Into.AssociatedTypes (Self : Type) (T : Type) where

class Into (Self : Type) (T : Type)
  [associatedTypes : outParam (Into.AssociatedTypes (Self : Type) (T : Type))]
  where
  into (Self) (T) : (Self -> RustM T)

--  See [`std::convert::From`]
class From.AssociatedTypes (Self : Type) (T : Type) where

class From (Self : Type) (T : Type)
  [associatedTypes : outParam (From.AssociatedTypes (Self : Type) (T : Type))]
  where
  _from (Self) (T) : (T -> RustM Self)

@[spec]
def Impl.into_hoisted
    (T : Type)
    (U : Type)
    [trait_constr_into_hoisted_associated_type_i0 : From.AssociatedTypes U T]
    [trait_constr_into_hoisted_i0 : From U T ]
    (self : T) :
    RustM U := do
  (From._from U T self)

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
  into := (Impl.into_hoisted T U)

--  See [`std::convert::Infallible`]
structure Infallible where
  -- no fields

@[spec]
def Impl_3.from_hoisted (T : Type) (x : T) : RustM T := do (pure x)

@[reducible] instance Impl_3.AssociatedTypes (T : Type) :
  From.AssociatedTypes T T
  where

instance Impl_3 (T : Type) : From T T where
  _from := (Impl_3.from_hoisted T)

--  See [`std::convert::AsRef`]
class AsRef.AssociatedTypes (Self : Type) (T : Type) where

class AsRef (Self : Type) (T : Type)
  [associatedTypes : outParam (AsRef.AssociatedTypes (Self : Type) (T : Type))]
  where
  as_ref (Self) (T) : (Self -> RustM T)

@[spec]
def Impl_4.as_ref_hoisted (T : Type) (self : T) : RustM T := do (pure self)

@[reducible] instance Impl_4.AssociatedTypes (T : Type) :
  AsRef.AssociatedTypes T T
  where

instance Impl_4 (T : Type) : AsRef T T where
  as_ref := (Impl_4.as_ref_hoisted T)

end core_models.convert


namespace core_models.default

--  See [`std::default::Default`]
class Default.AssociatedTypes (Self : Type) where

class Default (Self : Type)
  [associatedTypes : outParam (Default.AssociatedTypes (Self : Type))]
  where
  default (Self) : (rust_primitives.hax.Tuple0 -> RustM Self)

end core_models.default


namespace core_models.fmt

--  See [`std::fmt::Error`]
structure Error where
  -- no fields

--  See [`std::fmt::Formatter`]
structure Formatter where
  -- no fields

--  See [`std::fmt::Arguments`]
structure Arguments where
  _0 : rust_primitives.hax.Tuple0

end core_models.fmt


namespace core_models.fmt.rt

opaque ArgumentType : Type

structure Argument where
  ty : ArgumentType

opaque Impl.new_display (T : Type) (x : T) : RustM Argument

opaque Impl.new_debug (T : Type) (x : T) : RustM Argument

opaque Impl.new_lower_hex (T : Type) (x : T) : RustM Argument

opaque Impl_1.new_binary (T : Type) (x : T) : RustM Argument

opaque Impl_1.new_const (T : Type) (U : Type) (x : T) (y : U) :
    RustM core_models.fmt.Arguments

opaque Impl_1.new_v1 (T : Type) (U : Type) (V : Type) (W : Type)
    (x : T)
    (y : U)
    (z : V)
    (t : W) :
    RustM core_models.fmt.Arguments

@[spec]
def Impl_1.none (_ : rust_primitives.hax.Tuple0) :
    RustM (RustArray Argument 0) := do
  (pure (RustArray.ofVec #v[]))

opaque Impl_1.new_v1_formatted (T : Type) (U : Type) (V : Type)
    (x : T)
    (y : U)
    (z : V) :
    RustM core_models.fmt.Arguments

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

end core_models.fmt.rt


namespace core_models.hash

--  See [`std::hash::Hasher`]
class Hasher.AssociatedTypes (Self : Type) where

class Hasher (Self : Type)
  [associatedTypes : outParam (Hasher.AssociatedTypes (Self : Type))]
  where

--  See [`std::hash::Hash`]
class Hash.AssociatedTypes (Self : Type) where

class Hash (Self : Type)
  [associatedTypes : outParam (Hash.AssociatedTypes (Self : Type))]
  where
  hash (Self)
    (H : Type)
    [trait_constr_hash_associated_type_i1 : Hasher.AssociatedTypes H]
    [trait_constr_hash_i1 : Hasher H ] :
    (Self -> H -> RustM H)

end core_models.hash


namespace core_models.hint

--  See [`std::hint::black_box`]
def black_box (T : Type) (dummy : T) : RustM T := do (pure dummy)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def black_box.spec (T : Type) (dummy : T) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (hax_lib.prop.Impl.from_bool true))
      (black_box (T : Type) (dummy : T)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [black_box] <;> bv_decide
}

--  See [`std::hint::must_use`]
def must_use (T : Type) (value : T) : RustM T := do (pure value)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def must_use.spec (T : Type) (value : T) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (hax_lib.prop.Impl.from_bool true))
      (must_use (T : Type) (value : T)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [must_use] <;> bv_decide
}

end core_models.hint


namespace core_models.marker

--  See [`std::marker::Copy`]
class Copy.AssociatedTypes (Self : Type) where
  [trait_constr_Copy_i0 : core_models.clone.Clone.AssociatedTypes Self]

attribute [instance_reducible, instance]
  Copy.AssociatedTypes.trait_constr_Copy_i0

class Copy (Self : Type)
  [associatedTypes : outParam (Copy.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Copy_i0 : core_models.clone.Clone Self]

attribute [instance_reducible, instance] Copy.trait_constr_Copy_i0

--  See [`std::marker::Send`]
class Send.AssociatedTypes (Self : Type) where

class Send (Self : Type)
  [associatedTypes : outParam (Send.AssociatedTypes (Self : Type))]
  where

--  See [`std::marker::Sync`]
class Sync.AssociatedTypes (Self : Type) where

class Sync (Self : Type)
  [associatedTypes : outParam (Sync.AssociatedTypes (Self : Type))]
  where

--  See [`std::marker::Sized`]
class Sized.AssociatedTypes (Self : Type) where

class Sized (Self : Type)
  [associatedTypes : outParam (Sized.AssociatedTypes (Self : Type))]
  where

--  See [`std::marker::StructuralPartialEq`]
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
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_3_i0 : core_models.clone.Clone T ] :
  Copy.AssociatedTypes T
  where

instance Impl_3
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_3_i0 : core_models.clone.Clone T ] :
  Copy T
  where

structure PhantomData (T : Type) where

end core_models.marker


namespace core_models.mem

--  See [`std::mem::forget`]
opaque forget (T : Type) (t : T) : RustM rust_primitives.hax.Tuple0

--  See [`std::mem::forget_unsized`]
opaque forget_unsized (T : Type) (t : T) : RustM rust_primitives.hax.Tuple0

--  See [`std::mem::size_of`]
opaque size_of (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

--  See [`std::mem::size_of_val`]
opaque size_of_val (T : Type) (val : T) : RustM usize

--  See [`std::mem::min_align_of`]
opaque min_align_of (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

--  See [`std::mem::min_align_of_val`]
opaque min_align_of_val (T : Type) (val : T) : RustM usize

--  See [`std::mem::align_of`]
opaque align_of (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

--  See [`std::mem::align_of_val`]
opaque align_of_val (T : Type) (val : T) : RustM usize

--  See [`std::mem::align_of_val_raw`]
opaque align_of_val_raw (T : Type) (val : T) : RustM usize

--  See [`std::mem::needs_drop`]
opaque needs_drop (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM Bool

--  See [`std::mem::uninitialized`]
opaque uninitialized (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM T

--  See [`std::mem::swap`]
opaque swap (T : Type) (x : T) (y : T) : RustM (rust_primitives.hax.Tuple2 T T)

--  See [`std::mem::replace`]
opaque replace (T : Type) (dest : T) (src : T) :
    RustM (rust_primitives.hax.Tuple2 T T)

--  See [`std::mem::drop`]
opaque drop (T : Type) (_x : T) : RustM rust_primitives.hax.Tuple0

--  See [`std::mem::take`]
opaque take (T : Type) (x : T) : RustM (rust_primitives.hax.Tuple2 T T)

--  See [`std::mem::transmute_copy`]
opaque transmute_copy (Src : Type) (Dst : Type) (src : Src) : RustM Dst

--  See [`std::mem::variant_count`]
opaque variant_count (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

--  See [`std::mem::zeroed`]
opaque zeroed (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM T

--  See [`std::mem::transmute`]
opaque transmute (Src : Type) (Dst : Type) (src : Src) : RustM Dst

end core_models.mem


namespace core_models.mem.manually_drop

structure ManuallyDrop (T : Type) where
  value : T

end core_models.mem.manually_drop


namespace core_models.num.error

--  See [`std::num::TryFromIntError`]
structure TryFromIntError where
  _0 : rust_primitives.hax.Tuple0

--  See [`std::num::IntErrorKind`]
structure IntErrorKind where
  -- no fields

--  See [`std::num::ParseIntError`]
structure ParseIntError where
  kind : IntErrorKind

end core_models.num.error


namespace core_models.num

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_6.leading_zeros (x : u8) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_6.ilog2 (x : u8) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_7.leading_zeros (x : u16) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_7.ilog2 (x : u16) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_8.leading_zeros (x : u32) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_8.ilog2 (x : u32) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_9.leading_zeros (x : u64) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_9.ilog2 (x : u64) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_10.leading_zeros (x : u128) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_10.ilog2 (x : u128) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_11.leading_zeros (x : usize) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_11.ilog2 (x : usize) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_12.leading_zeros (x : i8) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_12.ilog2 (x : i8) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_13.leading_zeros (x : i16) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_13.ilog2 (x : i16) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_14.leading_zeros (x : i32) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_14.ilog2 (x : i32) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_15.leading_zeros (x : i64) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_15.ilog2 (x : i64) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_16.leading_zeros (x : i128) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_16.ilog2 (x : i128) : RustM u32

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_17.leading_zeros (x : isize) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_17.ilog2 (x : isize) : RustM u32

@[spec]
def Impl_18.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM u8 := do
  (pure (0 : u8))

@[reducible] instance Impl_18.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u8
  where

instance Impl_18 : core_models.default.Default u8 where
  default := (Impl_18.default_hoisted)

@[spec]
def Impl_19.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM u16 := do
  (pure (0 : u16))

@[reducible] instance Impl_19.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u16
  where

instance Impl_19 : core_models.default.Default u16 where
  default := (Impl_19.default_hoisted)

@[spec]
def Impl_20.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM u32 := do
  (pure (0 : u32))

@[reducible] instance Impl_20.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u32
  where

instance Impl_20 : core_models.default.Default u32 where
  default := (Impl_20.default_hoisted)

@[spec]
def Impl_21.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM u64 := do
  (pure (0 : u64))

@[reducible] instance Impl_21.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u64
  where

instance Impl_21 : core_models.default.Default u64 where
  default := (Impl_21.default_hoisted)

@[spec]
def Impl_22.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM u128 := do
  (pure (0 : u128))

@[reducible] instance Impl_22.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u128
  where

instance Impl_22 : core_models.default.Default u128 where
  default := (Impl_22.default_hoisted)

@[spec]
def Impl_23.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM usize := do
  (pure (0 : usize))

@[reducible] instance Impl_23.AssociatedTypes :
  core_models.default.Default.AssociatedTypes usize
  where

instance Impl_23 : core_models.default.Default usize where
  default := (Impl_23.default_hoisted)

@[spec]
def Impl_24.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM i8 := do
  (pure (0 : i8))

@[reducible] instance Impl_24.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i8
  where

instance Impl_24 : core_models.default.Default i8 where
  default := (Impl_24.default_hoisted)

@[spec]
def Impl_25.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM i16 := do
  (pure (0 : i16))

@[reducible] instance Impl_25.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i16
  where

instance Impl_25 : core_models.default.Default i16 where
  default := (Impl_25.default_hoisted)

@[spec]
def Impl_26.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM i32 := do
  (pure (0 : i32))

@[reducible] instance Impl_26.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i32
  where

instance Impl_26 : core_models.default.Default i32 where
  default := (Impl_26.default_hoisted)

@[spec]
def Impl_27.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM i64 := do
  (pure (0 : i64))

@[reducible] instance Impl_27.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i64
  where

instance Impl_27 : core_models.default.Default i64 where
  default := (Impl_27.default_hoisted)

@[spec]
def Impl_28.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM i128 := do
  (pure (0 : i128))

@[reducible] instance Impl_28.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i128
  where

instance Impl_28 : core_models.default.Default i128 where
  default := (Impl_28.default_hoisted)

@[spec]
def Impl_29.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM isize := do
  (pure (0 : isize))

@[reducible] instance Impl_29.AssociatedTypes :
  core_models.default.Default.AssociatedTypes isize
  where

instance Impl_29 : core_models.default.Default isize where
  default := (Impl_29.default_hoisted)

end core_models.num


namespace core_models.ops.arith

--  See [`std::ops::AddAssign`]
class AddAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class AddAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (AddAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  add_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::SubAssign`]
class SubAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class SubAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (SubAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  sub_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::MulAssign`]
class MulAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class MulAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (MulAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  mul_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::DivAssign`]
class DivAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class DivAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (DivAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  div_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::RemAssign`]
class RemAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class RemAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (RemAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  rem_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

end core_models.ops.arith


namespace core_models.ops.control_flow

--  See [`std::ops::ControlFlow`]
inductive ControlFlow (B : Type) (C : Type) : Type
| --  See [`std::ops::ControlFlow::Continue`]
    Continue : C -> ControlFlow (B : Type) (C : Type)
| --  See [`std::ops::ControlFlow::Break`]
    Break : B -> ControlFlow (B : Type) (C : Type)

end core_models.ops.control_flow


namespace core_models.ops.function

@[spec]
def Impl_2.call_once_hoisted (Arg : Type) (Out : Type)
    (self : (Arg -> RustM Out))
    (arg : Arg) :
    RustM Out := do
  (self arg)

@[spec]
def Impl.call_once_hoisted (Arg1 : Type) (Arg2 : Type) (Out : Type)
    (self : (Arg1 -> Arg2 -> RustM Out))
    (arg : (rust_primitives.hax.Tuple2 Arg1 Arg2)) :
    RustM Out := do
  (self (rust_primitives.hax.Tuple2._0 arg) (rust_primitives.hax.Tuple2._1 arg))

@[spec]
def Impl_1.call_once_hoisted
    (Arg1 : Type)
    (Arg2 : Type)
    (Arg3 : Type)
    (Out : Type)
    (self : (Arg1 -> Arg2 -> Arg3 -> RustM Out))
    (arg : (rust_primitives.hax.Tuple3 Arg1 Arg2 Arg3)) :
    RustM Out := do
  (self
    (rust_primitives.hax.Tuple3._0 arg)
    (rust_primitives.hax.Tuple3._1 arg)
    (rust_primitives.hax.Tuple3._2 arg))

end core_models.ops.function


namespace core_models.ops.try_trait

--  See [`std::ops::FromResidual`]
class FromResidual.AssociatedTypes (Self : Type) (R : Type) where

class FromResidual (Self : Type) (R : Type)
  [associatedTypes : outParam (FromResidual.AssociatedTypes (Self : Type) (R :
      Type))]
  where
  from_residual (Self) (R) : (R -> RustM Self)

end core_models.ops.try_trait


namespace core_models.ops.drop

--  See [`std::ops::Drop`]
class Drop.AssociatedTypes (Self : Type) where

class Drop (Self : Type)
  [associatedTypes : outParam (Drop.AssociatedTypes (Self : Type))]
  where
  drop (Self) : (Self -> RustM Self)

end core_models.ops.drop


namespace core_models.option

--  See [`std::option::Option`]
inductive Option (T : Type) : Type
| --  See [`std::option::Option::Some`]
    Some : T -> Option (T : Type)
| --  See [`std::option::Option::None`]
    None : Option (T : Type)

end core_models.option


namespace core_models.cmp

--  See [`std::cmp::PartialOrd`]
class PartialOrd.AssociatedTypes (Self : Type) (Rhs : Type) where
  [trait_constr_PartialOrd_i0 : PartialEq.AssociatedTypes Self Rhs]

attribute [instance_reducible, instance]
  PartialOrd.AssociatedTypes.trait_constr_PartialOrd_i0

class PartialOrd (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialOrd.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  [trait_constr_PartialOrd_i0 : PartialEq Self Rhs]
  partial_cmp (Self) (Rhs) :
    (Self -> Rhs -> RustM (core_models.option.Option Ordering))

attribute [instance_reducible, instance] PartialOrd.trait_constr_PartialOrd_i0

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

@[spec]
def Impl_1.lt_hoisted
    (T : Type)
    [trait_constr_lt_hoisted_associated_type_i0 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_lt_hoisted_i0 : PartialOrd T T ]
    [trait_constr_lt_hoisted_associated_type_i1 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_lt_hoisted_i1 : PartialOrd T T ]
    (self : T)
    (y : T) :
    RustM Bool := do
  match (← (PartialOrd.partial_cmp T T self y)) with
    | (core_models.option.Option.Some  (Ordering.Less )) => do (pure true)
    | _ => do (pure false)

@[spec]
def Impl_1.le_hoisted
    (T : Type)
    [trait_constr_le_hoisted_associated_type_i0 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_le_hoisted_i0 : PartialOrd T T ]
    [trait_constr_le_hoisted_associated_type_i1 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_le_hoisted_i1 : PartialOrd T T ]
    (self : T)
    (y : T) :
    RustM Bool := do
  match (← (PartialOrd.partial_cmp T T self y)) with
    | (core_models.option.Option.Some  (Ordering.Less )) |
      (core_models.option.Option.Some  (Ordering.Equal )) => do
      (pure true)
    | _ => do (pure false)

@[spec]
def Impl_1.gt_hoisted
    (T : Type)
    [trait_constr_gt_hoisted_associated_type_i0 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_gt_hoisted_i0 : PartialOrd T T ]
    [trait_constr_gt_hoisted_associated_type_i1 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_gt_hoisted_i1 : PartialOrd T T ]
    (self : T)
    (y : T) :
    RustM Bool := do
  match (← (PartialOrd.partial_cmp T T self y)) with
    | (core_models.option.Option.Some  (Ordering.Greater )) => do (pure true)
    | _ => do (pure false)

@[spec]
def Impl_1.ge_hoisted
    (T : Type)
    [trait_constr_ge_hoisted_associated_type_i0 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_ge_hoisted_i0 : PartialOrd T T ]
    [trait_constr_ge_hoisted_associated_type_i1 : PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_ge_hoisted_i1 : PartialOrd T T ]
    (self : T)
    (y : T) :
    RustM Bool := do
  match (← (PartialOrd.partial_cmp T T self y)) with
    | (core_models.option.Option.Some  (Ordering.Greater )) |
      (core_models.option.Option.Some  (Ordering.Equal )) => do
      (pure true)
    | _ => do (pure false)

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
  lt := (Impl_1.lt_hoisted T)
  le := (Impl_1.le_hoisted T)
  gt := (Impl_1.gt_hoisted T)
  ge := (Impl_1.ge_hoisted T)

--  See [`std::cmp::Ord`]
class Ord.AssociatedTypes (Self : Type) where
  [trait_constr_Ord_i0 : Eq.AssociatedTypes Self]
  [trait_constr_Ord_i1 : PartialOrd.AssociatedTypes Self Self]

attribute [instance_reducible, instance] Ord.AssociatedTypes.trait_constr_Ord_i0

attribute [instance_reducible, instance] Ord.AssociatedTypes.trait_constr_Ord_i1

class Ord (Self : Type)
  [associatedTypes : outParam (Ord.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Ord_i0 : Eq Self]
  [trait_constr_Ord_i1 : PartialOrd Self Self]
  cmp (Self) : (Self -> Self -> RustM Ordering)

attribute [instance_reducible, instance] Ord.trait_constr_Ord_i0

attribute [instance_reducible, instance] Ord.trait_constr_Ord_i1

--  See [`std::cmp::max`]
@[spec]
def max
    (T : Type)
    [trait_constr_max_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_max_i0 : Ord T ]
    (v1 : T)
    (v2 : T) :
    RustM T := do
  match (← (Ord.cmp T v1 v2)) with
    | (Ordering.Greater ) => do (pure v1)
    | _ => do (pure v2)

--  See [`std::cmp::min`]
@[spec]
def min
    (T : Type)
    [trait_constr_min_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_min_i0 : Ord T ]
    (v1 : T)
    (v2 : T) :
    RustM T := do
  match (← (Ord.cmp T v1 v2)) with
    | (Ordering.Greater ) => do (pure v2)
    | _ => do (pure v1)

@[spec]
def Impl_2.partial_cmp_hoisted
    (T : Type)
    [trait_constr_partial_cmp_hoisted_associated_type_i0 :
      PartialOrd.AssociatedTypes
      T
      T]
    [trait_constr_partial_cmp_hoisted_i0 : PartialOrd T T ]
    (self : (Reverse T))
    (other : (Reverse T)) :
    RustM (core_models.option.Option Ordering) := do
  (PartialOrd.partial_cmp T T (Reverse._0 other) (Reverse._0 self))

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
  partial_cmp := (Impl_2.partial_cmp_hoisted T)

@[spec]
def Impl_5.cmp_hoisted
    (T : Type)
    [trait_constr_cmp_hoisted_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_cmp_hoisted_i0 : Ord T ]
    (self : (Reverse T))
    (other : (Reverse T)) :
    RustM Ordering := do
  (Ord.cmp T (Reverse._0 other) (Reverse._0 self))

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
  cmp := (Impl_5.cmp_hoisted T)

end core_models.cmp


namespace core_models.option

--  See [`std::option::Option::as_ref`]
@[spec]
def Impl.as_ref (T : Type) (self : (Option T)) : RustM (Option T) := do
  match self with
    | (Option.Some  x) => do (pure (Option.Some x))
    | (Option.None ) => do (pure Option.None)

--  See [`std::option::Option::unwrap_or`]
@[spec]
def Impl.unwrap_or (T : Type) (self : (Option T)) (default : T) : RustM T := do
  match self with
    | (Option.Some  x) => do (pure x)
    | (Option.None ) => do (pure default)

--  See [`std::option::Option::unwrap_or_default`]
@[spec]
def Impl.unwrap_or_default
    (T : Type)
    [trait_constr_unwrap_or_default_associated_type_i0 :
      core_models.default.Default.AssociatedTypes
      T]
    [trait_constr_unwrap_or_default_i0 : core_models.default.Default T ]
    (self : (Option T)) :
    RustM T := do
  match self with
    | (Option.Some  x) => do (pure x)
    | (Option.None ) => do
      (core_models.default.Default.default T rust_primitives.hax.Tuple0.mk)

--  See [`std::option::Option::take`]
-- 
--  Note: The interface in Rust is wrong, but is good after extraction.
--  We cannot make a useful model with the right interface so we lose the executability.
@[spec]
def Impl.take (T : Type) (self : (Option T)) :
    RustM (rust_primitives.hax.Tuple2 (Option T) (Option T)) := do
  (pure (rust_primitives.hax.Tuple2.mk Option.None self))

--  See [`std::option::Option::is_some`]
def Impl.is_some (T : Type) (self : (Option T)) : RustM Bool := do
  match self with | (Option.Some  _) => do (pure true) | _ => do (pure false)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl.is_some.spec (T : Type) (self : (Option T)) :
    Spec
      (requires := do pure True)
      (ensures := fun
          res => do
          (hax_lib.prop.constructors.implies
            (← (hax_lib.prop.constructors.from_bool res))
            (← (hax_lib.prop.Impl.from_bool true))))
      (Impl.is_some (T : Type) (self : (Option T))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.is_some] <;> bv_decide
}

--  See [`std::option::Option::is_none`]
@[spec]
def Impl.is_none (T : Type) (self : (Option T)) : RustM Bool := do
  ((← (Impl.is_some T self)) ==? false)

end core_models.option


namespace core_models.panicking

opaque panic_explicit (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Never

opaque panic (_msg : String) : RustM rust_primitives.hax.Never

opaque panic_fmt (_fmt : core_models.fmt.Arguments) :
    RustM rust_primitives.hax.Never

end core_models.panicking


namespace core_models.panicking.internal

opaque panic (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM T

end core_models.panicking.internal


namespace core_models.hash

@[spec]
def Impl.hash_hoisted
    (T : Type)
    (H : Type)
    [trait_constr_hash_hoisted_associated_type_i0 : Hasher.AssociatedTypes H]
    [trait_constr_hash_hoisted_i0 : Hasher H ]
    (self : T)
    (h : H) :
    RustM H := do
  (core_models.panicking.internal.panic H rust_primitives.hax.Tuple0.mk)

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Hash.AssociatedTypes T
  where

instance Impl (T : Type) : Hash T where
  hash :=
    fun
      
      (H : Type)
      [trait_constr__associated_type_i0 : Hasher.AssociatedTypes H]
      [trait_constr__i0 : Hasher H ]
      =>
    (Impl.hash_hoisted T H)

end core_models.hash


namespace core_models.result

--  See [`std::result::Result`]
inductive Result (T : Type) (E : Type) : Type
| --  See [`std::result::Result::Ok`]
    Ok : T -> Result (T : Type) (E : Type)
| --  See [`std::result::Result::Err`]
    Err : E -> Result (T : Type) (E : Type)

end core_models.result


namespace core_models.convert

@[spec]
def Impl_1.try_from_hoisted
    (T : Type)
    (U : Type)
    [trait_constr_try_from_hoisted_associated_type_i0 : From.AssociatedTypes
      U
      T]
    [trait_constr_try_from_hoisted_i0 : From U T ]
    (x : T) :
    RustM (core_models.result.Result U Infallible) := do
  (pure (core_models.result.Result.Ok (← (From._from U T x))))

end core_models.convert


namespace core_models.fmt

--  See [`std::fmt::Result`]
abbrev Result :
  Type :=
  (core_models.result.Result rust_primitives.hax.Tuple0 Error)

--  See [`std::fmt::Display`]
class Display.AssociatedTypes (Self : Type) where

class Display (Self : Type)
  [associatedTypes : outParam (Display.AssociatedTypes (Self : Type))]
  where
  fmt (Self) :
    (Self ->
    Formatter ->
    RustM (rust_primitives.hax.Tuple2
      Formatter
      (core_models.result.Result rust_primitives.hax.Tuple0 Error)))

--  See [`std::fmt::Debug`]
class Debug.AssociatedTypes (Self : Type) where

class Debug (Self : Type)
  [associatedTypes : outParam (Debug.AssociatedTypes (Self : Type))]
  where
  dbg_fmt (Self) :
    (Self ->
    Formatter ->
    RustM (rust_primitives.hax.Tuple2
      Formatter
      (core_models.result.Result rust_primitives.hax.Tuple0 Error)))

end core_models.fmt


namespace core_models.error

--  See [`std::error::Error`]
class Error.AssociatedTypes (Self : Type) where
  [trait_constr_Error_i0 : core_models.fmt.Display.AssociatedTypes Self]
  [trait_constr_Error_i1 : core_models.fmt.Debug.AssociatedTypes Self]

attribute [instance_reducible, instance]
  Error.AssociatedTypes.trait_constr_Error_i0

attribute [instance_reducible, instance]
  Error.AssociatedTypes.trait_constr_Error_i1

class Error (Self : Type)
  [associatedTypes : outParam (Error.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Error_i0 : core_models.fmt.Display Self]
  [trait_constr_Error_i1 : core_models.fmt.Debug Self]

attribute [instance_reducible, instance] Error.trait_constr_Error_i0

attribute [instance_reducible, instance] Error.trait_constr_Error_i1

end core_models.error


namespace core_models.fmt

@[spec]
def Impl.dbg_fmt_hoisted (T : Type) (self : T) (f : Formatter) :
    RustM
    (rust_primitives.hax.Tuple2
      Formatter
      (core_models.result.Result rust_primitives.hax.Tuple0 Error))
    := do
  let
    hax_temp_output : (core_models.result.Result
      rust_primitives.hax.Tuple0
      Error) :=
    (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
  (pure (rust_primitives.hax.Tuple2.mk f hax_temp_output))

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Debug.AssociatedTypes T
  where

instance Impl (T : Type) : Debug T where
  dbg_fmt := (Impl.dbg_fmt_hoisted T)

@[spec]
def Impl_11.write_fmt (f : Formatter) (args : Arguments) :
    RustM
    (rust_primitives.hax.Tuple2
      Formatter
      (core_models.result.Result rust_primitives.hax.Tuple0 Error))
    := do
  let
    hax_temp_output : (core_models.result.Result
      rust_primitives.hax.Tuple0
      Error) :=
    (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
  (pure (rust_primitives.hax.Tuple2.mk f hax_temp_output))

end core_models.fmt


namespace core_models.option

--  See [`std::option::Option::ok_or`]
@[spec]
def Impl.ok_or (T : Type) (E : Type) (self : (Option T)) (err : E) :
    RustM (core_models.result.Result T E) := do
  match self with
    | (Option.Some  v) => do (pure (core_models.result.Result.Ok v))
    | (Option.None ) => do (pure (core_models.result.Result.Err err))

end core_models.option


namespace core_models.result

--  See [`std::result::Result::is_ok`]
@[spec]
def Impl.is_ok (T : Type) (E : Type) (self : (Result T E)) : RustM Bool := do
  match self with | (Result.Ok  _) => do (pure true) | _ => do (pure false)

--  See [`std::result::Result::as_ref`]
@[spec]
def Impl.as_ref (T : Type) (E : Type) (self : (Result T E)) :
    RustM (Result T E) := do
  match self with
    | (Result.Ok  t) => do (pure (Result.Ok t))
    | (Result.Err  e) => do (pure (Result.Err e))

--  See [`std::result::Result::unwrap_or`]
@[spec]
def Impl.unwrap_or (T : Type) (E : Type) (self : (Result T E)) (default : T) :
    RustM T := do
  match self with
    | (Result.Ok  t) => do (pure t)
    | (Result.Err  _) => do (pure default)

--  See [`std::result::Result::unwrap_or_default`]
@[spec]
def Impl.unwrap_or_default
    (T : Type)
    (E : Type)
    [trait_constr_unwrap_or_default_associated_type_i0 :
      core_models.default.Default.AssociatedTypes
      T]
    [trait_constr_unwrap_or_default_i0 : core_models.default.Default T ]
    (self : (Result T E)) :
    RustM T := do
  match self with
    | (Result.Ok  t) => do (pure t)
    | (Result.Err  _) => do
      (core_models.default.Default.default T rust_primitives.hax.Tuple0.mk)

--  See [`std::result::Result::ok`]
@[spec]
def Impl.ok (T : Type) (E : Type) (self : (Result T E)) :
    RustM (core_models.option.Option T) := do
  match self with
    | (Result.Ok  x) => do (pure (core_models.option.Option.Some x))
    | (Result.Err  _) => do (pure core_models.option.Option.None)

--  See [`std::result::Result::err`]
@[spec]
def Impl.err (T : Type) (E : Type) (self : (Result T E)) :
    RustM (core_models.option.Option E) := do
  match self with
    | (Result.Ok  _) => do (pure core_models.option.Option.None)
    | (Result.Err  e) => do (pure (core_models.option.Option.Some e))

--  See [`std::result::Result::and`]
@[spec]
def Impl.and (T : Type) (E : Type) (U : Type)
    (self : (Result T E))
    (res : (Result U E)) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  _) => do (pure res)
    | (Result.Err  e) => do (pure (Result.Err e))

--  See [`std::result::Result::or`]
@[spec]
def Impl.or (T : Type) (E : Type) (F : Type)
    (self : (Result T E))
    (res : (Result T F)) :
    RustM (Result T F) := do
  match self with
    | (Result.Ok  t) => do (pure (Result.Ok t))
    | (Result.Err  _) => do (pure res)

--  See [`std::result::Result::cloned`]
@[spec]
def Impl_1.cloned
    (T : Type)
    (E : Type)
    [trait_constr_cloned_associated_type_i0 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_cloned_i0 : core_models.clone.Clone T ]
    (self : (Result T E)) :
    RustM (Result T E) := do
  match self with
    | (Result.Ok  t) => do
      (pure (Result.Ok (← (core_models.clone.Clone.clone T t))))
    | (Result.Err  e) => do (pure (Result.Err e))

--  See [`std::result::Result::transpose`]
@[spec]
def Impl_2.transpose (T : Type) (E : Type)
    (self : (Result (core_models.option.Option T) E)) :
    RustM (core_models.option.Option (Result T E)) := do
  match self with
    | (Result.Ok  (core_models.option.Option.Some  t)) => do
      (pure (core_models.option.Option.Some (Result.Ok t)))
    | (Result.Ok  (core_models.option.Option.None )) => do
      (pure core_models.option.Option.None)
    | (Result.Err  e) => do
      (pure (core_models.option.Option.Some (Result.Err e)))

--  See [`std::result::Result::flatten`]
@[spec]
def Impl_3.flatten (T : Type) (E : Type) (self : (Result (Result T E) E)) :
    RustM (Result T E) := do
  match self with
    | (Result.Ok  inner) => do (pure inner)
    | (Result.Err  e) => do (pure (Result.Err e))

end core_models.result


namespace core_models.slice

--  See [`std::slice::contains`]
opaque Impl.contains
    (T : Type)
    [trait_constr_contains_associated_type_i0 :
      core_models.cmp.PartialEq.AssociatedTypes
      T
      T]
    [trait_constr_contains_i0 : core_models.cmp.PartialEq T T ]
    (s : (RustSlice T))
    (v : T) :
    RustM Bool

--  See [`std::slice::copy_within`]
opaque Impl.copy_within
    (T : Type)
    (R : Type)
    [trait_constr_copy_within_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_copy_within_i0 : core_models.marker.Copy T ]
    (s : (RustSlice T))
    (src : R)
    (dest : usize) :
    RustM (RustSlice T)

end core_models.slice


namespace core_models.str.error

--  See [`std::str::Utf8Error`]
structure Utf8Error where
  -- no fields

end core_models.str.error


namespace core_models.str.converts

opaque from_utf8 (s : (RustSlice u8)) :
    RustM (core_models.result.Result String core_models.str.error.Utf8Error)

end core_models.str.converts


namespace core_models.str.iter

structure Split (T : Type) where
  _0 : T

end core_models.str.iter


namespace core_models.convert

--  See [`std::convert::TryInto`]
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
    (Self -> RustM (core_models.result.Result T associatedTypes.Error))

--  See [`std::convert::TryFrom`]
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
    (T -> RustM (core_models.result.Result Self associatedTypes.Error))

end core_models.convert


namespace core_models.iter.traits.collect

--  See [`std::iter::IntoIterator`]
class IntoIterator.AssociatedTypes (Self : Type) where
  IntoIter : Type

attribute [reducible] IntoIterator.AssociatedTypes.IntoIter

abbrev IntoIterator.IntoIter :=
  IntoIterator.AssociatedTypes.IntoIter

class IntoIterator (Self : Type)
  [associatedTypes : outParam (IntoIterator.AssociatedTypes (Self : Type))]
  where
  into_iter (Self) : (Self -> RustM associatedTypes.IntoIter)

end core_models.iter.traits.collect


namespace core_models.ops.arith

--  See [`std::ops::Add`]
class Add.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Add.AssociatedTypes.Output

abbrev Add.Output :=
  Add.AssociatedTypes.Output

class Add (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Add.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  add (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

--  See [`std::ops::Sub`]
class Sub.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Sub.AssociatedTypes.Output

abbrev Sub.Output :=
  Sub.AssociatedTypes.Output

class Sub (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Sub.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  sub (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

--  See [`std::ops::Mul`]
class Mul.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Mul.AssociatedTypes.Output

abbrev Mul.Output :=
  Mul.AssociatedTypes.Output

class Mul (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Mul.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  mul (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

--  See [`std::ops::Div`]
class Div.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Div.AssociatedTypes.Output

abbrev Div.Output :=
  Div.AssociatedTypes.Output

class Div (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Div.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  div (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

--  See [`std::ops::Neg`]
class Neg.AssociatedTypes (Self : Type) where
  Output : Type

attribute [reducible] Neg.AssociatedTypes.Output

abbrev Neg.Output :=
  Neg.AssociatedTypes.Output

class Neg (Self : Type)
  [associatedTypes : outParam (Neg.AssociatedTypes (Self : Type))]
  where
  neg (Self) : (Self -> RustM associatedTypes.Output)

--  See [`std::ops::Rem`]
class Rem.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Rem.AssociatedTypes.Output

abbrev Rem.Output :=
  Rem.AssociatedTypes.Output

class Rem (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Rem.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  rem (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

end core_models.ops.arith


namespace core_models.ops.bit

--  See [`std::ops::Shr`]
class Shr.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Shr.AssociatedTypes.Output

abbrev Shr.Output :=
  Shr.AssociatedTypes.Output

class Shr (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Shr.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  shr (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

--  See [`std::ops::Shl`]
class Shl.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Shl.AssociatedTypes.Output

abbrev Shl.Output :=
  Shl.AssociatedTypes.Output

class Shl (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Shl.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  shl (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

--  See [`std::ops::BitXor`]
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

--  See [`std::ops::BitAnd`]
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

class BitOr.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] BitOr.AssociatedTypes.Output

abbrev BitOr.Output :=
  BitOr.AssociatedTypes.Output

class BitOr (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitOr.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitor (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

end core_models.ops.bit


namespace core_models.ops.index

--  See [`std::ops::Index`]
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

end core_models.ops.index


namespace core_models.ops.function

--  See [`std::ops::FnOnce`]
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

end core_models.ops.function


namespace core_models.ops.try_trait

--  See [`std::ops::Try`]
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
    RustM (core_models.ops.control_flow.ControlFlow
      associatedTypes.Residual
      associatedTypes.Output))

end core_models.ops.try_trait


namespace core_models.slice

--  See [`std::slice::SliceIndex`]
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
    (Self -> T -> RustM (core_models.option.Option associatedTypes.Output))

end core_models.slice


namespace core_models.str.traits

class FromStr.AssociatedTypes (Self : Type) where
  Err : Type

attribute [reducible] FromStr.AssociatedTypes.Err

abbrev FromStr.Err :=
  FromStr.AssociatedTypes.Err

class FromStr (Self : Type)
  [associatedTypes : outParam (FromStr.AssociatedTypes (Self : Type))]
  where
  from_str (Self) :
    (String -> RustM (core_models.result.Result Self associatedTypes.Err))

end core_models.str.traits


namespace core_models.convert

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
  try_from := (Impl_1.try_from_hoisted T U)

@[spec]
def Impl_2.try_into_hoisted
    (T : Type)
    (U : Type)
    [trait_constr_try_into_hoisted_associated_type_i0 : TryFrom.AssociatedTypes
      U
      T]
    [trait_constr_try_into_hoisted_i0 : TryFrom U T ]
    (self : T) :
    RustM (core_models.result.Result U (TryFrom.Error U T)) := do
  (TryFrom.try_from U T self)

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
  try_into := (Impl_2.try_into_hoisted T U)

end core_models.convert


namespace core_models.iter.traits.collect

--  See [`std::iter::FromIterator`]
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

end core_models.iter.traits.collect


namespace core_models.ops.function

--  See [`std::ops::Fn`]
class Fn.AssociatedTypes (Self : Type) (Args : Type) where
  [trait_constr_Fn_i0 : FnOnce.AssociatedTypes Self Args]

attribute [instance_reducible, instance] Fn.AssociatedTypes.trait_constr_Fn_i0

class Fn (Self : Type) (Args : Type)
  [associatedTypes : outParam (Fn.AssociatedTypes (Self : Type) (Args : Type))]
  where
  [trait_constr_Fn_i0 : FnOnce Self Args]
  call (Self) (Args) : (Self -> Args -> RustM (FnOnce.Output Self Args))

attribute [instance_reducible, instance] Fn.trait_constr_Fn_i0

@[reducible] instance Impl_2.AssociatedTypes (Arg : Type) (Out : Type) :
  FnOnce.AssociatedTypes (Arg -> RustM Out) Arg
  where
  Output := Out

instance Impl_2 (Arg : Type) (Out : Type) : FnOnce (Arg -> RustM Out) Arg where
  call_once := (Impl_2.call_once_hoisted Arg Out)

@[reducible] instance Impl.AssociatedTypes
  (Arg1 : Type)
  (Arg2 : Type)
  (Out : Type) :
  FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> RustM Out)
  (rust_primitives.hax.Tuple2 Arg1 Arg2)
  where
  Output := Out

instance Impl (Arg1 : Type) (Arg2 : Type) (Out : Type) :
  FnOnce (Arg1 -> Arg2 -> RustM Out) (rust_primitives.hax.Tuple2 Arg1 Arg2)
  where
  call_once := (Impl.call_once_hoisted Arg1 Arg2 Out)

@[reducible] instance Impl_1.AssociatedTypes
  (Arg1 : Type)
  (Arg2 : Type)
  (Arg3 : Type)
  (Out : Type) :
  FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (rust_primitives.hax.Tuple3 Arg1 Arg2 Arg3)
  where
  Output := Out

instance Impl_1 (Arg1 : Type) (Arg2 : Type) (Arg3 : Type) (Out : Type) :
  FnOnce
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (rust_primitives.hax.Tuple3 Arg1 Arg2 Arg3)
  where
  call_once := (Impl_1.call_once_hoisted Arg1 Arg2 Arg3 Out)

end core_models.ops.function


namespace core_models.option

--  See [`std::option::Option::is_some_and`]
@[spec]
def Impl.is_some_and
    (T : Type)
    (F : Type)
    [trait_constr_is_some_and_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_is_some_and_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => do (pure false)
    | (Option.Some  x) => do (core_models.ops.function.FnOnce.call_once F T f x)

--  See [`std::option::Option::is_none_or`]
@[spec]
def Impl.is_none_or
    (T : Type)
    (F : Type)
    [trait_constr_is_none_or_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_is_none_or_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => do (pure true)
    | (Option.Some  x) => do (core_models.ops.function.FnOnce.call_once F T f x)

--  See [`std::option::Option::unwrap_or_else`]
@[spec]
def Impl.unwrap_or_else
    (T : Type)
    (F : Type)
    [trait_constr_unwrap_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_unwrap_or_else_i0 : core_models.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := T})]
    (self : (Option T))
    (f : F) :
    RustM T := do
  match self with
    | (Option.Some  x) => do (pure x)
    | (Option.None ) => do
      (core_models.ops.function.FnOnce.call_once
        F
        rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk)

--  See [`std::option::Option::map`]
@[spec]
def Impl.map
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) => do
      (pure (Option.Some
        (← (core_models.ops.function.FnOnce.call_once F T f x))))
    | (Option.None ) => do (pure Option.None)

--  See [`std::option::Option::map_or`]
@[spec]
def Impl.map_or
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Option.None ) => do (pure default)

--  See [`std::option::Option::map_or_else`]
@[spec]
def Impl.map_or_else
    (T : Type)
    (U : Type)
    (D : Type)
    (F : Type)
    [trait_constr_map_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_else_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      core_models.ops.function.FnOnce.AssociatedTypes
      D
      rust_primitives.hax.Tuple0]
    [trait_constr_map_or_else_i1 : core_models.ops.function.FnOnce
      D
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          D
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Option.None ) => do
      (core_models.ops.function.FnOnce.call_once
        D
        rust_primitives.hax.Tuple0 default rust_primitives.hax.Tuple0.mk)

--  See [`std::option::Option::map_or_default`]
@[spec]
def Impl.map_or_default
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_default_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_default_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_default_associated_type_i1 :
      core_models.default.Default.AssociatedTypes
      U]
    [trait_constr_map_or_default_i1 : core_models.default.Default U ]
    (self : (Option T))
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Option.None ) => do
      (core_models.default.Default.default U rust_primitives.hax.Tuple0.mk)

--  See [`std::option::Option::ok_or_else`]
@[spec]
def Impl.ok_or_else
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_ok_or_else_i0 : core_models.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := E})]
    (self : (Option T))
    (err : F) :
    RustM (core_models.result.Result T E) := do
  match self with
    | (Option.Some  v) => do (pure (core_models.result.Result.Ok v))
    | (Option.None ) => do
      (pure (core_models.result.Result.Err
        (← (core_models.ops.function.FnOnce.call_once
          F
          rust_primitives.hax.Tuple0 err rust_primitives.hax.Tuple0.mk))))

--  See [`std::option::Option::and_then`]
@[spec]
def Impl.and_then
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_and_then_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := (Option U)})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) => do (core_models.ops.function.FnOnce.call_once F T f x)
    | (Option.None ) => do (pure Option.None)

end core_models.option


namespace core_models.result

--  See [`std::result::Result::is_ok_and`]
@[spec]
def Impl.is_ok_and
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_is_ok_and_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_is_ok_and_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := Bool})]
    (self : (Result T E))
    (f : F) :
    RustM Bool := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Result.Err  _) => do (pure false)

--  See [`std::result::Result::is_err_and`]
@[spec]
def Impl.is_err_and
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_is_err_and_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      E]
    [trait_constr_is_err_and_i0 : core_models.ops.function.FnOnce
      F
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F E
        by infer_instance
        with Output := Bool})]
    (self : (Result T E))
    (f : F) :
    RustM Bool := do
  match self with
    | (Result.Ok  _) => do (pure false)
    | (Result.Err  e) => do (core_models.ops.function.FnOnce.call_once F E f e)

--  See [`std::result::Result::unwrap_or_else`]
@[spec]
def Impl.unwrap_or_else
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_unwrap_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      E]
    [trait_constr_unwrap_or_else_i0 : core_models.ops.function.FnOnce
      F
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F E
        by infer_instance
        with Output := T})]
    (self : (Result T E))
    (op : F) :
    RustM T := do
  match self with
    | (Result.Ok  t) => do (pure t)
    | (Result.Err  e) => do (core_models.ops.function.FnOnce.call_once F E op e)

--  See [`std::result::Result::map`]
@[spec]
def Impl.map
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) => do
      (pure (Result.Ok
        (← (core_models.ops.function.FnOnce.call_once F T op t))))
    | (Result.Err  e) => do (pure (Result.Err e))

--  See [`std::result::Result::map_or`]
@[spec]
def Impl.map_or
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Result.Err  _) => do (pure default)

--  See [`std::result::Result::map_or_else`]
@[spec]
def Impl.map_or_else
    (T : Type)
    (E : Type)
    (U : Type)
    (D : Type)
    (F : Type)
    [trait_constr_map_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_else_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      core_models.ops.function.FnOnce.AssociatedTypes
      D
      E]
    [trait_constr_map_or_else_i1 : core_models.ops.function.FnOnce
      D
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes D E
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Result.Err  e) => do
      (core_models.ops.function.FnOnce.call_once D E default e)

--  See [`std::result::Result::map_or_default`]
@[spec]
def Impl.map_or_default
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_default_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_default_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_default_associated_type_i1 :
      core_models.default.Default.AssociatedTypes
      U]
    [trait_constr_map_or_default_i1 : core_models.default.Default U ]
    (self : (Result T E))
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Result.Err  _) => do
      (core_models.default.Default.default U rust_primitives.hax.Tuple0.mk)

--  See [`std::result::Result::map_err`]
@[spec]
def Impl.map_err
    (T : Type)
    (E : Type)
    (F : Type)
    (O : Type)
    [trait_constr_map_err_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      O
      E]
    [trait_constr_map_err_i0 : core_models.ops.function.FnOnce
      O
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes O E
        by infer_instance
        with Output := F})]
    (self : (Result T E))
    (op : O) :
    RustM (Result T F) := do
  match self with
    | (Result.Ok  t) => do (pure (Result.Ok t))
    | (Result.Err  e) => do
      (pure (Result.Err
        (← (core_models.ops.function.FnOnce.call_once O E op e))))

--  See [`std::result::Result::inspect`]
@[spec]
def Impl.inspect
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_inspect_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_inspect_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := rust_primitives.hax.Tuple0})]
    (self : (Result T E))
    (f : F) :
    RustM (Result T E) := do
  let _ ←
    match self with
      | (Result.Ok  t) => do
        let _ ← (core_models.ops.function.FnOnce.call_once F T f t);
        (pure rust_primitives.hax.Tuple0.mk)
      | _ => do (pure rust_primitives.hax.Tuple0.mk);
  (pure self)

--  See [`std::result::Result::inspect_err`]
@[spec]
def Impl.inspect_err
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_inspect_err_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      E]
    [trait_constr_inspect_err_i0 : core_models.ops.function.FnOnce
      F
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F E
        by infer_instance
        with Output := rust_primitives.hax.Tuple0})]
    (self : (Result T E))
    (f : F) :
    RustM (Result T E) := do
  let _ ←
    match self with
      | (Result.Err  e) => do
        let _ ← (core_models.ops.function.FnOnce.call_once F E f e);
        (pure rust_primitives.hax.Tuple0.mk)
      | _ => do (pure rust_primitives.hax.Tuple0.mk);
  (pure self)

--  See [`std::result::Result::and_then`]
@[spec]
def Impl.and_then
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_and_then_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := (Result U E)})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T op t)
    | (Result.Err  e) => do (pure (Result.Err e))

--  See [`std::result::Result::or_else`]
@[spec]
def Impl.or_else
    (T : Type)
    (E : Type)
    (F : Type)
    (O : Type)
    [trait_constr_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      O
      E]
    [trait_constr_or_else_i0 : core_models.ops.function.FnOnce
      O
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes O E
        by infer_instance
        with Output := (Result T F)})]
    (self : (Result T E))
    (op : O) :
    RustM (Result T F) := do
  match self with
    | (Result.Ok  t) => do (pure (Result.Ok t))
    | (Result.Err  e) => do (core_models.ops.function.FnOnce.call_once O E op e)

end core_models.result


namespace core_models.slice

--  See [`std::slice::get`]
@[spec]
def Impl.get
    (T : Type)
    (I : Type)
    [trait_constr_get_associated_type_i0 : SliceIndex.AssociatedTypes
      I
      (RustSlice T)]
    [trait_constr_get_i0 : SliceIndex I (RustSlice T) ]
    (s : (RustSlice T))
    (index : I) :
    RustM (core_models.option.Option (SliceIndex.Output I (RustSlice T))) := do
  (SliceIndex.get I (RustSlice T) index s)

end core_models.slice

