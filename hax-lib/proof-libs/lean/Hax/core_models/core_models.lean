
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

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Clone.AssociatedTypes T
  where

instance Impl (T : Type) : Clone T where
  clone := fun (self : T) => do (pure self)

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
  neq := fun (self : T) (y : T) => do ((← (PartialEq.eq T T self y)) ==? false)

--  See [`std::cmp::Reverse`]
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

--  See [`std::cmp::Ordering::is_eq`]
@[spec]
def Impl_54.is_eq (self : Ordering) : RustM Bool := do
  match self with | (Ordering.Equal ) => do (pure true) | _ => do (pure false)

--  See [`std::cmp::Ordering::is_ne`]
@[spec]
def Impl_54.is_ne (self : Ordering) : RustM Bool := do
  match self with
    | (Ordering.Less ) | (Ordering.Greater ) => do (pure true)
    | _ => do (pure false)

--  See [`std::cmp::Ordering::is_lt`]
@[spec]
def Impl_54.is_lt (self : Ordering) : RustM Bool := do
  match self with | (Ordering.Less ) => do (pure true) | _ => do (pure false)

--  See [`std::cmp::Ordering::is_gt`]
@[spec]
def Impl_54.is_gt (self : Ordering) : RustM Bool := do
  match self with | (Ordering.Greater ) => do (pure true) | _ => do (pure false)

--  See [`std::cmp::Ordering::is_le`]
@[spec]
def Impl_54.is_le (self : Ordering) : RustM Bool := do
  match self with
    | (Ordering.Less ) | (Ordering.Equal ) => do (pure true)
    | _ => do (pure false)

--  See [`std::cmp::Ordering::is_ge`]
@[spec]
def Impl_54.is_ge (self : Ordering) : RustM Bool := do
  match self with
    | (Ordering.Greater ) | (Ordering.Equal ) => do (pure true)
    | _ => do (pure false)

--  See [`std::cmp::Ordering::reverse`]
@[spec]
def Impl_54.reverse (self : Ordering) : RustM Ordering := do
  match self with
    | (Ordering.Less ) => do (pure Ordering.Greater)
    | (Ordering.Equal ) => do (pure Ordering.Equal)
    | (Ordering.Greater ) => do (pure Ordering.Less)

--  See [`std::cmp::Ordering::then`]
@[spec]
def Impl_54.then (self : Ordering) (other : Ordering) : RustM Ordering := do
  match self with | (Ordering.Equal ) => do (pure other) | _ => do (pure self)

--  See [`std::cmp::Ordering::then_with`]
@[spec]
def Impl_54.then_with
    (F : Type)
    [trait_constr_then_with_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_then_with_i0 : core.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := Ordering})]
    (self : Ordering)
    (f : F) :
    RustM Ordering := do
  match self with
    | (Ordering.Equal ) => do
      (core.ops.function.FnOnce.call_once
        F
        rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk)
    | _ => do (pure self)

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

--  See [`std::convert::Infallible`]
structure Infallible where
  -- no fields

@[reducible] instance Impl_3.AssociatedTypes (T : Type) :
  From.AssociatedTypes T T
  where

instance Impl_3 (T : Type) : From T T where
  _from := fun (x : T) => do (pure x)

--  See [`std::convert::AsRef`]
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

end core_models.convert


namespace core_models.default

--  See [`std::default::Default`]
class Default.AssociatedTypes (Self : Type) where

class Default (Self : Type)
  [associatedTypes : outParam (Default.AssociatedTypes (Self : Type))]
  where
  default (Self) : (rust_primitives.hax.Tuple0 -> RustM Self)

end core_models.default


namespace core_models.f32

--  See [`std::primitive::f32::abs`]
opaque Impl.abs (x : f64) : RustM f64

end core_models.f32


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


namespace core_models.iter.adapters.enumerate

--  See [`std::iter::Enumerate`]
structure Enumerate (I : Type) where
  iter : I
  count : usize

@[spec]
def Impl.new (I : Type) (iter : I) : RustM (Enumerate I) := do
  (pure (Enumerate.mk (iter := iter) (count := (0 : usize))))

end core_models.iter.adapters.enumerate


namespace core_models.iter.adapters.step_by

--  See [`std::iter::StepBy`]
structure StepBy (I : Type) where
  iter : I
  step : usize

@[spec]
def Impl.new (I : Type) (iter : I) (step : usize) : RustM (StepBy I) := do
  (pure (StepBy.mk (iter := iter) (step := step)))

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (StepBy I) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator (StepBy I) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.step_by


namespace core_models.iter.adapters.take

--  See [`std::iter::Take`]
structure Take (I : Type) where
  iter : I
  n : usize

@[spec]
def Impl.new (I : Type) (iter : I) (n : usize) : RustM (Take I) := do
  (pure (Take.mk (iter := iter) (n := n)))

end core_models.iter.adapters.take


namespace core_models.iter.adapters.zip

--  See [`std::iter::Zip`]
structure Zip (I1 : Type) (I2 : Type) where
  it1 : I1
  it2 : I2

@[spec]
def Impl.new
    (I1 : Type)
    (I2 : Type)
    [trait_constr_new_associated_type_i0 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      I1]
    [trait_constr_new_i0 : core_models.iter.traits.iterator.Iterator I1 ]
    [trait_constr_new_associated_type_i1 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      I2]
    [trait_constr_new_i1 : core_models.iter.traits.iterator.Iterator I2 ]
    (it1 : I1)
    (it2 : I2) :
    RustM (Zip I1 I2) := do
  (pure (Zip.mk (it1 := it1) (it2 := it2)))

@[instance] opaque Impl_1.AssociatedTypes
  (I1 : Type)
  (I2 : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I1]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I1 ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I2]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator I2 ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Zip I1 I2) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I1 : Type)
  (I2 : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I1]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I1 ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I2]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator I2 ] :
  core_models.iter.traits.iterator.Iterator (Zip I1 I2) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.zip


namespace core_models.iter.adapters.skip

--  See [`std::iter::Skip`]
structure Skip (I : Type) where
  iter : I
  n : usize

@[spec]
def Impl.new (I : Type) (iter : I) (n : usize) : RustM (Skip I) := do
  (pure (Skip.mk (iter := iter) (n := n)))

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Skip I) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator (Skip I) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.skip


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

--  See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
@[spec]
def Impl_6.wrapping_add (x : u8) (y : u8) : RustM u8 := do
  (rust_primitives.arithmetic.wrapping_add_u8 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_6.wrapping_sub (x : u8) (y : u8) : RustM u8 := do
  (rust_primitives.arithmetic.wrapping_sub_u8 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_6.wrapping_mul (x : u8) (y : u8) : RustM u8 := do
  (rust_primitives.arithmetic.wrapping_mul_u8 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_6.pow (x : u8) (exp : u32) : RustM u8 := do
  (rust_primitives.arithmetic.pow_u8 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_6.leading_zeros (x : u8) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_6.ilog2 (x : u8) : RustM u32

--  See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
@[spec]
def Impl_6.is_power_of_two (x : u8) : RustM Bool := do
  ((← (x !=? (0 : u8))) &&? (← ((← (x &&&? (← (x -? (1 : u8))))) ==? (0 : u8))))

--  See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
@[spec]
def Impl_7.wrapping_add (x : u16) (y : u16) : RustM u16 := do
  (rust_primitives.arithmetic.wrapping_add_u16 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_7.wrapping_sub (x : u16) (y : u16) : RustM u16 := do
  (rust_primitives.arithmetic.wrapping_sub_u16 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_7.wrapping_mul (x : u16) (y : u16) : RustM u16 := do
  (rust_primitives.arithmetic.wrapping_mul_u16 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_7.pow (x : u16) (exp : u32) : RustM u16 := do
  (rust_primitives.arithmetic.pow_u16 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_7.leading_zeros (x : u16) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_7.ilog2 (x : u16) : RustM u32

--  See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
@[spec]
def Impl_7.is_power_of_two (x : u16) : RustM Bool := do
  ((← (x !=? (0 : u16)))
    &&? (← ((← (x &&&? (← (x -? (1 : u16))))) ==? (0 : u16))))

--  See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
@[spec]
def Impl_8.wrapping_add (x : u32) (y : u32) : RustM u32 := do
  (rust_primitives.arithmetic.wrapping_add_u32 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_8.wrapping_sub (x : u32) (y : u32) : RustM u32 := do
  (rust_primitives.arithmetic.wrapping_sub_u32 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_8.wrapping_mul (x : u32) (y : u32) : RustM u32 := do
  (rust_primitives.arithmetic.wrapping_mul_u32 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_8.pow (x : u32) (exp : u32) : RustM u32 := do
  (rust_primitives.arithmetic.pow_u32 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_8.leading_zeros (x : u32) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_8.ilog2 (x : u32) : RustM u32

--  See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
@[spec]
def Impl_8.is_power_of_two (x : u32) : RustM Bool := do
  ((← (x !=? (0 : u32)))
    &&? (← ((← (x &&&? (← (x -? (1 : u32))))) ==? (0 : u32))))

--  See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
@[spec]
def Impl_9.wrapping_add (x : u64) (y : u64) : RustM u64 := do
  (rust_primitives.arithmetic.wrapping_add_u64 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_9.wrapping_sub (x : u64) (y : u64) : RustM u64 := do
  (rust_primitives.arithmetic.wrapping_sub_u64 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_9.wrapping_mul (x : u64) (y : u64) : RustM u64 := do
  (rust_primitives.arithmetic.wrapping_mul_u64 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_9.pow (x : u64) (exp : u32) : RustM u64 := do
  (rust_primitives.arithmetic.pow_u64 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_9.leading_zeros (x : u64) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_9.ilog2 (x : u64) : RustM u32

--  See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
@[spec]
def Impl_9.is_power_of_two (x : u64) : RustM Bool := do
  ((← (x !=? (0 : u64)))
    &&? (← ((← (x &&&? (← (x -? (1 : u64))))) ==? (0 : u64))))

--  See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
@[spec]
def Impl_10.wrapping_add (x : u128) (y : u128) : RustM u128 := do
  (rust_primitives.arithmetic.wrapping_add_u128 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_10.wrapping_sub (x : u128) (y : u128) : RustM u128 := do
  (rust_primitives.arithmetic.wrapping_sub_u128 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_10.wrapping_mul (x : u128) (y : u128) : RustM u128 := do
  (rust_primitives.arithmetic.wrapping_mul_u128 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_10.pow (x : u128) (exp : u32) : RustM u128 := do
  (rust_primitives.arithmetic.pow_u128 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_10.leading_zeros (x : u128) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_10.ilog2 (x : u128) : RustM u32

--  See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
@[spec]
def Impl_10.is_power_of_two (x : u128) : RustM Bool := do
  ((← (x !=? (0 : u128)))
    &&? (← ((← (x &&&? (← (x -? (1 : u128))))) ==? (0 : u128))))

--  See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
@[spec]
def Impl_11.wrapping_add (x : usize) (y : usize) : RustM usize := do
  (rust_primitives.arithmetic.wrapping_add_usize x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_11.wrapping_sub (x : usize) (y : usize) : RustM usize := do
  (rust_primitives.arithmetic.wrapping_sub_usize x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_11.wrapping_mul (x : usize) (y : usize) : RustM usize := do
  (rust_primitives.arithmetic.wrapping_mul_usize x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_11.pow (x : usize) (exp : u32) : RustM usize := do
  (rust_primitives.arithmetic.pow_usize x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_11.leading_zeros (x : usize) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_11.ilog2 (x : usize) : RustM u32

--  See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
@[spec]
def Impl_11.is_power_of_two (x : usize) : RustM Bool := do
  ((← (x !=? (0 : usize)))
    &&? (← ((← (x &&&? (← (x -? (1 : usize))))) ==? (0 : usize))))

@[spec]
def Impl_12.wrapping_add (x : i8) (y : i8) : RustM i8 := do
  (rust_primitives.arithmetic.wrapping_add_i8 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_12.wrapping_sub (x : i8) (y : i8) : RustM i8 := do
  (rust_primitives.arithmetic.wrapping_sub_i8 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_12.wrapping_mul (x : i8) (y : i8) : RustM i8 := do
  (rust_primitives.arithmetic.wrapping_mul_i8 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_12.pow (x : i8) (exp : u32) : RustM i8 := do
  (rust_primitives.arithmetic.pow_i8 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_12.leading_zeros (x : i8) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_12.ilog2 (x : i8) : RustM u32

--  See [`std::primitive::i8::signum`] (and similar for other signed integer types)
@[spec]
def Impl_12.signum (x : i8) : RustM i8 := do
  if (← (x >? (0 : i8))) then do
    (pure (1 : i8))
  else do
    if (← (x ==? (0 : i8))) then do (pure (0 : i8)) else do (pure (-1 : i8))

@[spec]
def Impl_13.wrapping_add (x : i16) (y : i16) : RustM i16 := do
  (rust_primitives.arithmetic.wrapping_add_i16 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_13.wrapping_sub (x : i16) (y : i16) : RustM i16 := do
  (rust_primitives.arithmetic.wrapping_sub_i16 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_13.wrapping_mul (x : i16) (y : i16) : RustM i16 := do
  (rust_primitives.arithmetic.wrapping_mul_i16 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_13.pow (x : i16) (exp : u32) : RustM i16 := do
  (rust_primitives.arithmetic.pow_i16 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_13.leading_zeros (x : i16) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_13.ilog2 (x : i16) : RustM u32

--  See [`std::primitive::i8::signum`] (and similar for other signed integer types)
@[spec]
def Impl_13.signum (x : i16) : RustM i16 := do
  if (← (x >? (0 : i16))) then do
    (pure (1 : i16))
  else do
    if (← (x ==? (0 : i16))) then do (pure (0 : i16)) else do (pure (-1 : i16))

@[spec]
def Impl_14.wrapping_add (x : i32) (y : i32) : RustM i32 := do
  (rust_primitives.arithmetic.wrapping_add_i32 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_14.wrapping_sub (x : i32) (y : i32) : RustM i32 := do
  (rust_primitives.arithmetic.wrapping_sub_i32 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_14.wrapping_mul (x : i32) (y : i32) : RustM i32 := do
  (rust_primitives.arithmetic.wrapping_mul_i32 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_14.pow (x : i32) (exp : u32) : RustM i32 := do
  (rust_primitives.arithmetic.pow_i32 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_14.leading_zeros (x : i32) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_14.ilog2 (x : i32) : RustM u32

--  See [`std::primitive::i8::signum`] (and similar for other signed integer types)
@[spec]
def Impl_14.signum (x : i32) : RustM i32 := do
  if (← (x >? (0 : i32))) then do
    (pure (1 : i32))
  else do
    if (← (x ==? (0 : i32))) then do (pure (0 : i32)) else do (pure (-1 : i32))

@[spec]
def Impl_15.wrapping_add (x : i64) (y : i64) : RustM i64 := do
  (rust_primitives.arithmetic.wrapping_add_i64 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_15.wrapping_sub (x : i64) (y : i64) : RustM i64 := do
  (rust_primitives.arithmetic.wrapping_sub_i64 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_15.wrapping_mul (x : i64) (y : i64) : RustM i64 := do
  (rust_primitives.arithmetic.wrapping_mul_i64 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_15.pow (x : i64) (exp : u32) : RustM i64 := do
  (rust_primitives.arithmetic.pow_i64 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_15.leading_zeros (x : i64) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_15.ilog2 (x : i64) : RustM u32

--  See [`std::primitive::i8::signum`] (and similar for other signed integer types)
@[spec]
def Impl_15.signum (x : i64) : RustM i64 := do
  if (← (x >? (0 : i64))) then do
    (pure (1 : i64))
  else do
    if (← (x ==? (0 : i64))) then do (pure (0 : i64)) else do (pure (-1 : i64))

@[spec]
def Impl_16.wrapping_add (x : i128) (y : i128) : RustM i128 := do
  (rust_primitives.arithmetic.wrapping_add_i128 x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_16.wrapping_sub (x : i128) (y : i128) : RustM i128 := do
  (rust_primitives.arithmetic.wrapping_sub_i128 x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_16.wrapping_mul (x : i128) (y : i128) : RustM i128 := do
  (rust_primitives.arithmetic.wrapping_mul_i128 x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_16.pow (x : i128) (exp : u32) : RustM i128 := do
  (rust_primitives.arithmetic.pow_i128 x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_16.leading_zeros (x : i128) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_16.ilog2 (x : i128) : RustM u32

--  See [`std::primitive::i8::signum`] (and similar for other signed integer types)
@[spec]
def Impl_16.signum (x : i128) : RustM i128 := do
  if (← (x >? (0 : i128))) then do
    (pure (1 : i128))
  else do
    if (← (x ==? (0 : i128))) then do
      (pure (0 : i128))
    else do
      (pure (-1 : i128))

@[spec]
def Impl_17.wrapping_add (x : isize) (y : isize) : RustM isize := do
  (rust_primitives.arithmetic.wrapping_add_isize x y)

--  See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
@[spec]
def Impl_17.wrapping_sub (x : isize) (y : isize) : RustM isize := do
  (rust_primitives.arithmetic.wrapping_sub_isize x y)

--  See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
@[spec]
def Impl_17.wrapping_mul (x : isize) (y : isize) : RustM isize := do
  (rust_primitives.arithmetic.wrapping_mul_isize x y)

--  See [`std::primitive::u8::pow`] (and similar for other integer types)
@[spec]
def Impl_17.pow (x : isize) (exp : u32) : RustM isize := do
  (rust_primitives.arithmetic.pow_isize x exp)

--  See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
opaque Impl_17.leading_zeros (x : isize) : RustM u32

--  See [`std::primitive::u8::ilog2`] (and similar for other integer types)
opaque Impl_17.ilog2 (x : isize) : RustM u32

--  See [`std::primitive::i8::signum`] (and similar for other signed integer types)
@[spec]
def Impl_17.signum (x : isize) : RustM isize := do
  if (← (x >? (0 : isize))) then do
    (pure (1 : isize))
  else do
    if (← (x ==? (0 : isize))) then do
      (pure (0 : isize))
    else do
      (pure (-1 : isize))

@[reducible] instance Impl_18.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u8
  where

instance Impl_18 : core_models.default.Default u8 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u8))

@[reducible] instance Impl_19.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u16
  where

instance Impl_19 : core_models.default.Default u16 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u16))

@[reducible] instance Impl_20.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u32
  where

instance Impl_20 : core_models.default.Default u32 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u32))

@[reducible] instance Impl_21.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u64
  where

instance Impl_21 : core_models.default.Default u64 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u64))

@[reducible] instance Impl_22.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u128
  where

instance Impl_22 : core_models.default.Default u128 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u128))

@[reducible] instance Impl_23.AssociatedTypes :
  core_models.default.Default.AssociatedTypes usize
  where

instance Impl_23 : core_models.default.Default usize where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : usize))

@[reducible] instance Impl_24.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i8
  where

instance Impl_24 : core_models.default.Default i8 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i8))

@[reducible] instance Impl_25.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i16
  where

instance Impl_25 : core_models.default.Default i16 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i16))

@[reducible] instance Impl_26.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i32
  where

instance Impl_26 : core_models.default.Default i32 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i32))

@[reducible] instance Impl_27.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i64
  where

instance Impl_27 : core_models.default.Default i64 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i64))

@[reducible] instance Impl_28.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i128
  where

instance Impl_28 : core_models.default.Default i128 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i128))

@[reducible] instance Impl_29.AssociatedTypes :
  core_models.default.Default.AssociatedTypes isize
  where

instance Impl_29 : core_models.default.Default isize where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : isize))

@[reducible] instance Impl_30.AssociatedTypes :
  core_models.default.Default.AssociatedTypes Bool
  where

instance Impl_30 : core_models.default.Default Bool where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure false)

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


namespace core_models.ops.bit

--  See [`std::ops::ShrAssign`]
class ShrAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class ShrAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (ShrAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  shr_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::ShlAssign`]
class ShlAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class ShlAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (ShlAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  shl_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::BitXorAssign`]
class BitXorAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class BitXorAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitXorAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitxor_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::BitAndAssign`]
class BitAndAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class BitAndAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitAndAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitand_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

--  See [`std::ops::BitOrAssign`]
class BitOrAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class BitOrAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitOrAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitor_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

end core_models.ops.bit


namespace core_models.ops.control_flow

--  See [`std::ops::ControlFlow`]
inductive ControlFlow (B : Type) (C : Type) : Type
| --  See [`std::ops::ControlFlow::Continue`]
    Continue : C -> ControlFlow (B : Type) (C : Type)
| --  See [`std::ops::ControlFlow::Break`]
    Break : B -> ControlFlow (B : Type) (C : Type)

end core_models.ops.control_flow


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


namespace core_models.ops.range

--  See [`std::ops::RangeTo`]
structure RangeTo (T : Type) where
  _end : T

--  See [`std::ops::RangeFrom`]
structure RangeFrom (T : Type) where
  start : T

--  See [`std::ops::Range`]
structure Range (T : Type) where
  start : T
  _end : T

--  See [`std::ops::RangeFull`]
structure RangeFull where
  -- no fields

--  See [`std::ops::RangeInclusive`]
structure RangeInclusive (T : Type) where
  start : T
  _end : T

end core_models.ops.range


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
      | (core_models.option.Option.Some  (Ordering.Less )) => do (pure true)
      | _ => do (pure false)
  le :=
    fun
      [trait_constr_le_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_le_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (core_models.option.Option.Some  (Ordering.Less )) |
        (core_models.option.Option.Some  (Ordering.Equal )) => do
        (pure true)
      | _ => do (pure false)
  gt :=
    fun
      [trait_constr_gt_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_gt_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (core_models.option.Option.Some  (Ordering.Greater )) => do (pure true)
      | _ => do (pure false)
  ge :=
    fun
      [trait_constr_ge_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_ge_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (core_models.option.Option.Some  (Ordering.Greater )) |
        (core_models.option.Option.Some  (Ordering.Equal )) => do
        (pure true)
      | _ => do (pure false)

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

end core_models.cmp


namespace core_models.iter.adapters.enumerate

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Enumerate I)
  where
  Item := (rust_primitives.hax.Tuple2
    usize
    (core_models.iter.traits.iterator.Iterator.Item I))

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator (Enumerate I)
  where
  next := fun (self : (Enumerate I)) => do
    let ⟨tmp0, out⟩ ←
      (core_models.iter.traits.iterator.Iterator.next I (Enumerate.iter self));
    let self : (Enumerate I) := {self with iter := tmp0};
    let ⟨self, hax_temp_output⟩ ←
      match out with
        | (core_models.option.Option.Some  a) => do
          let i : usize := (Enumerate.count self);
          let _ ←
            (hax_lib.assume
              (← (hax_lib.prop.constructors.from_bool
                (← ((Enumerate.count self) <? core.num.Impl_11.MAX)))));
          let self : (Enumerate I) :=
            {self with count := (← ((Enumerate.count self) +? (1 : usize)))};
          (pure (rust_primitives.hax.Tuple2.mk
            self
            (core_models.option.Option.Some
              (rust_primitives.hax.Tuple2.mk i a))))
        | (core_models.option.Option.None ) => do
          (pure (rust_primitives.hax.Tuple2.mk
            self
            core_models.option.Option.None));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end core_models.iter.adapters.enumerate


namespace core_models.iter.adapters.take

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Take I)
  where
  Item := (core_models.iter.traits.iterator.Iterator.Item I)

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator (Take I)
  where
  next := fun (self : (Take I)) => do
    let ⟨self, hax_temp_output⟩ ←
      if (← ((Take.n self) !=? (0 : usize))) then do
        let self : (Take I) :=
          {self with n := (← ((Take.n self) -? (1 : usize)))};
        let ⟨tmp0, out⟩ ←
          (core_models.iter.traits.iterator.Iterator.next I (Take.iter self));
        let self : (Take I) := {self with iter := tmp0};
        (pure (rust_primitives.hax.Tuple2.mk self out))
      else do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end core_models.iter.adapters.take


namespace core_models.iter.adapters.flatten

--  See [`std::iter::Flatten`]
structure Flatten
  (I : Type)
  [trait_constr_Flatten_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Flatten_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Flatten_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Flatten_i1 : core_models.iter.traits.iterator.Iterator
    (core_models.iter.traits.iterator.Iterator.Item I)
    ]
  where
  it : I
  current : (core_models.option.Option
      (core_models.iter.traits.iterator.Iterator.Item I))

@[spec]
def Impl.new
    (I : Type)
    [trait_constr_new_associated_type_i0 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      I]
    [trait_constr_new_i0 : core_models.iter.traits.iterator.Iterator I ]
    [trait_constr_new_associated_type_i1 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      (core_models.iter.traits.iterator.Iterator.Item I)]
    [trait_constr_new_i1 : core_models.iter.traits.iterator.Iterator
      (core_models.iter.traits.iterator.Iterator.Item I)
      ]
    (it : I) :
    RustM (Flatten I) := do
  (pure (Flatten.mk (it := it) (current := core_models.option.Option.None)))

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator
    (core_models.iter.traits.iterator.Iterator.Item I)
    ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Flatten I) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator
    (core_models.iter.traits.iterator.Iterator.Item I)
    ] :
  core_models.iter.traits.iterator.Iterator (Flatten I) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.flatten


namespace core_models.iter.adapters.chain

--  See [`std::iter::Chain`]
structure Chain (A : Type) (B : Type) where
  a : (core_models.option.Option A)
  b : B

@[spec]
def Impl.new
    (A : Type)
    (B : Type)
    [trait_constr_new_associated_type_i0 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      A]
    [trait_constr_new_i0 : core_models.iter.traits.iterator.Iterator A ]
    [trait_constr_new_associated_type_i1 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      B]
    [trait_constr_new_i1 : core_models.iter.traits.iterator.Iterator
      B
      (associatedTypes := {
        show core_models.iter.traits.iterator.Iterator.AssociatedTypes B
        by infer_instance
        with Item := (core_models.iter.traits.iterator.Iterator.Item A)})]
    (a : A)
    (b : B) :
    RustM (Chain A B) := do
  (pure (Chain.mk (a := (core_models.option.Option.Some a)) (b := b)))

@[instance] opaque Impl_1.AssociatedTypes
  (A : Type)
  (B : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    A]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator A ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    B]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator
    B
    (associatedTypes := {
      show core_models.iter.traits.iterator.Iterator.AssociatedTypes B
      by infer_instance
      with Item := (core_models.iter.traits.iterator.Iterator.Item A)})] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Chain A B) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (A : Type)
  (B : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    A]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator A ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    B]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator
    B
    (associatedTypes := {
      show core_models.iter.traits.iterator.Iterator.AssociatedTypes B
      by infer_instance
      with Item := (core_models.iter.traits.iterator.Iterator.Item A)})] :
  core_models.iter.traits.iterator.Iterator (Chain A B) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.chain


namespace core_models.num

--  See [`std::primitive::u8::checked_div`] (and similar for other integer types)
@[spec]
def Impl_6.checked_div (x : u8) (y : u8) :
    RustM (core_models.option.Option u8) := do
  if (← (y ==? (0 : u8))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
@[spec]
def Impl_6.checked_rem (x : u8) (y : u8) :
    RustM (core_models.option.Option u8) := do
  if (← (y ==? (0 : u8))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::u8::checked_div`] (and similar for other integer types)
@[spec]
def Impl_7.checked_div (x : u16) (y : u16) :
    RustM (core_models.option.Option u16) := do
  if (← (y ==? (0 : u16))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
@[spec]
def Impl_7.checked_rem (x : u16) (y : u16) :
    RustM (core_models.option.Option u16) := do
  if (← (y ==? (0 : u16))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::u8::checked_div`] (and similar for other integer types)
@[spec]
def Impl_8.checked_div (x : u32) (y : u32) :
    RustM (core_models.option.Option u32) := do
  if (← (y ==? (0 : u32))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
@[spec]
def Impl_8.checked_rem (x : u32) (y : u32) :
    RustM (core_models.option.Option u32) := do
  if (← (y ==? (0 : u32))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::u8::checked_div`] (and similar for other integer types)
@[spec]
def Impl_9.checked_div (x : u64) (y : u64) :
    RustM (core_models.option.Option u64) := do
  if (← (y ==? (0 : u64))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
@[spec]
def Impl_9.checked_rem (x : u64) (y : u64) :
    RustM (core_models.option.Option u64) := do
  if (← (y ==? (0 : u64))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::u8::checked_div`] (and similar for other integer types)
@[spec]
def Impl_10.checked_div (x : u128) (y : u128) :
    RustM (core_models.option.Option u128) := do
  if (← (y ==? (0 : u128))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
@[spec]
def Impl_10.checked_rem (x : u128) (y : u128) :
    RustM (core_models.option.Option u128) := do
  if (← (y ==? (0 : u128))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::u8::checked_div`] (and similar for other integer types)
@[spec]
def Impl_11.checked_div (x : usize) (y : usize) :
    RustM (core_models.option.Option usize) := do
  if (← (y ==? (0 : usize))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
@[spec]
def Impl_11.checked_rem (x : usize) (y : usize) :
    RustM (core_models.option.Option usize) := do
  if (← (y ==? (0 : usize))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
@[spec]
def Impl_12.checked_div (x : i8) (y : i8) :
    RustM (core_models.option.Option i8) := do
  if
  (← ((← (y ==? (0 : i8)))
    ||? (← ((← (x ==? Impl_12.MIN)) &&? (← (y ==? (-1 : i8))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
@[spec]
def Impl_12.checked_rem (x : i8) (y : i8) :
    RustM (core_models.option.Option i8) := do
  if
  (← ((← (y ==? (0 : i8)))
    ||? (← ((← (x ==? Impl_12.MIN)) &&? (← (y ==? (-1 : i8))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
@[spec]
def Impl_13.checked_div (x : i16) (y : i16) :
    RustM (core_models.option.Option i16) := do
  if
  (← ((← (y ==? (0 : i16)))
    ||? (← ((← (x ==? Impl_13.MIN)) &&? (← (y ==? (-1 : i16))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
@[spec]
def Impl_13.checked_rem (x : i16) (y : i16) :
    RustM (core_models.option.Option i16) := do
  if
  (← ((← (y ==? (0 : i16)))
    ||? (← ((← (x ==? Impl_13.MIN)) &&? (← (y ==? (-1 : i16))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
@[spec]
def Impl_14.checked_div (x : i32) (y : i32) :
    RustM (core_models.option.Option i32) := do
  if
  (← ((← (y ==? (0 : i32)))
    ||? (← ((← (x ==? Impl_14.MIN)) &&? (← (y ==? (-1 : i32))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
@[spec]
def Impl_14.checked_rem (x : i32) (y : i32) :
    RustM (core_models.option.Option i32) := do
  if
  (← ((← (y ==? (0 : i32)))
    ||? (← ((← (x ==? Impl_14.MIN)) &&? (← (y ==? (-1 : i32))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
@[spec]
def Impl_15.checked_div (x : i64) (y : i64) :
    RustM (core_models.option.Option i64) := do
  if
  (← ((← (y ==? (0 : i64)))
    ||? (← ((← (x ==? Impl_15.MIN)) &&? (← (y ==? (-1 : i64))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
@[spec]
def Impl_15.checked_rem (x : i64) (y : i64) :
    RustM (core_models.option.Option i64) := do
  if
  (← ((← (y ==? (0 : i64)))
    ||? (← ((← (x ==? Impl_15.MIN)) &&? (← (y ==? (-1 : i64))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
@[spec]
def Impl_16.checked_div (x : i128) (y : i128) :
    RustM (core_models.option.Option i128) := do
  if
  (← ((← (y ==? (0 : i128)))
    ||? (← ((← (x ==? Impl_16.MIN)) &&? (← (y ==? (-1 : i128))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
@[spec]
def Impl_16.checked_rem (x : i128) (y : i128) :
    RustM (core_models.option.Option i128) := do
  if
  (← ((← (y ==? (0 : i128)))
    ||? (← ((← (x ==? Impl_16.MIN)) &&? (← (y ==? (-1 : i128))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

--  See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
@[spec]
def Impl_17.checked_div (x : isize) (y : isize) :
    RustM (core_models.option.Option isize) := do
  if
  (← ((← (y ==? (0 : isize)))
    ||? (← ((← (x ==? Impl_17.MIN)) &&? (← (y ==? (-1 : isize))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x /? y))))

--  See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
@[spec]
def Impl_17.checked_rem (x : isize) (y : isize) :
    RustM (core_models.option.Option isize) := do
  if
  (← ((← (y ==? (0 : isize)))
    ||? (← ((← (x ==? Impl_17.MIN)) &&? (← (y ==? (-1 : isize))))))) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some (← (x %? y))))

end core_models.num


namespace core_models.option

--  See [`std::option::Option::is_some_and`]
@[spec]
def Impl.is_some_and
    (T : Type)
    (F : Type)
    [trait_constr_is_some_and_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_is_some_and_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => do (pure false)
    | (Option.Some  x) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x))

--  See [`std::option::Option::is_none_or`]
@[spec]
def Impl.is_none_or
    (T : Type)
    (F : Type)
    [trait_constr_is_none_or_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_is_none_or_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => do (pure true)
    | (Option.Some  x) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x))

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

--  See [`std::option::Option::unwrap_or_else`]
@[spec]
def Impl.unwrap_or_else
    (T : Type)
    (F : Type)
    [trait_constr_unwrap_or_else_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_unwrap_or_else_i0 : core.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
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
      (core.ops.function.FnOnce.call_once
        F
        rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk)

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

--  See [`std::option::Option::map`]
@[spec]
def Impl.map
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) => do
      (pure (Option.Some
        (← (core.ops.function.FnOnce.call_once
          F
          (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x)))))
    | (Option.None ) => do (pure Option.None)

--  See [`std::option::Option::map_or`]
@[spec]
def Impl.map_or
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_or_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t))
    | (Option.None ) => do (pure default)

--  See [`std::option::Option::map_or_else`]
@[spec]
def Impl.map_or_else
    (T : Type)
    (U : Type)
    (D : Type)
    (F : Type)
    [trait_constr_map_or_else_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_or_else_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      core.ops.function.FnOnce.AssociatedTypes
      D
      rust_primitives.hax.Tuple0]
    [trait_constr_map_or_else_i1 : core.ops.function.FnOnce
      D
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          D
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t))
    | (Option.None ) => do
      (core.ops.function.FnOnce.call_once
        D
        rust_primitives.hax.Tuple0 default rust_primitives.hax.Tuple0.mk)

--  See [`std::option::Option::map_or_default`]
@[spec]
def Impl.map_or_default
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_default_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_or_default_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
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
    | (Option.Some  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t))
    | (Option.None ) => do
      (core_models.default.Default.default U rust_primitives.hax.Tuple0.mk)

--  See [`std::option::Option::and_then`]
@[spec]
def Impl.and_then
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_and_then_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := (Option U)})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x))
    | (Option.None ) => do (pure Option.None)

--  See [`std::option::Option::take`]
-- 
--  Note: The interface in Rust is wrong, but is good after extraction.
--  We cannot make a useful model with the right interface so we lose the executability.
@[spec]
def Impl.take (T : Type) (self : (Option T)) :
    RustM (rust_primitives.hax.Tuple2 (Option T) (Option T)) := do
  (pure (rust_primitives.hax.Tuple2.mk Option.None self))

--  See [`std::option::Option::filter`]
opaque Impl.filter
    (T : Type)
    (P : Type)
    [trait_constr_filter_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      P
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_filter_i0 : core.ops.function.FnOnce
      P
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          P
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (predicate : P) :
    RustM (Option T)

--  See [`std::option::Option::or`]
@[spec]
def Impl.or (T : Type) (self : (Option T)) (optb : (Option T)) :
    RustM (Option T) := do
  match self with
    | (Option.Some  x) => do (pure (Option.Some x))
    | (Option.None ) => do (pure optb)

--  See [`std::option::Option::or_else`]
@[spec]
def Impl.or_else
    (T : Type)
    (F : Type)
    [trait_constr_or_else_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_or_else_i0 : core.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := (Option T)})]
    (self : (Option T))
    (f : F) :
    RustM (Option T) := do
  match self with
    | (Option.Some  x) => do (pure (Option.Some x))
    | (Option.None ) => do
      (core.ops.function.FnOnce.call_once
        F
        rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk)

--  See [`std::option::Option::xor`]
@[spec]
def Impl.xor (T : Type) (self : (Option T)) (optb : (Option T)) :
    RustM (Option T) := do
  match (rust_primitives.hax.Tuple2.mk self optb) with
    | ⟨(Option.Some  a), (Option.None )⟩ => do (pure (Option.Some a))
    | ⟨(Option.None ), (Option.Some  b)⟩ => do (pure (Option.Some b))
    | _ => do (pure Option.None)

--  See [`std::option::Option::zip`]
@[spec]
def Impl.zip (T : Type) (U : Type) (self : (Option T)) (other : (Option U)) :
    RustM (Option (rust_primitives.hax.Tuple2 T U)) := do
  match (rust_primitives.hax.Tuple2.mk self other) with
    | ⟨(Option.Some  a), (Option.Some  b)⟩ => do
      (pure (Option.Some (rust_primitives.hax.Tuple2.mk a b)))
    | _ => do (pure Option.None)

--  See [`std::option::Option::inspect`]
@[spec]
def Impl.inspect
    (T : Type)
    (F : Type)
    [trait_constr_inspect_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_inspect_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := rust_primitives.hax.Tuple0})]
    (self : (Option T))
    (f : F) :
    RustM (Option T) := do
  let _ ←
    match self with
      | (Option.Some  x) => do
        let _ ←
          (core.ops.function.FnOnce.call_once
            F
            (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x));
        (pure rust_primitives.hax.Tuple0.mk)
      | _ => do (pure rust_primitives.hax.Tuple0.mk);
  (pure self)

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

--  See [`std::option::Option::flatten`]
@[spec]
def Impl_1.flatten (T : Type) (self : (Option (Option T))) :
    RustM (Option T) := do
  match self with
    | (Option.Some  inner) => do (pure inner)
    | (Option.None ) => do (pure Option.None)

@[reducible] instance Impl_2.AssociatedTypes (T : Type) :
  core_models.default.Default.AssociatedTypes (Option T)
  where

instance Impl_2 (T : Type) : core_models.default.Default (Option T) where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure Option.None)

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


namespace core_models.cmp

--  See [`std::cmp::clamp`]
def clamp
    (T : Type)
    [trait_constr_clamp_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_clamp_i0 : Ord T ]
    (value : T)
    (min : T)
    (max : T) :
    RustM T := do
  let _ ←
    if (← (!? (← (Impl_54.is_le (← (Ord.cmp T min max)))))) then do
      (core_models.panicking.internal.panic rust_primitives.hax.Tuple0
        rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  match (← (Ord.cmp T value min)) with
    | (Ordering.Less ) => do (pure min)
    | (Ordering.Equal ) => do (pure value)
    | (Ordering.Greater ) => do
      match (← (Ord.cmp T value max)) with
        | (Ordering.Greater ) => do (pure max)
        | _ => do (pure value)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      clamp.spec
      (T : Type)
      [trait_constr_clamp_associated_type_i0 : Ord.AssociatedTypes T]
      [trait_constr_clamp_i0 : Ord T ]
      (value : T)
      (min : T)
      (max : T) :
    Spec
      (requires := do (Impl_54.is_le (← (Ord.cmp T min max))))
      (ensures := fun _ => pure True)
      (clamp (T : Type) (value : T) (min : T) (max : T)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [clamp] <;> bv_decide
}

end core_models.cmp


namespace core_models.hash

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Hash.AssociatedTypes T
  where

instance Impl (T : Type) : Hash T where
  hash :=
    fun
      (H : Type)
      [trait_constr_hash_associated_type_i0 : Hasher.AssociatedTypes H]
      [trait_constr_hash_i0 : Hasher H ] (self : T) (h : H) => do
    (core_models.panicking.internal.panic H rust_primitives.hax.Tuple0.mk)

end core_models.hash


namespace core_models.result

--  See [`std::result::Result`]
inductive Result (T : Type) (E : Type) : Type
| --  See [`std::result::Result::Ok`]
    Ok : T -> Result (T : Type) (E : Type)
| --  See [`std::result::Result::Err`]
    Err : E -> Result (T : Type) (E : Type)

end core_models.result


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

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Debug.AssociatedTypes T
  where

instance Impl (T : Type) : Debug T where
  dbg_fmt := fun (self : T) (f : Formatter) => do
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple2.mk f hax_temp_output))

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


namespace core_models.num

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_6.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u8 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_7.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u16 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_8.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u32 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_9.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u64 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_10.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u128 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_11.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result usize core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_12.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i8 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_13.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i16 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_14.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i32 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_15.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i64 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_16.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i128 core_models.num.error.ParseIntError)

--  See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
opaque Impl_17.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result isize core_models.num.error.ParseIntError)

end core_models.num


namespace core_models.option

--  See [`std::option::Option::ok_or`]
@[spec]
def Impl.ok_or (T : Type) (E : Type) (self : (Option T)) (err : E) :
    RustM (core_models.result.Result T E) := do
  match self with
    | (Option.Some  v) => do (pure (core_models.result.Result.Ok v))
    | (Option.None ) => do (pure (core_models.result.Result.Err err))

--  See [`std::option::Option::ok_or_else`]
@[spec]
def Impl.ok_or_else
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_ok_or_else_i0 : core.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
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
        (← (core.ops.function.FnOnce.call_once
          F
          rust_primitives.hax.Tuple0 err rust_primitives.hax.Tuple0.mk))))

end core_models.option


namespace core_models.result

--  See [`std::result::Result::is_ok`]
@[spec]
def Impl.is_ok (T : Type) (E : Type) (self : (Result T E)) : RustM Bool := do
  match self with | (Result.Ok  _) => do (pure true) | _ => do (pure false)

--  See [`std::result::Result::is_ok_and`]
@[spec]
def Impl.is_ok_and
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_is_ok_and_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_is_ok_and_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := Bool})]
    (self : (Result T E))
    (f : F) :
    RustM Bool := do
  match self with
    | (Result.Ok  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t))
    | (Result.Err  _) => do (pure false)

--  See [`std::result::Result::is_err`]
@[spec]
def Impl.is_err (T : Type) (E : Type) (self : (Result T E)) : RustM Bool := do
  (!? (← (Impl.is_ok T E self)))

--  See [`std::result::Result::is_err_and`]
@[spec]
def Impl.is_err_and
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_is_err_and_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 E)]
    [trait_constr_is_err_and_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 E)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 E)
        by infer_instance
        with Output := Bool})]
    (self : (Result T E))
    (f : F) :
    RustM Bool := do
  match self with
    | (Result.Ok  _) => do (pure false)
    | (Result.Err  e) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 E) f (rust_primitives.hax.Tuple1.mk e))

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

--  See [`std::result::Result::unwrap_or_else`]
@[spec]
def Impl.unwrap_or_else
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_unwrap_or_else_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 E)]
    [trait_constr_unwrap_or_else_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 E)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 E)
        by infer_instance
        with Output := T})]
    (self : (Result T E))
    (op : F) :
    RustM T := do
  match self with
    | (Result.Ok  t) => do (pure t)
    | (Result.Err  e) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 E) op (rust_primitives.hax.Tuple1.mk e))

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

--  See [`std::result::Result::map`]
@[spec]
def Impl.map
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) => do
      (pure (Result.Ok
        (← (core.ops.function.FnOnce.call_once
          F
          (rust_primitives.hax.Tuple1 T)
          op
          (rust_primitives.hax.Tuple1.mk t)))))
    | (Result.Err  e) => do (pure (Result.Err e))

--  See [`std::result::Result::map_or`]
@[spec]
def Impl.map_or
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_or_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t))
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
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_or_else_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      core.ops.function.FnOnce.AssociatedTypes
      D
      (rust_primitives.hax.Tuple1 E)]
    [trait_constr_map_or_else_i1 : core.ops.function.FnOnce
      D
      (rust_primitives.hax.Tuple1 E)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          D
          (rust_primitives.hax.Tuple1 E)
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t))
    | (Result.Err  e) => do
      (core.ops.function.FnOnce.call_once
        D
        (rust_primitives.hax.Tuple1 E)
        default
        (rust_primitives.hax.Tuple1.mk e))

--  See [`std::result::Result::map_or_default`]
@[spec]
def Impl.map_or_default
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_default_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_map_or_default_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
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
    | (Result.Ok  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t))
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
      core.ops.function.FnOnce.AssociatedTypes
      O
      (rust_primitives.hax.Tuple1 E)]
    [trait_constr_map_err_i0 : core.ops.function.FnOnce
      O
      (rust_primitives.hax.Tuple1 E)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          O
          (rust_primitives.hax.Tuple1 E)
        by infer_instance
        with Output := F})]
    (self : (Result T E))
    (op : O) :
    RustM (Result T F) := do
  match self with
    | (Result.Ok  t) => do (pure (Result.Ok t))
    | (Result.Err  e) => do
      (pure (Result.Err
        (← (core.ops.function.FnOnce.call_once
          O
          (rust_primitives.hax.Tuple1 E)
          op
          (rust_primitives.hax.Tuple1.mk e)))))

--  See [`std::result::Result::inspect`]
@[spec]
def Impl.inspect
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_inspect_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_inspect_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := rust_primitives.hax.Tuple0})]
    (self : (Result T E))
    (f : F) :
    RustM (Result T E) := do
  let _ ←
    match self with
      | (Result.Ok  t) => do
        let _ ←
          (core.ops.function.FnOnce.call_once
            F
            (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk t));
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
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 E)]
    [trait_constr_inspect_err_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 E)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 E)
        by infer_instance
        with Output := rust_primitives.hax.Tuple0})]
    (self : (Result T E))
    (f : F) :
    RustM (Result T E) := do
  let _ ←
    match self with
      | (Result.Err  e) => do
        let _ ←
          (core.ops.function.FnOnce.call_once
            F
            (rust_primitives.hax.Tuple1 E) f (rust_primitives.hax.Tuple1.mk e));
        (pure rust_primitives.hax.Tuple0.mk)
      | _ => do (pure rust_primitives.hax.Tuple0.mk);
  (pure self)

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

--  See [`std::result::Result::and_then`]
@[spec]
def Impl.and_then
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_and_then_i0 : core.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with Output := (Result U E)})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) => do
      (core.ops.function.FnOnce.call_once
        F
        (rust_primitives.hax.Tuple1 T) op (rust_primitives.hax.Tuple1.mk t))
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

--  See [`std::result::Result::or_else`]
@[spec]
def Impl.or_else
    (T : Type)
    (E : Type)
    (F : Type)
    (O : Type)
    [trait_constr_or_else_associated_type_i0 :
      core.ops.function.FnOnce.AssociatedTypes
      O
      (rust_primitives.hax.Tuple1 E)]
    [trait_constr_or_else_i0 : core.ops.function.FnOnce
      O
      (rust_primitives.hax.Tuple1 E)
      (associatedTypes := {
        show
          core.ops.function.FnOnce.AssociatedTypes
          O
          (rust_primitives.hax.Tuple1 E)
        by infer_instance
        with Output := (Result T F)})]
    (self : (Result T E))
    (op : O) :
    RustM (Result T F) := do
  match self with
    | (Result.Ok  t) => do (pure (Result.Ok t))
    | (Result.Err  e) => do
      (core.ops.function.FnOnce.call_once
        O
        (rust_primitives.hax.Tuple1 E) op (rust_primitives.hax.Tuple1.mk e))

--  See [`std::result::Result::expect_err`]
def Impl.expect_err (T : Type) (E : Type)
    (self : (Result T E))
    (_msg : String) :
    RustM E := do
  match self with
    | (Result.Ok  _) => do
      (core_models.panicking.internal.panic E rust_primitives.hax.Tuple0.mk)
    | (Result.Err  e) => do (pure e)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.expect_err.spec (T : Type) (E : Type)
      (self : (Result T E))
      (_msg : String) :
    Spec
      (requires := do (Impl.is_err T E self))
      (ensures := fun _ => pure True)
      (Impl.expect_err
        (T : Type)
        (E : Type)
        (self : (Result T E))
        (_msg : String)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.expect_err] <;> bv_decide
}

--  See [`std::result::Result::unwrap_err`]
def Impl.unwrap_err (T : Type) (E : Type) (self : (Result T E)) : RustM E := do
  match self with
    | (Result.Ok  _) => do
      (core_models.panicking.internal.panic E rust_primitives.hax.Tuple0.mk)
    | (Result.Err  e) => do (pure e)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl.unwrap_err.spec (T : Type) (E : Type) (self : (Result T E)) :
    Spec
      (requires := do (Impl.is_err T E self))
      (ensures := fun _ => pure True)
      (Impl.unwrap_err (T : Type) (E : Type) (self : (Result T E))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.unwrap_err] <;> bv_decide
}

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


namespace core_models.slice.iter

--  See [`std::slice::Chunks`]
structure Chunks (T : Type) where
  cs : usize
  elements : (RustSlice T)

@[spec]
def Impl.new (T : Type) (cs : usize) (elements : (RustSlice T)) :
    RustM (Chunks T) := do
  (pure (Chunks.mk (cs := cs) (elements := elements)))

--  See [`std::slice::ChunksExact`]
structure ChunksExact (T : Type) where
  cs : usize
  elements : (RustSlice T)

@[spec]
def Impl_1.new (T : Type) (cs : usize) (elements : (RustSlice T)) :
    RustM (ChunksExact T) := do
  (pure (ChunksExact.mk (cs := cs) (elements := elements)))

--  See [`std::slice::Iter`]
structure Iter (T : Type) where
  _0 : (rust_primitives.sequence.Seq T)

@[reducible] instance Impl_2.AssociatedTypes (T : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Iter T)
  where
  Item := T

instance Impl_2 (T : Type) :
  core_models.iter.traits.iterator.Iterator (Iter T)
  where
  next := fun (self : (Iter T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← ((← (rust_primitives.sequence.seq_len T (Iter._0 self)))
        ==? (0 : usize))) then do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None))
      else do
        let ⟨tmp0, out⟩ ←
          (rust_primitives.sequence.seq_remove T (Iter._0 self) (0 : usize));
        let self : (Iter T) := {self with _0 := tmp0};
        let res : T := out;
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.option.Option.Some res)));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl_3.AssociatedTypes (T : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Chunks T)
  where
  Item := (RustSlice T)

instance Impl_3 (T : Type) :
  core_models.iter.traits.iterator.Iterator (Chunks T)
  where
  next := fun (self : (Chunks T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← ((← (rust_primitives.slice.slice_length T (Chunks.elements self)))
        ==? (0 : usize))) then do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None))
      else do
        if
        (← ((← (rust_primitives.slice.slice_length T (Chunks.elements self)))
          <? (Chunks.cs self))) then do
          let res : (RustSlice T) := (Chunks.elements self);
          let self : (Chunks T) :=
            {self
            with elements := (← (rust_primitives.slice.slice_slice T
              (Chunks.elements self)
              (0 : usize)
              (0 : usize)))};
          (pure (rust_primitives.hax.Tuple2.mk
            self
            (core_models.option.Option.Some res)))
        else do
          let ⟨res, new_elements⟩ ←
            (rust_primitives.slice.slice_split_at T
              (Chunks.elements self)
              (Chunks.cs self));
          let self : (Chunks T) := {self with elements := new_elements};
          (pure (rust_primitives.hax.Tuple2.mk
            self
            (core_models.option.Option.Some res)));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl_4.AssociatedTypes (T : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (ChunksExact T)
  where
  Item := (RustSlice T)

instance Impl_4 (T : Type) :
  core_models.iter.traits.iterator.Iterator (ChunksExact T)
  where
  next := fun (self : (ChunksExact T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← ((← (rust_primitives.slice.slice_length T (ChunksExact.elements self)))
        <? (ChunksExact.cs self))) then do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None))
      else do
        let ⟨res, new_elements⟩ ←
          (rust_primitives.slice.slice_split_at T
            (ChunksExact.elements self)
            (ChunksExact.cs self));
        let self : (ChunksExact T) := {self with elements := new_elements};
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.option.Option.Some res)));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

--  See [`std::slice::Windows`]
structure Windows (T : Type) where
  size : usize
  elements : (RustSlice T)

@[spec]
def Impl_5.new (T : Type) (size : usize) (elements : (RustSlice T)) :
    RustM (Windows T) := do
  (pure (Windows.mk (size := size) (elements := elements)))

@[instance] opaque Impl_6.AssociatedTypes (T : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Windows T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 (T : Type) :
  core_models.iter.traits.iterator.Iterator (Windows T) :=
  by constructor <;> exact Inhabited.default

end core_models.slice.iter


namespace core_models.slice

--  See [`std::slice::len`]
@[spec]
def Impl.len (T : Type) (s : (RustSlice T)) : RustM usize := do
  (rust_primitives.slice.slice_length T s)

--  See [`std::slice::chunks`]
@[spec]
def Impl.chunks (T : Type) (s : (RustSlice T)) (cs : usize) :
    RustM (core_models.slice.iter.Chunks T) := do
  (core_models.slice.iter.Impl.new T cs s)

--  See [`std::slice::iter`]
@[spec]
def Impl.iter (T : Type) (s : (RustSlice T)) :
    RustM (core_models.slice.iter.Iter T) := do
  (pure (core_models.slice.iter.Iter.mk
    (← (rust_primitives.sequence.seq_from_slice T s))))

--  See [`std::slice::chunks_exact`]
@[spec]
def Impl.chunks_exact (T : Type) (s : (RustSlice T)) (cs : usize) :
    RustM (core_models.slice.iter.ChunksExact T) := do
  (core_models.slice.iter.Impl_1.new T cs s)

--  See [`std::slice::is_empty`]
@[spec]
def Impl.is_empty (T : Type) (s : (RustSlice T)) : RustM Bool := do
  ((← (Impl.len T s)) ==? (0 : usize))

--  See [`std::slice::contains`]
opaque Impl.contains
    (T : Type)
    [trait_constr_contains_associated_type_i0 :
      core.cmp.PartialEq.AssociatedTypes
      T
      T]
    [trait_constr_contains_i0 : core.cmp.PartialEq T T ]
    (s : (RustSlice T))
    (v : T) :
    RustM Bool

--  See [`std::slice::copy_within`]
opaque Impl.copy_within
    (T : Type)
    (R : Type)
    [trait_constr_copy_within_associated_type_i0 :
      core.marker.Copy.AssociatedTypes
      T]
    [trait_constr_copy_within_i0 : core.marker.Copy T ]
    (s : (RustSlice T))
    (src : R)
    (dest : usize) :
    RustM (RustSlice T)

--  See [`std::slice::binary_search`]
opaque Impl.binary_search (T : Type) (s : (RustSlice T)) (x : T) :
    RustM (core_models.result.Result usize usize)

--  See [`std::slice::first`]
@[spec]
def Impl.first (T : Type) (s : (RustSlice T)) :
    RustM (core_models.option.Option T) := do
  if (← (Impl.is_empty T s)) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some
      (← (rust_primitives.slice.slice_index T s (0 : usize)))))

--  See [`std::slice::last`]
@[spec]
def Impl.last (T : Type) (s : (RustSlice T)) :
    RustM (core_models.option.Option T) := do
  if (← (Impl.is_empty T s)) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some
      (← (rust_primitives.slice.slice_index T
        s
        (← ((← (Impl.len T s)) -? (1 : usize)))))))

--  See [`std::slice::reverse`]
opaque Impl.reverse (T : Type) (s : (RustSlice T)) : RustM (RustSlice T)

--  See [`std::slice::starts_with`]
opaque Impl.starts_with
    (T : Type)
    [trait_constr_starts_with_associated_type_i0 :
      core.cmp.PartialEq.AssociatedTypes
      T
      T]
    [trait_constr_starts_with_i0 : core.cmp.PartialEq T T ]
    (s : (RustSlice T))
    (needle : (RustSlice T)) :
    RustM Bool

--  See [`std::slice::ends_with`]
opaque Impl.ends_with
    (T : Type)
    [trait_constr_ends_with_associated_type_i0 :
      core.cmp.PartialEq.AssociatedTypes
      T
      T]
    [trait_constr_ends_with_i0 : core.cmp.PartialEq T T ]
    (s : (RustSlice T))
    (needle : (RustSlice T)) :
    RustM Bool

--  See [`std::slice::fill`]
opaque Impl.fill
    (T : Type)
    [trait_constr_fill_associated_type_i0 : core.clone.Clone.AssociatedTypes T]
    [trait_constr_fill_i0 : core.clone.Clone T ]
    (s : (RustSlice T))
    (value : T) :
    RustM (RustSlice T)

--  See [`std::slice::copy_from_slice`]
def Impl.copy_from_slice
    (T : Type)
    [trait_constr_copy_from_slice_associated_type_i0 :
      core.marker.Copy.AssociatedTypes
      T]
    [trait_constr_copy_from_slice_i0 : core.marker.Copy T ]
    (s : (RustSlice T))
    (src : (RustSlice T)) :
    RustM (RustSlice T) := do
  let s : (RustSlice T) ←
    (rust_primitives.slice.slice_clone_from_slice T s src);
  (pure s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.copy_from_slice.spec
      (T : Type)
      [trait_constr_copy_from_slice_associated_type_i0 :
        core.marker.Copy.AssociatedTypes
        T]
      [trait_constr_copy_from_slice_i0 : core.marker.Copy T ]
      (s : (RustSlice T))
      (src : (RustSlice T)) :
    Spec
      (requires := do ((← (Impl.len T s)) ==? (← (Impl.len T src))))
      (ensures := fun _ => pure True)
      (Impl.copy_from_slice
        (T : Type)
        (s : (RustSlice T))
        (src : (RustSlice T))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.copy_from_slice] <;> bv_decide
}

--  See [`std::slice::clone_from_slice`]
def Impl.clone_from_slice
    (T : Type)
    [trait_constr_clone_from_slice_associated_type_i0 :
      core.clone.Clone.AssociatedTypes
      T]
    [trait_constr_clone_from_slice_i0 : core.clone.Clone T ]
    (s : (RustSlice T))
    (src : (RustSlice T)) :
    RustM (RustSlice T) := do
  let s : (RustSlice T) ←
    (rust_primitives.slice.slice_clone_from_slice T s src);
  (pure s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.clone_from_slice.spec
      (T : Type)
      [trait_constr_clone_from_slice_associated_type_i0 :
        core.clone.Clone.AssociatedTypes
        T]
      [trait_constr_clone_from_slice_i0 : core.clone.Clone T ]
      (s : (RustSlice T))
      (src : (RustSlice T)) :
    Spec
      (requires := do ((← (Impl.len T s)) ==? (← (Impl.len T src))))
      (ensures := fun _ => pure True)
      (Impl.clone_from_slice
        (T : Type)
        (s : (RustSlice T))
        (src : (RustSlice T))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.clone_from_slice] <;> bv_decide
}

--  See [`std::slice::split_at`]
def Impl.split_at (T : Type) (s : (RustSlice T)) (mid : usize) :
    RustM (rust_primitives.hax.Tuple2 (RustSlice T) (RustSlice T)) := do
  (rust_primitives.slice.slice_split_at T s mid)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl.split_at.spec (T : Type) (s : (RustSlice T)) (mid : usize) :
    Spec
      (requires := do (mid <=? (← (Impl.len T s))))
      (ensures := fun _ => pure True)
      (Impl.split_at (T : Type) (s : (RustSlice T)) (mid : usize)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.split_at] <;> bv_decide
}

--  See [`std::slice::split_at_checked`]
@[spec]
def Impl.split_at_checked (T : Type) (s : (RustSlice T)) (mid : usize) :
    RustM
    (core_models.option.Option
      (rust_primitives.hax.Tuple2 (RustSlice T) (RustSlice T)))
    := do
  if (← (mid <=? (← (Impl.len T s)))) then do
    (pure (core_models.option.Option.Some (← (Impl.split_at T s mid))))
  else do
    (pure core_models.option.Option.None)

--  See [`std::slice::swap`]
opaque Impl.swap (T : Type) (s : (RustSlice T)) (a : usize) (b : usize) :
    RustM (RustSlice T)

--  See [`std::slice::windows`]
def Impl.windows (T : Type) (s : (RustSlice T)) (size : usize) :
    RustM (core_models.slice.iter.Windows T) := do
  let _ ←
    if (← (size ==? (0 : usize))) then do
      (core_models.panicking.internal.panic rust_primitives.hax.Tuple0
        rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  (core_models.slice.iter.Impl_5.new T size s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl.windows.spec (T : Type) (s : (RustSlice T)) (size : usize) :
    Spec
      (requires := do (size >? (0 : usize)))
      (ensures := fun _ => pure True)
      (Impl.windows (T : Type) (s : (RustSlice T)) (size : usize)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.windows] <;> bv_decide
}

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
  Item : Type
  IntoIter : Type

attribute [reducible] IntoIterator.AssociatedTypes.Item

attribute [reducible] IntoIterator.AssociatedTypes.IntoIter

abbrev IntoIterator.Item :=
  IntoIterator.AssociatedTypes.Item

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

--  See [`std::ops::BitOr`]
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

--  See [`std::ops::Not`]
class Not.AssociatedTypes (Self : Type) where
  Output : Type

attribute [reducible] Not.AssociatedTypes.Output

abbrev Not.Output :=
  Not.AssociatedTypes.Output

class Not (Self : Type)
  [associatedTypes : outParam (Not.AssociatedTypes (Self : Type))]
  where
  not (Self) : (Self -> RustM associatedTypes.Output)

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


namespace core_models.ops.deref

--  See [`std::ops::Deref`]
class Deref.AssociatedTypes (Self : Type) where
  Target : Type

attribute [reducible] Deref.AssociatedTypes.Target

abbrev Deref.Target :=
  Deref.AssociatedTypes.Target

class Deref (Self : Type)
  [associatedTypes : outParam (Deref.AssociatedTypes (Self : Type))]
  where
  deref (Self) : (Self -> RustM associatedTypes.Target)

end core_models.ops.deref


namespace core_models.slice.index

--  See [`std::slice::SliceIndex`]. We model the safe methods only;
--  `get_unchecked`/`get_unchecked_mut` would require raw-pointer
--  machinery and `*const`/`*mut` semantics we don\'t have. The
--  `&mut`-flavored `get_mut`/`index_mut` are also omitted — they
--  need a back-edge tuple shape and aren\'t required by anything
--  downstream Aeneas extraction emits in our test crate yet.
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
  index (Self) (T) : (Self -> T -> RustM associatedTypes.Output)

end core_models.slice.index


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
  try_from := fun (x : T) => do
    (pure (core_models.result.Result.Ok (← (From._from U T x))))

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
class FnMut.AssociatedTypes (Self : Type) (Args : Type) where
  [trait_constr_FnMut_i0 : FnOnce.AssociatedTypes Self Args]

attribute [instance_reducible, instance]
  FnMut.AssociatedTypes.trait_constr_FnMut_i0

class FnMut (Self : Type) (Args : Type)
  [associatedTypes : outParam (FnMut.AssociatedTypes (Self : Type) (Args :
      Type))]
  where
  [trait_constr_FnMut_i0 : FnOnce Self Args]
  call_mut (Self) (Args) : (Self -> Args -> RustM (FnOnce.Output Self Args))

attribute [instance_reducible, instance] FnMut.trait_constr_FnMut_i0

--  See [`std::ops::Fn`]
class Fn.AssociatedTypes (Self : Type) (Args : Type) where
  [trait_constr_Fn_i0 : FnMut.AssociatedTypes Self Args]

attribute [instance_reducible, instance] Fn.AssociatedTypes.trait_constr_Fn_i0

class Fn (Self : Type) (Args : Type)
  [associatedTypes : outParam (Fn.AssociatedTypes (Self : Type) (Args : Type))]
  where
  [trait_constr_Fn_i0 : FnMut Self Args]
  call (Self) (Args) : (Self -> Args -> RustM (FnOnce.Output Self Args))

attribute [instance_reducible, instance] Fn.trait_constr_Fn_i0

end core_models.ops.function


namespace core_models.ops.deref

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Deref.AssociatedTypes T
  where
  Target := T

instance Impl (T : Type) : Deref T where
  deref := fun (self : T) => do (pure self)

end core_models.ops.deref


namespace core_models.slice

--  See [`std::slice::get`]
@[spec]
def Impl.get
    (T : Type)
    (I : Type)
    [trait_constr_get_associated_type_i0 :
      core_models.slice.index.SliceIndex.AssociatedTypes
      I
      (RustSlice T)]
    [trait_constr_get_i0 : core_models.slice.index.SliceIndex I (RustSlice T) ]
    (s : (RustSlice T))
    (index : I) :
    RustM
    (core_models.option.Option
      (core_models.slice.index.SliceIndex.Output I (RustSlice T)))
    := do
  (core_models.slice.index.SliceIndex.get I (RustSlice T) index s)

end core_models.slice

