/-
  Scalar trait instances for the Aeneas library.
  Imported after Types.lean which provides the trait structure definitions.
-/
import CoreModels.Core.Types
import CoreModels.Alloc.Types

namespace CoreModels.core

open Aeneas.Std Result

/-! ## Scalar PartialEq / PartialOrd instances -/

instance U8.Insts.CoreCmpPartialEqU8       : cmp.PartialEq U8    U8    := { eq := fun x y => ok (x == y) }
instance U16.Insts.CoreCmpPartialEqU16     : cmp.PartialEq U16   U16   := { eq := fun x y => ok (x == y) }
instance U32.Insts.CoreCmpPartialEqU32     : cmp.PartialEq U32   U32   := { eq := fun x y => ok (x == y) }
instance U64.Insts.CoreCmpPartialEqU64     : cmp.PartialEq U64   U64   := { eq := fun x y => ok (x == y) }
instance U128.Insts.CoreCmpPartialEqU128   : cmp.PartialEq U128  U128  := { eq := fun x y => ok (x == y) }
instance Usize.Insts.CoreCmpPartialEqUsize : cmp.PartialEq Usize Usize := { eq := fun x y => ok (x == y) }
instance I8.Insts.CoreCmpPartialEqI8       : cmp.PartialEq I8    I8    := { eq := fun x y => ok (x == y) }
instance I16.Insts.CoreCmpPartialEqI16     : cmp.PartialEq I16   I16   := { eq := fun x y => ok (x == y) }
instance I32.Insts.CoreCmpPartialEqI32     : cmp.PartialEq I32   I32   := { eq := fun x y => ok (x == y) }
instance I64.Insts.CoreCmpPartialEqI64     : cmp.PartialEq I64   I64   := { eq := fun x y => ok (x == y) }
instance I128.Insts.CoreCmpPartialEqI128   : cmp.PartialEq I128  I128  := { eq := fun x y => ok (x == y) }
instance Isize.Insts.CoreCmpPartialEqIsize : cmp.PartialEq Isize Isize := { eq := fun x y => ok (x == y) }

def mkUPartialOrd {ty} : cmp.PartialOrd (UScalar ty) (UScalar ty) := {
  PartialEqInst := { eq := fun x y => ok (x == y) }
  partial_cmp := fun x y =>
    ok (option.Option.Some
      (match compare x.val y.val with
       | .lt => cmp.Ordering.Less
       | .eq => cmp.Ordering.Equal
       | .gt => cmp.Ordering.Greater))
}

/-- The `Iterator::next` implementation for `core::ops::range::Range<A>`,
    parameterised over the `Step` dictionary. -/
def IteratorRange.next {A : Type} (StepInst : iter.range.Step A) :
    ops.range.Range A → Aeneas.Std.Result ((Option A) × ops.range.Range A) := fun range => do
  let cmp ← StepInst.corecmpPartialOrdInst.partial_cmp range.start range.«end»
  let isLess : Bool := match cmp with
    | Option.some o => match o with
                       | core.cmp.Ordering.Less => true
                       | _ => false
    | _ => false
  if isLess then
    let cur ← StepInst.cloneCloneInst.clone range.start
    let next? ← StepInst.forward_checked cur 1#usize
    match next? with
    | Option.none      => .fail .panic
    | Option.some next => .ok (Option.some cur, { range with start := next })
  else .ok (Option.none, range)

def mkIPartialOrd {ty} : cmp.PartialOrd (IScalar ty) (IScalar ty) := {
  PartialEqInst := { eq := fun x y => ok (x == y) }
  partial_cmp := fun x y =>
    ok (option.Option.Some
      (match compare x.val y.val with
       | .lt => cmp.Ordering.Less
       | .eq => cmp.Ordering.Equal
       | .gt => cmp.Ordering.Greater))
}

instance U8.Insts.CoreCmpPartialOrdU8       : cmp.PartialOrd U8    U8    := mkUPartialOrd
instance U16.Insts.CoreCmpPartialOrdU16     : cmp.PartialOrd U16   U16   := mkUPartialOrd
instance U32.Insts.CoreCmpPartialOrdU32     : cmp.PartialOrd U32   U32   := mkUPartialOrd
instance U64.Insts.CoreCmpPartialOrdU64     : cmp.PartialOrd U64   U64   := mkUPartialOrd
instance U128.Insts.CoreCmpPartialOrdU128   : cmp.PartialOrd U128  U128  := mkUPartialOrd
instance Usize.Insts.CoreCmpPartialOrdUsize : cmp.PartialOrd Usize Usize := mkUPartialOrd
instance I8.Insts.CoreCmpPartialOrdI8       : cmp.PartialOrd I8    I8    := mkIPartialOrd
instance I16.Insts.CoreCmpPartialOrdI16     : cmp.PartialOrd I16   I16   := mkIPartialOrd
instance I32.Insts.CoreCmpPartialOrdI32     : cmp.PartialOrd I32   I32   := mkIPartialOrd
instance I64.Insts.CoreCmpPartialOrdI64     : cmp.PartialOrd I64   I64   := mkIPartialOrd
instance I128.Insts.CoreCmpPartialOrdI128   : cmp.PartialOrd I128  I128  := mkIPartialOrd
instance Isize.Insts.CoreCmpPartialOrdIsize : cmp.PartialOrd Isize Isize := mkIPartialOrd

abbrev ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next :=
  @IteratorRange.next

/-- [core::cmp::impls::{core::cmp::PartialOrd<&0 (B)> for &1 (A)}::lt]:
    Source: '/rustc/library/core/src/cmp.rs', lines 2133:8-2133:40
    Name pattern: [core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::lt]
    Visibility: public -/
@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::lt"]
def Shared1A.Insts.CoreCmpPartialOrdShared0B.lt
  {A : Type} {B : Type} (PartialOrdInst : cmp.PartialOrd A B) :
  A → B → Result Bool := fun a b => do
  let o ← PartialOrdInst.partial_cmp a b
  match o with
  | some cmp.Ordering.Less => ok true
  | _ => ok false

/-- [core::cmp::impls::{core::cmp::PartialOrd<&0 (B)> for &1 (A)}::gt]:
    Source: '/rustc/library/core/src/cmp.rs', lines 2141:8-2141:40
    Name pattern: [core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::gt]
    Visibility: public -/
@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::gt"]
def Shared1A.Insts.CoreCmpPartialOrdShared0B.gt
  {A : Type} {B : Type} (PartialOrdInst : cmp.PartialOrd A B) :
  A → B → Result Bool := fun a b => do
  let o ← PartialOrdInst.partial_cmp a b
  match o with
  | some cmp.Ordering.Greater => ok true
  | _ => ok false

/-- [core::slice::cmp::{core::cmp::PartialEq<[U]> for [T]}::eq]:
    Source: '/rustc/library/core/src/slice/cmp.rs', lines 18:4-18:37
    Name pattern: [core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::eq]
    Visibility: public -/
@[rust_fun "core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::eq"]
def Slice.Insts.CoreCmpPartialEqSlice.eq
  {T : Type} {U : Type} (cmpPartialEqInst : cmp.PartialEq T U) :
  Slice T → Slice U → Result Bool := fun s1 s2 =>
  if s1.length ≠ s2.length then ok false
  else do
    let rs ← (s1.val.zip s2.val).mapM (fun p => cmpPartialEqInst.eq p.1 p.2)
    ok (rs.all id)

/-! ## Slice -/

def slice.Slice.len {T : Type u} (v : Aeneas.Std.Slice T) : Aeneas.Std.Result Usize :=
  pure (@Aeneas.Std.Slice.len T v)

/-! ## Option -/

def option.Option.unwrap_or :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.unwrap_or T x y)

def option.Option.is_some :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_some T x)

def option.Option.is_none :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_none T x)

def option.Option.take :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.take T x)

/-! ## Mem -/

def mem.swap :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.swap T x y)

def mem.replace :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.replace T x y)

/-! ## Redirects to Aeneas's library -/

export Aeneas.Std.core (
  num.U8.MIN num.U8.MAX num.I8.MIN num.I8.MAX
  num.U16.MIN num.U16.MAX num.I16.MIN num.I16.MAX
  num.U32.MIN num.U32.MAX num.I32.MIN num.I32.MAX
  num.U64.MIN num.U64.MAX num.I64.MIN num.I64.MAX
  num.U128.MIN num.U128.MAX num.I128.MIN num.I128.MAX
  num.Usize.MIN num.Usize.MAX num.Isize.MIN num.Isize.MAX
  convert.num.FromU16U8.from
  convert.num.FromU32U8.from
  convert.num.FromU32U16.from
  convert.num.FromU64U8.from
  convert.num.FromU64U16.from
  convert.num.FromU64U32.from
  convert.num.FromU128U8.from
  convert.num.FromU128U16.from
  convert.num.FromU128U32.from
  convert.num.FromU128U64.from
  convert.num.FromUsizeU8.from
  convert.num.FromUsizeU16.from
  convert.num.FromI16I8.from
  convert.num.FromI32I8.from
  convert.num.FromI32I16.from
  convert.num.FromI64I8.from
  convert.num.FromI64I16.from
  convert.num.FromI64I32.from
  convert.num.FromI128I8.from
  convert.num.FromI128I16.from
  convert.num.FromI128I32.from
  convert.num.FromI128I64.from
  convert.num.FromIsizeI8.from
  convert.num.FromIsizeI16.from
)

end CoreModels.core
