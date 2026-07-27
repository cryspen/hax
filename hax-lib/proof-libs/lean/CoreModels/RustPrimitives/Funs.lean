import Aeneas
import CoreModels.Command
import CoreModels.Core.TypesPrologue
import CoreModels.Core.Types
open Aeneas
open Aeneas.Std hiding namespace core
open Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace CoreModels

/-- [rust_primitives::slice::slice_length]:
    Source: 'rust_primitives/src/lib.rs', lines 4:4-4:44
    Name pattern: [rust_primitives::slice::slice_length]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::slice_length"]
def rust_primitives.slice.slice_length
  {T : Type} : Slice T → Result Std.Usize := fun s => ok (Slice.len s)

/-- [rust_primitives::slice::slice_split_at]:
    Source: 'rust_primitives/src/lib.rs', lines 8:4-8:65
    Name pattern: [rust_primitives::slice::slice_split_at]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::slice_split_at"]
def rust_primitives.slice.slice_split_at
  {T : Type} : Slice T → Std.Usize → Result ((Slice T) × (Slice T)) :=
  Aeneas.Std.core.slice.Slice.split_at

/-- [rust_primitives::slice::slice_contains]:
    Source: 'rust_primitives/src/lib.rs', lines 11:4-11:63
    Name pattern: [rust_primitives::slice::slice_contains]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::slice_contains"]
def rust_primitives.slice.slice_contains
  {T : Type} (CoreCmpPartialEqInst : core.cmp.PartialEq T T) :
  Slice T → T → Result Bool := fun s x => do
  let rs ← s.val.mapM (fun y => CoreCmpPartialEqInst.eq y x)
  ok (rs.any id)

/-- [rust_primitives::slice::slice_index]:
    Source: 'rust_primitives/src/lib.rs', lines 15:4-15:50
    Name pattern: [rust_primitives::slice::slice_index]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::slice_index"]
def rust_primitives.slice.slice_index
  {T : Type} : Slice T → Std.Usize → Result T := Slice.index_usize

/-- [rust_primitives::slice::slice_slice]:
    Source: 'rust_primitives/src/lib.rs', lines 18:4-18:62
    Name pattern: [rust_primitives::slice::slice_slice]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::slice_slice"]
def rust_primitives.slice.slice_slice
  {T : Type} : Slice T → Std.Usize → Std.Usize → Result (Slice T) :=
  fun s i j => Slice.subslice s ⟨i, j⟩

/-- [rust_primitives::slice::slice_clone_from_slice]:
    Source: 'rust_primitives/src/lib.rs', lines 21:4-21:67
    Name pattern: [rust_primitives::slice::slice_clone_from_slice]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::slice_clone_from_slice"]
def rust_primitives.slice.slice_clone_from_slice
  {T : Type} (corecloneCloneInst : core.clone.Clone T) :
  Slice T → Slice T → Result (Slice T) := fun dest src =>
  if dest.length = src.length then ok src
  else fail .panic

private theorem foldlM_list_build_length {T F : Type}
    (step : List T × F → Nat → Result (List T × F))
    (hstep : ∀ l f i r, step (l, f) i = .ok r → r.1.length = l.length + 1) :
    ∀ (l : List Nat) (acc : List T) (f : F) (result : List T × F),
    l.foldlM step (acc, f) = .ok result → result.1.length = acc.length + l.length := by
  intro l
  induction l with
  | nil =>
    intro acc f result h
    simp only [List.foldlM_nil] at h
    have heq : result = (acc, f) := (Result.ok.inj h).symm
    simp [heq]
  | cons x xs ih =>
    intro acc f result h
    simp only [List.foldlM_cons] at h
    cases hstep_x : step (acc, f) x with
    | ok r =>
      obtain ⟨r1, r2⟩ := r
      simp only [hstep_x] at h
      have hlen_r : r1.length = acc.length + 1 := by
        have := hstep acc f x ⟨r1, r2⟩ hstep_x; simpa using this
      have ih' := ih r1 r2 result h
      simp only [List.length_cons]; omega
    | fail e => simp [hstep_x] at h
    | div => simp [hstep_x] at h

/-- [rust_primitives::slice::array_from_fn]:
    Source: 'rust_primitives/src/lib.rs', lines 28:4-28:81
    Name pattern: [rust_primitives::slice::array_from_fn]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::array_from_fn"]
def rust_primitives.slice.array_from_fn
  {T : Type} {F : Type} (N : Std.Usize) (coreopsfunctionFnMutFTupleUsizeTInst :
  core.ops.function.FnMut F Std.Usize T) :
  F → Result (Array T N) := fun f =>
  match h : (List.range N.val).foldlM
    (fun (s : List T × F) (i : Nat) => do
      let (v, f') ← coreopsfunctionFnMutFTupleUsizeTInst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
      ok (s.1 ++ [v], f'))
    ([], f) with
  | fail e => fail e
  | div => div
  | ok result => ok ⟨result.1, by
      have hlen := foldlM_list_build_length
        (fun (s : List T × F) (i : Nat) => do
          let (v, f') ← coreopsfunctionFnMutFTupleUsizeTInst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
          ok (s.1 ++ [v], f'))
        (fun l f i r hr => by
          simp only [] at hr
          cases hcall : coreopsfunctionFnMutFTupleUsizeTInst.call_mut f ⟨BitVec.ofNat _ i⟩ with
          | ok p =>
            obtain ⟨v, fv⟩ := p
            simp only [hcall, bind_tc_ok] at hr
            have heq : r = (l ++ [v], fv) := (Result.ok.inj hr).symm
            simp [heq, List.length_append]
          | fail e =>
            simp only [hcall, bind_tc_fail] at hr
            exact nomatch hr
          | div =>
            simp only [hcall, bind_tc_div] at hr
            exact nomatch hr)
        _ [] f result h
      simp [List.length_range] at hlen; exact hlen⟩

/-- [rust_primitives::slice::array_map]:
    Source: 'rust_primitives/src/lib.rs', lines 31:4-31:84
    Name pattern: [rust_primitives::slice::array_map]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::array_map"]
def rust_primitives.slice.array_map
  {T : Type} {U : Type} {F : Type} {N : Std.Usize}
  (coreopsfunctionFnFTupleTUInst : core.ops.function.Fn F T U) :
  Array T N → F → Result (Array U N) := fun a f =>
  match h : a.val.mapM (fun x => coreopsfunctionFnFTupleTUInst.call f x) with
  | ok mapped => ok ⟨mapped, by
      have := List.mapM_Result_length h; have := a.property; omega⟩
  | fail e => fail e
  | div => div

/-- [rust_primitives::slice::array_as_slice]:
    Source: 'rust_primitives/src/lib.rs', lines 34:4-34:64
    Name pattern: [rust_primitives::slice::array_as_slice]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::array_as_slice"]
def rust_primitives.slice.array_as_slice
  {T : Type} {N : Std.Usize} : Array T N → Result (Slice T) :=
  fun a => ok (Array.to_slice a)

/-- [rust_primitives::slice::array_slice]:
    Source: 'rust_primitives/src/lib.rs', lines 37:4-37:81
    Name pattern: [rust_primitives::slice::array_slice]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::array_slice"]
def rust_primitives.slice.array_slice
  {T : Type} {N : Std.Usize} :
  Array T N → Std.Usize → Std.Usize → Result (Slice T) :=
  fun a i j => Array.subslice a ⟨i, j⟩

/-- [rust_primitives::slice::array_index]:
    Source: 'rust_primitives/src/lib.rs', lines 40:4-40:69
    Name pattern: [rust_primitives::slice::array_index]
    Visibility: public -/
@[rust_fun "rust_primitives::slice::array_index"]
def rust_primitives.slice.array_index
  {T : Type} {N : Std.Usize} : Array T N → Std.Usize → Result T :=
  fun a i => Slice.index_usize (Array.to_slice a) i

/-- [rust_primitives::sequence::seq_from_slice]:
    Source: 'rust_primitives/src/lib.rs', lines 51:4-51:48
    Name pattern: [rust_primitives::sequence::seq_from_slice]
    Visibility: public -/
@[rust_fun "rust_primitives::sequence::seq_from_slice"]
def rust_primitives.sequence.seq_from_slice
  {T : Type} : Slice T → Result (rust_primitives.sequence.Seq T) := fun s => ok s

/-- [rust_primitives::sequence::seq_from_array]:
    Source: 'rust_primitives/src/lib.rs', lines 57:4-57:65
    Name pattern: [rust_primitives::sequence::seq_from_array]
    Visibility: public -/
@[rust_fun "rust_primitives::sequence::seq_from_array"]
def rust_primitives.sequence.seq_from_array
  {T : Type} {N : Std.Usize} :
  Array T N → Result (rust_primitives.sequence.Seq T) := fun a => ok (Array.to_slice a)

/-- [rust_primitives::sequence::seq_len]:
    Source: 'rust_primitives/src/lib.rs', lines 81:4-81:42
    Name pattern: [rust_primitives::sequence::seq_len]
    Visibility: public -/
@[rust_fun "rust_primitives::sequence::seq_len"]
def rust_primitives.sequence.seq_len
  {T : Type} : rust_primitives.sequence.Seq T → Result Std.Usize :=
  fun s => ok (Slice.len s)

/-- [rust_primitives::sequence::seq_remove]:
    Source: 'rust_primitives/src/lib.rs', lines 87:4-87:55
    Name pattern: [rust_primitives::sequence::seq_remove]
    Visibility: public -/
@[rust_fun "rust_primitives::sequence::seq_remove"]
def rust_primitives.sequence.seq_remove
  {T : Type} :
  rust_primitives.sequence.Seq T → Std.Usize → Result (T ×
    (rust_primitives.sequence.Seq T)) := fun s i =>
  if h : i.val < s.val.length then
    ok (s.val.get ⟨i.val, h⟩, ⟨s.val.take i.val ++ s.val.drop (i.val + 1), by
      simp only [List.length_append, List.length_take, List.length_drop]
      have := s.property; omega⟩)
  else fail .arrayOutOfBounds

def usaturating_mul {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨BitVec.ofNat _ (Min.min (UScalar.max ty) (x.val * y.val))⟩

def isaturating_mul {ty : IScalarTy} (x y : IScalar ty) : IScalar ty :=
  ⟨BitVec.ofInt _ (Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val * y.val)))⟩

def urem_euclid {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if y.val = 0 then fail .divisionByZero
  else ok ⟨BitVec.ofNat _ (x.val % y.val)⟩

def irem_euclid {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  if y.val = 0 then fail .divisionByZero
  else ok ⟨BitVec.ofInt _ (x.val % y.val)⟩

@[rust_fun "rust_primitives::arithmetic::saturating_mul_u8"]
def rust_primitives.arithmetic.saturating_mul_u8 : Std.U8 → Std.U8 → Result Std.U8 :=
  fun x y => ok (usaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_u8"]
def rust_primitives.arithmetic.rem_euclid_u8 : Std.U8 → Std.U8 → Result Std.U8 := urem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_u16"]
def rust_primitives.arithmetic.saturating_mul_u16 : Std.U16 → Std.U16 → Result Std.U16 :=
  fun x y => ok (usaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_u16"]
def rust_primitives.arithmetic.rem_euclid_u16 : Std.U16 → Std.U16 → Result Std.U16 := urem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_u32"]
def rust_primitives.arithmetic.saturating_mul_u32 : Std.U32 → Std.U32 → Result Std.U32 :=
  fun x y => ok (usaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_u32"]
def rust_primitives.arithmetic.rem_euclid_u32 : Std.U32 → Std.U32 → Result Std.U32 := urem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_u64"]
def rust_primitives.arithmetic.saturating_mul_u64 : Std.U64 → Std.U64 → Result Std.U64 :=
  fun x y => ok (usaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_u64"]
def rust_primitives.arithmetic.rem_euclid_u64 : Std.U64 → Std.U64 → Result Std.U64 := urem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_u128"]
def rust_primitives.arithmetic.saturating_mul_u128 : Std.U128 → Std.U128 → Result Std.U128 :=
  fun x y => ok (usaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_u128"]
def rust_primitives.arithmetic.rem_euclid_u128 : Std.U128 → Std.U128 → Result Std.U128 := urem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_usize"]
def rust_primitives.arithmetic.saturating_mul_usize : Std.Usize → Std.Usize → Result Std.Usize :=
  fun x y => ok (usaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_usize"]
def rust_primitives.arithmetic.rem_euclid_usize : Std.Usize → Std.Usize → Result Std.Usize := urem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_i8"]
def rust_primitives.arithmetic.saturating_mul_i8 : Std.I8 → Std.I8 → Result Std.I8 :=
  fun x y => ok (isaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_i8"]
def rust_primitives.arithmetic.rem_euclid_i8 : Std.I8 → Std.I8 → Result Std.I8 := irem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_i16"]
def rust_primitives.arithmetic.saturating_mul_i16 : Std.I16 → Std.I16 → Result Std.I16 :=
  fun x y => ok (isaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_i16"]
def rust_primitives.arithmetic.rem_euclid_i16 : Std.I16 → Std.I16 → Result Std.I16 := irem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_i32"]
def rust_primitives.arithmetic.saturating_mul_i32 : Std.I32 → Std.I32 → Result Std.I32 :=
  fun x y => ok (isaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_i32"]
def rust_primitives.arithmetic.rem_euclid_i32 : Std.I32 → Std.I32 → Result Std.I32 := irem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_i64"]
def rust_primitives.arithmetic.saturating_mul_i64 : Std.I64 → Std.I64 → Result Std.I64 :=
  fun x y => ok (isaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_i64"]
def rust_primitives.arithmetic.rem_euclid_i64 : Std.I64 → Std.I64 → Result Std.I64 := irem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_i128"]
def rust_primitives.arithmetic.saturating_mul_i128 : Std.I128 → Std.I128 → Result Std.I128 :=
  fun x y => ok (isaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_i128"]
def rust_primitives.arithmetic.rem_euclid_i128 : Std.I128 → Std.I128 → Result Std.I128 := irem_euclid

@[rust_fun "rust_primitives::arithmetic::saturating_mul_isize"]
def rust_primitives.arithmetic.saturating_mul_isize : Std.Isize → Std.Isize → Result Std.Isize :=
  fun x y => ok (isaturating_mul x y)

@[rust_fun "rust_primitives::arithmetic::rem_euclid_isize"]
def rust_primitives.arithmetic.rem_euclid_isize : Std.Isize → Std.Isize → Result Std.Isize := irem_euclid

def uoverflowing_sub {ty : UScalarTy} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨x.bv - y.bv⟩, decide (x.val < y.val))

def uoverflowing_mul {ty : UScalarTy} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨BitVec.ofNat _ (x.val * y.val)⟩, decide (2 ^ ty.numBits ≤ x.val * y.val))

def ioverflowing_sub {ty : IScalarTy} (x y : IScalar ty) : IScalar ty × Bool :=
  let z := x.val - y.val
  (⟨BitVec.ofInt _ z⟩,
   decide (¬ (-2 ^ (ty.numBits - 1) ≤ z ∧ z < 2 ^ (ty.numBits - 1))))

def ioverflowing_mul {ty : IScalarTy} (x y : IScalar ty) : IScalar ty × Bool :=
  let z := x.val * y.val
  (⟨BitVec.ofInt _ z⟩,
   decide (¬ (-2 ^ (ty.numBits - 1) ≤ z ∧ z < 2 ^ (ty.numBits - 1))))

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_u8"]
def rust_primitives.arithmetic.overflowing_sub_u8 : Std.U8 → Std.U8 → Result (Std.U8 × Bool) :=
  fun x y => ok (uoverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_u8"]
def rust_primitives.arithmetic.overflowing_mul_u8 : Std.U8 → Std.U8 → Result (Std.U8 × Bool) :=
  fun x y => ok (uoverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_u16"]
def rust_primitives.arithmetic.overflowing_sub_u16 : Std.U16 → Std.U16 → Result (Std.U16 × Bool) :=
  fun x y => ok (uoverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_u16"]
def rust_primitives.arithmetic.overflowing_mul_u16 : Std.U16 → Std.U16 → Result (Std.U16 × Bool) :=
  fun x y => ok (uoverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_u32"]
def rust_primitives.arithmetic.overflowing_sub_u32 : Std.U32 → Std.U32 → Result (Std.U32 × Bool) :=
  fun x y => ok (uoverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_u32"]
def rust_primitives.arithmetic.overflowing_mul_u32 : Std.U32 → Std.U32 → Result (Std.U32 × Bool) :=
  fun x y => ok (uoverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_u64"]
def rust_primitives.arithmetic.overflowing_sub_u64 : Std.U64 → Std.U64 → Result (Std.U64 × Bool) :=
  fun x y => ok (uoverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_u64"]
def rust_primitives.arithmetic.overflowing_mul_u64 : Std.U64 → Std.U64 → Result (Std.U64 × Bool) :=
  fun x y => ok (uoverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_u128"]
def rust_primitives.arithmetic.overflowing_sub_u128 : Std.U128 → Std.U128 → Result (Std.U128 × Bool) :=
  fun x y => ok (uoverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_u128"]
def rust_primitives.arithmetic.overflowing_mul_u128 : Std.U128 → Std.U128 → Result (Std.U128 × Bool) :=
  fun x y => ok (uoverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_usize"]
def rust_primitives.arithmetic.overflowing_sub_usize : Std.Usize → Std.Usize → Result (Std.Usize × Bool) :=
  fun x y => ok (uoverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_usize"]
def rust_primitives.arithmetic.overflowing_mul_usize : Std.Usize → Std.Usize → Result (Std.Usize × Bool) :=
  fun x y => ok (uoverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_i8"]
def rust_primitives.arithmetic.overflowing_sub_i8 : Std.I8 → Std.I8 → Result (Std.I8 × Bool) :=
  fun x y => ok (ioverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_i8"]
def rust_primitives.arithmetic.overflowing_mul_i8 : Std.I8 → Std.I8 → Result (Std.I8 × Bool) :=
  fun x y => ok (ioverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_i16"]
def rust_primitives.arithmetic.overflowing_sub_i16 : Std.I16 → Std.I16 → Result (Std.I16 × Bool) :=
  fun x y => ok (ioverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_i16"]
def rust_primitives.arithmetic.overflowing_mul_i16 : Std.I16 → Std.I16 → Result (Std.I16 × Bool) :=
  fun x y => ok (ioverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_i32"]
def rust_primitives.arithmetic.overflowing_sub_i32 : Std.I32 → Std.I32 → Result (Std.I32 × Bool) :=
  fun x y => ok (ioverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_i32"]
def rust_primitives.arithmetic.overflowing_mul_i32 : Std.I32 → Std.I32 → Result (Std.I32 × Bool) :=
  fun x y => ok (ioverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_i64"]
def rust_primitives.arithmetic.overflowing_sub_i64 : Std.I64 → Std.I64 → Result (Std.I64 × Bool) :=
  fun x y => ok (ioverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_i64"]
def rust_primitives.arithmetic.overflowing_mul_i64 : Std.I64 → Std.I64 → Result (Std.I64 × Bool) :=
  fun x y => ok (ioverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_i128"]
def rust_primitives.arithmetic.overflowing_sub_i128 : Std.I128 → Std.I128 → Result (Std.I128 × Bool) :=
  fun x y => ok (ioverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_i128"]
def rust_primitives.arithmetic.overflowing_mul_i128 : Std.I128 → Std.I128 → Result (Std.I128 × Bool) :=
  fun x y => ok (ioverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_sub_isize"]
def rust_primitives.arithmetic.overflowing_sub_isize : Std.Isize → Std.Isize → Result (Std.Isize × Bool) :=
  fun x y => ok (ioverflowing_sub x y)

@[rust_fun "rust_primitives::arithmetic::overflowing_mul_isize"]
def rust_primitives.arithmetic.overflowing_mul_isize : Std.Isize → Std.Isize → Result (Std.Isize × Bool) :=
  fun x y => ok (ioverflowing_mul x y)

@[rust_fun "rust_primitives::arithmetic::pow_u8"]
def rust_primitives.arithmetic.pow_u8 : Std.U8 → Std.U32 → Result Std.U8 :=
  fun x n => UScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_u16"]
def rust_primitives.arithmetic.pow_u16 : Std.U16 → Std.U32 → Result Std.U16 :=
  fun x n => UScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_u32"]
def rust_primitives.arithmetic.pow_u32 : Std.U32 → Std.U32 → Result Std.U32 :=
  fun x n => UScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_u64"]
def rust_primitives.arithmetic.pow_u64 : Std.U64 → Std.U32 → Result Std.U64 :=
  fun x n => UScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_u128"]
def rust_primitives.arithmetic.pow_u128 : Std.U128 → Std.U32 → Result Std.U128 :=
  fun x n => UScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_usize"]
def rust_primitives.arithmetic.pow_usize : Std.Usize → Std.U32 → Result Std.Usize :=
  fun x n => UScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_i8"]
def rust_primitives.arithmetic.pow_i8 : Std.I8 → Std.U32 → Result Std.I8 :=
  fun x n => IScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_i16"]
def rust_primitives.arithmetic.pow_i16 : Std.I16 → Std.U32 → Result Std.I16 :=
  fun x n => IScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_i32"]
def rust_primitives.arithmetic.pow_i32 : Std.I32 → Std.U32 → Result Std.I32 :=
  fun x n => IScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_i64"]
def rust_primitives.arithmetic.pow_i64 : Std.I64 → Std.U32 → Result Std.I64 :=
  fun x n => IScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_i128"]
def rust_primitives.arithmetic.pow_i128 : Std.I128 → Std.U32 → Result Std.I128 :=
  fun x n => IScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::pow_isize"]
def rust_primitives.arithmetic.pow_isize : Std.Isize → Std.U32 → Result Std.Isize :=
  fun x n => IScalar.tryMk _ (x.val ^ n.val)

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_u8"]
def rust_primitives.arithmetic.from_be_bytes_u8 : Array Std.U8 1#usize → Result Std.U8 :=
  fun a => ok (Aeneas.Std.core.num.U8.from_be_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_u8"]
def rust_primitives.arithmetic.from_le_bytes_u8 : Array Std.U8 1#usize → Result Std.U8 :=
  fun a => ok (Aeneas.Std.core.num.U8.from_le_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_u16"]
def rust_primitives.arithmetic.from_be_bytes_u16 : Array Std.U8 2#usize → Result Std.U16 :=
  fun a => ok (Aeneas.Std.core.num.U16.from_be_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_u16"]
def rust_primitives.arithmetic.from_le_bytes_u16 : Array Std.U8 2#usize → Result Std.U16 :=
  fun a => ok (Aeneas.Std.core.num.U16.from_le_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_u32"]
def rust_primitives.arithmetic.from_be_bytes_u32 : Array Std.U8 4#usize → Result Std.U32 :=
  fun a => ok (Aeneas.Std.core.num.U32.from_be_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_u32"]
def rust_primitives.arithmetic.from_le_bytes_u32 : Array Std.U8 4#usize → Result Std.U32 :=
  fun a => ok (Aeneas.Std.core.num.U32.from_le_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_u64"]
def rust_primitives.arithmetic.from_be_bytes_u64 : Array Std.U8 8#usize → Result Std.U64 :=
  fun a => ok (Aeneas.Std.core.num.U64.from_be_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_u64"]
def rust_primitives.arithmetic.from_le_bytes_u64 : Array Std.U8 8#usize → Result Std.U64 :=
  fun a => ok (Aeneas.Std.core.num.U64.from_le_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_u128"]
def rust_primitives.arithmetic.from_be_bytes_u128 : Array Std.U8 16#usize → Result Std.U128 :=
  fun a => ok (Aeneas.Std.core.num.U128.from_be_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_u128"]
def rust_primitives.arithmetic.from_le_bytes_u128 : Array Std.U8 16#usize → Result Std.U128 :=
  fun a => ok (Aeneas.Std.core.num.U128.from_le_bytes a)

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_usize"]
def rust_primitives.arithmetic.from_be_bytes_usize : Array Std.U8 8#usize → Result Std.Usize :=
  fun a => ok ⟨(BitVec.fromBEBytes (a.val.map U8.bv)).setWidth _⟩

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_usize"]
def rust_primitives.arithmetic.from_le_bytes_usize : Array Std.U8 8#usize → Result Std.Usize :=
  fun a => ok ⟨(BitVec.fromLEBytes (a.val.map U8.bv)).setWidth _⟩

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_i8"]
def rust_primitives.arithmetic.from_be_bytes_i8 : Array Std.U8 1#usize → Result Std.I8 :=
  fun a => ok ⟨ (BitVec.fromBEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_i8"]
def rust_primitives.arithmetic.from_le_bytes_i8 : Array Std.U8 1#usize → Result Std.I8 :=
  fun a => ok ⟨ (BitVec.fromLEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_i16"]
def rust_primitives.arithmetic.from_be_bytes_i16 : Array Std.U8 2#usize → Result Std.I16 :=
  fun a => ok ⟨ (BitVec.fromBEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_i16"]
def rust_primitives.arithmetic.from_le_bytes_i16 : Array Std.U8 2#usize → Result Std.I16 :=
  fun a => ok ⟨ (BitVec.fromLEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_i32"]
def rust_primitives.arithmetic.from_be_bytes_i32 : Array Std.U8 4#usize → Result Std.I32 :=
  fun a => ok ⟨ (BitVec.fromBEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_i32"]
def rust_primitives.arithmetic.from_le_bytes_i32 : Array Std.U8 4#usize → Result Std.I32 :=
  fun a => ok ⟨ (BitVec.fromLEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_i64"]
def rust_primitives.arithmetic.from_be_bytes_i64 : Array Std.U8 8#usize → Result Std.I64 :=
  fun a => ok ⟨ (BitVec.fromBEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_i64"]
def rust_primitives.arithmetic.from_le_bytes_i64 : Array Std.U8 8#usize → Result Std.I64 :=
  fun a => ok ⟨ (BitVec.fromLEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_i128"]
def rust_primitives.arithmetic.from_be_bytes_i128 : Array Std.U8 16#usize → Result Std.I128 :=
  fun a => ok ⟨ (BitVec.fromBEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_i128"]
def rust_primitives.arithmetic.from_le_bytes_i128 : Array Std.U8 16#usize → Result Std.I128 :=
  fun a => ok ⟨ (BitVec.fromLEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

@[rust_fun "rust_primitives::arithmetic::from_be_bytes_isize"]
def rust_primitives.arithmetic.from_be_bytes_isize : Array Std.U8 8#usize → Result Std.Isize :=
  fun a => ok ⟨(BitVec.fromBEBytes (a.val.map U8.bv)).setWidth _⟩

@[rust_fun "rust_primitives::arithmetic::from_le_bytes_isize"]
def rust_primitives.arithmetic.from_le_bytes_isize : Array Std.U8 8#usize → Result Std.Isize :=
  fun a => ok ⟨(BitVec.fromLEBytes (a.val.map U8.bv)).setWidth _⟩

def ucount_ones {ty : UScalarTy} (x : UScalar ty) : Std.U32 :=
  ⟨x.bv.cpop.setWidth 32⟩

def icount_ones {ty : IScalarTy} (x : IScalar ty) : Std.U32 :=
  ⟨x.bv.cpop.setWidth 32⟩

@[rust_fun "rust_primitives::arithmetic::count_ones_u8"]
def rust_primitives.arithmetic.count_ones_u8 : Std.U8 → Result Std.U32 :=
  fun x => ok (ucount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_u16"]
def rust_primitives.arithmetic.count_ones_u16 : Std.U16 → Result Std.U32 :=
  fun x => ok (ucount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_u32"]
def rust_primitives.arithmetic.count_ones_u32 : Std.U32 → Result Std.U32 :=
  fun x => ok (ucount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_u64"]
def rust_primitives.arithmetic.count_ones_u64 : Std.U64 → Result Std.U32 :=
  fun x => ok (ucount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_u128"]
def rust_primitives.arithmetic.count_ones_u128 : Std.U128 → Result Std.U32 :=
  fun x => ok (ucount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_usize"]
def rust_primitives.arithmetic.count_ones_usize : Std.Usize → Result Std.U32 :=
  fun x => ok (ucount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_i8"]
def rust_primitives.arithmetic.count_ones_i8 : Std.I8 → Result Std.U32 :=
  fun x => ok (icount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_i16"]
def rust_primitives.arithmetic.count_ones_i16 : Std.I16 → Result Std.U32 :=
  fun x => ok (icount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_i32"]
def rust_primitives.arithmetic.count_ones_i32 : Std.I32 → Result Std.U32 :=
  fun x => ok (icount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_i64"]
def rust_primitives.arithmetic.count_ones_i64 : Std.I64 → Result Std.U32 :=
  fun x => ok (icount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_i128"]
def rust_primitives.arithmetic.count_ones_i128 : Std.I128 → Result Std.U32 :=
  fun x => ok (icount_ones x)

@[rust_fun "rust_primitives::arithmetic::count_ones_isize"]
def rust_primitives.arithmetic.count_ones_isize : Std.Isize → Result Std.U32 :=
  fun x => ok (icount_ones x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_u8"]
def rust_primitives.arithmetic.leading_zeros_u8 : Std.U8 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.U8.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_u16"]
def rust_primitives.arithmetic.leading_zeros_u16 : Std.U16 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.U16.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_u32"]
def rust_primitives.arithmetic.leading_zeros_u32 : Std.U32 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.U32.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_u64"]
def rust_primitives.arithmetic.leading_zeros_u64 : Std.U64 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.U64.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_u128"]
def rust_primitives.arithmetic.leading_zeros_u128 : Std.U128 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.U128.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_usize"]
def rust_primitives.arithmetic.leading_zeros_usize : Std.Usize → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.Usize.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_i8"]
def rust_primitives.arithmetic.leading_zeros_i8 : Std.I8 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.I8.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_i16"]
def rust_primitives.arithmetic.leading_zeros_i16 : Std.I16 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.I16.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_i32"]
def rust_primitives.arithmetic.leading_zeros_i32 : Std.I32 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.I32.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_i64"]
def rust_primitives.arithmetic.leading_zeros_i64 : Std.I64 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.I64.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_i128"]
def rust_primitives.arithmetic.leading_zeros_i128 : Std.I128 → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.I128.leading_zeros x)

@[rust_fun "rust_primitives::arithmetic::leading_zeros_isize"]
def rust_primitives.arithmetic.leading_zeros_isize : Std.Isize → Result Std.U32 :=
  fun x => ok (Aeneas.Std.core.num.Isize.leading_zeros x)

def uilog2 {ty : UScalarTy} (x : UScalar ty) : Result Std.U32 :=
  if x.val = 0 then fail .panic
  else ok ⟨BitVec.ofNat 32 (Nat.log2 x.val)⟩

def iilog2 {ty : IScalarTy} (x : IScalar ty) : Result Std.U32 :=
  if x.val ≤ 0 then fail .panic
  else ok ⟨BitVec.ofNat 32 (Nat.log2 x.val.toNat)⟩

@[rust_fun "rust_primitives::arithmetic::ilog2_u8"]
def rust_primitives.arithmetic.ilog2_u8 : Std.U8 → Result Std.U32 := uilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_u16"]
def rust_primitives.arithmetic.ilog2_u16 : Std.U16 → Result Std.U32 := uilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_u32"]
def rust_primitives.arithmetic.ilog2_u32 : Std.U32 → Result Std.U32 := uilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_u64"]
def rust_primitives.arithmetic.ilog2_u64 : Std.U64 → Result Std.U32 := uilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_u128"]
def rust_primitives.arithmetic.ilog2_u128 : Std.U128 → Result Std.U32 := uilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_usize"]
def rust_primitives.arithmetic.ilog2_usize : Std.Usize → Result Std.U32 := uilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_i8"]
def rust_primitives.arithmetic.ilog2_i8 : Std.I8 → Result Std.U32 := iilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_i16"]
def rust_primitives.arithmetic.ilog2_i16 : Std.I16 → Result Std.U32 := iilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_i32"]
def rust_primitives.arithmetic.ilog2_i32 : Std.I32 → Result Std.U32 := iilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_i64"]
def rust_primitives.arithmetic.ilog2_i64 : Std.I64 → Result Std.U32 := iilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_i128"]
def rust_primitives.arithmetic.ilog2_i128 : Std.I128 → Result Std.U32 := iilog2

@[rust_fun "rust_primitives::arithmetic::ilog2_isize"]
def rust_primitives.arithmetic.ilog2_isize : Std.Isize → Result Std.U32 := iilog2

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_u8"]
def rust_primitives.arithmetic.to_be_bytes_u8 : Std.U8 → Result (Array Std.U8 1#usize) :=
  fun x => ok (Std.core.num.U8.to_be_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_u16"]
def rust_primitives.arithmetic.to_be_bytes_u16 : Std.U16 → Result (Array Std.U8 2#usize) :=
  fun x => ok (Std.core.num.U16.to_be_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_u32"]
def rust_primitives.arithmetic.to_be_bytes_u32 : Std.U32 → Result (Array Std.U8 4#usize) :=
  fun x => ok (Std.core.num.U32.to_be_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_u64"]
def rust_primitives.arithmetic.to_be_bytes_u64 : Std.U64 → Result (Array Std.U8 8#usize) :=
  fun x => ok (Std.core.num.U64.to_be_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_u128"]
def rust_primitives.arithmetic.to_be_bytes_u128 : Std.U128 → Result (Array Std.U8 16#usize) :=
  fun x => ok (Std.core.num.U128.to_be_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_usize"]
def rust_primitives.arithmetic.to_be_bytes_usize : Std.Usize → Result (Array Std.U8 8#usize) :=
  fun x => ok ⟨ (x.bv.setWidth 64).toBEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_i8"]
def rust_primitives.arithmetic.to_be_bytes_i8 : Std.I8 → Result (Array Std.U8 1#usize) :=
  fun x => ok ⟨ x.bv.toBEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_i16"]
def rust_primitives.arithmetic.to_be_bytes_i16 : Std.I16 → Result (Array Std.U8 2#usize) :=
  fun x => ok ⟨ x.bv.toBEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_i32"]
def rust_primitives.arithmetic.to_be_bytes_i32 : Std.I32 → Result (Array Std.U8 4#usize) :=
  fun x => ok ⟨ x.bv.toBEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_i64"]
def rust_primitives.arithmetic.to_be_bytes_i64 : Std.I64 → Result (Array Std.U8 8#usize) :=
  fun x => ok ⟨ x.bv.toBEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_i128"]
def rust_primitives.arithmetic.to_be_bytes_i128 : Std.I128 → Result (Array Std.U8 16#usize) :=
  fun x => ok ⟨ x.bv.toBEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_be_bytes_isize"]
def rust_primitives.arithmetic.to_be_bytes_isize : Std.Isize → Result (Array Std.U8 8#usize) :=
  fun x => ok ⟨ (x.bv.setWidth 64).toBEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_u8"]
def rust_primitives.arithmetic.to_le_bytes_u8 : Std.U8 → Result (Array Std.U8 1#usize) :=
  fun x => ok (Std.core.num.U8.to_le_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_u16"]
def rust_primitives.arithmetic.to_le_bytes_u16 : Std.U16 → Result (Array Std.U8 2#usize) :=
  fun x => ok (Std.core.num.U16.to_le_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_u32"]
def rust_primitives.arithmetic.to_le_bytes_u32 : Std.U32 → Result (Array Std.U8 4#usize) :=
  fun x => ok (Std.core.num.U32.to_le_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_u64"]
def rust_primitives.arithmetic.to_le_bytes_u64 : Std.U64 → Result (Array Std.U8 8#usize) :=
  fun x => ok (Std.core.num.U64.to_le_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_u128"]
def rust_primitives.arithmetic.to_le_bytes_u128 : Std.U128 → Result (Array Std.U8 16#usize) :=
  fun x => ok (Std.core.num.U128.to_le_bytes x)

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_usize"]
def rust_primitives.arithmetic.to_le_bytes_usize : Std.Usize → Result (Array Std.U8 8#usize) :=
  fun x => ok ⟨ (x.bv.setWidth 64).toLEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_i8"]
def rust_primitives.arithmetic.to_le_bytes_i8 : Std.I8 → Result (Array Std.U8 1#usize) :=
  fun x => ok ⟨ x.bv.toLEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_i16"]
def rust_primitives.arithmetic.to_le_bytes_i16 : Std.I16 → Result (Array Std.U8 2#usize) :=
  fun x => ok ⟨ x.bv.toLEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_i32"]
def rust_primitives.arithmetic.to_le_bytes_i32 : Std.I32 → Result (Array Std.U8 4#usize) :=
  fun x => ok ⟨ x.bv.toLEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_i64"]
def rust_primitives.arithmetic.to_le_bytes_i64 : Std.I64 → Result (Array Std.U8 8#usize) :=
  fun x => ok ⟨ x.bv.toLEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_i128"]
def rust_primitives.arithmetic.to_le_bytes_i128 : Std.I128 → Result (Array Std.U8 16#usize) :=
  fun x => ok ⟨ x.bv.toLEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::to_le_bytes_isize"]
def rust_primitives.arithmetic.to_le_bytes_isize : Std.Isize → Result (Array Std.U8 8#usize) :=
  fun x => ok ⟨ (x.bv.setWidth 64).toLEBytes.map UScalar.mk, by grind [BitVec.toBEBytes_length] ⟩

@[rust_fun "rust_primitives::arithmetic::abs_i8"]
def rust_primitives.arithmetic.abs_i8 : Std.I8 → Result Std.I8 :=
  fun x => ok ⟨BitVec.ofNat _ x.val.natAbs⟩

@[rust_fun "rust_primitives::arithmetic::abs_i16"]
def rust_primitives.arithmetic.abs_i16 : Std.I16 → Result Std.I16 :=
  fun x => ok ⟨BitVec.ofNat _ x.val.natAbs⟩

@[rust_fun "rust_primitives::arithmetic::abs_i32"]
def rust_primitives.arithmetic.abs_i32 : Std.I32 → Result Std.I32 :=
  fun x => ok ⟨BitVec.ofNat _ x.val.natAbs⟩

@[rust_fun "rust_primitives::arithmetic::abs_i64"]
def rust_primitives.arithmetic.abs_i64 : Std.I64 → Result Std.I64 :=
  fun x => ok ⟨BitVec.ofNat _ x.val.natAbs⟩

@[rust_fun "rust_primitives::arithmetic::abs_i128"]
def rust_primitives.arithmetic.abs_i128 : Std.I128 → Result Std.I128 :=
  fun x => ok ⟨BitVec.ofNat _ x.val.natAbs⟩

@[rust_fun "rust_primitives::arithmetic::abs_isize"]
def rust_primitives.arithmetic.abs_isize : Std.Isize → Result Std.Isize :=
  fun x => ok ⟨BitVec.ofNat _ x.val.natAbs⟩

@[rust_const "rust_primitives::arithmetic::SIZE_BITS"]
def rust_primitives.arithmetic.SIZE_BITS : Result Std.U32 :=
  ok Std.core.num.Usize.BITS

@[rust_const "rust_primitives::arithmetic::USIZE_MAX"]
def rust_primitives.arithmetic.USIZE_MAX : Result Std.Usize :=
  ok Std.core.num.Usize.MAX

@[rust_const "rust_primitives::arithmetic::ISIZE_MAX"]
def rust_primitives.arithmetic.ISIZE_MAX : Result Std.Isize :=
  ok Std.core.num.Isize.MAX

@[rust_const "rust_primitives::arithmetic::ISIZE_MIN"]
def rust_primitives.arithmetic.ISIZE_MIN : Result Std.Isize :=
  ok Std.core.num.Isize.MIN

@[rust_fun "alloc::string::{alloc::string::String}::new"]
def alloc.string.String.new : Result String := ok ""

@[rust_fun "rust_primitives::sequence::seq_empty"]
def rust_primitives.sequence.seq_empty
  (T : Type) : Result (rust_primitives.sequence.Seq T) := ok (Slice.new T)

@[rust_fun "rust_primitives::sequence::seq_from_boxed_slice"]
def rust_primitives.sequence.seq_from_boxed_slice
  {T : Type} : Slice T → Result (rust_primitives.sequence.Seq T) := fun s => ok s

@[rust_fun "rust_primitives::sequence::seq_to_slice"]
def rust_primitives.sequence.seq_to_slice
  {T : Type} : rust_primitives.sequence.Seq T → Result (Slice T) := fun s => ok s

@[rust_fun "rust_primitives::sequence::seq_concat"]
def rust_primitives.sequence.seq_concat
  {T : Type} :
  rust_primitives.sequence.Seq T → rust_primitives.sequence.Seq T → Result
    ((rust_primitives.sequence.Seq T) × (rust_primitives.sequence.Seq T)) :=
  fun s1 s2 =>
    let combined := s1.val ++ s2.val
    if h : combined.length ≤ Usize.max then ok (⟨combined, h⟩, Slice.new T)
    else fail .maximumSizeExceeded

@[rust_fun "rust_primitives::sequence::seq_extend"]
def rust_primitives.sequence.seq_extend
  {T : Type} (corecloneCloneInst : core.clone.Clone T) :
  rust_primitives.sequence.Seq T → Slice T → Result
    (rust_primitives.sequence.Seq T) := fun s src =>
  let combined := s.val ++ src.val
  if h : combined.length ≤ Usize.max then ok ⟨combined, h⟩
  else fail .maximumSizeExceeded

@[rust_fun "rust_primitives::sequence::seq_push"]
def rust_primitives.sequence.seq_push
  {T : Type} :
  rust_primitives.sequence.Seq T → T → Result (rust_primitives.sequence.Seq T) :=
  fun s x =>
    let extended := s.val ++ [x]
    if h : extended.length ≤ Usize.max then ok ⟨extended, h⟩
    else fail .maximumSizeExceeded

@[rust_fun "rust_primitives::sequence::seq_create"]
def rust_primitives.sequence.seq_create
  {T : Type} (corecloneCloneInst : core.clone.Clone T) :
  T → Std.Usize → Result (rust_primitives.sequence.Seq T) := fun x n =>
  ok ⟨List.replicate n.val x, by grind⟩

@[rust_fun "rust_primitives::sequence::seq_drain"]
def rust_primitives.sequence.seq_drain
  {T : Type} :
  rust_primitives.sequence.Seq T → Std.Usize → Std.Usize → Result
    ((rust_primitives.sequence.Seq T) × (rust_primitives.sequence.Seq T)) :=
  fun s start «end» =>
    if h : start.val ≤ «end».val ∧ «end».val ≤ s.length then
      let drained := (s.val.drop start.val).take («end».val - start.val)
      let remaining := s.val.take start.val ++ s.val.drop «end».val
      ok (⟨drained, by grind⟩, ⟨remaining, by grind⟩)
    else fail .arrayOutOfBounds

@[rust_fun "rust_primitives::sequence::seq_index"]
def rust_primitives.sequence.seq_index
  {T : Type} : rust_primitives.sequence.Seq T → Std.Usize → Result T :=
  Slice.index_usize

def rust_primitives.arithmetic.wrapping_add_i8 (x y : I8) : Result I8 :=
  .ok (Aeneas.Std.I8.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_i16 (x y : I16) : Result I16 :=
  .ok (Aeneas.Std.I16.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_i32 (x y : I32) : Result I32 :=
  .ok (Aeneas.Std.I32.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_i64 (x y : I64) : Result I64 :=
  .ok (Aeneas.Std.I64.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_i128 (x y : I128) : Result I128 :=
  .ok (Aeneas.Std.I128.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_isize (x y : Isize) : Result Isize :=
  .ok (Aeneas.Std.Isize.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_u8 (x y : U8) : Result U8 :=
  .ok (Aeneas.Std.U8.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_u16 (x y : U16) : Result U16 :=
  .ok (Aeneas.Std.U16.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_u32 (x y : U32) : Result U32 :=
  .ok (Aeneas.Std.U32.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_u64 (x y : U64) : Result U64 :=
  .ok (Aeneas.Std.U64.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_u128 (x y : U128) : Result U128 :=
  .ok (Aeneas.Std.U128.wrapping_add x y)
def rust_primitives.arithmetic.wrapping_add_usize (x y : Usize) : Result Usize :=
  .ok (Aeneas.Std.Usize.wrapping_add x y)

def rust_primitives.arithmetic.wrapping_sub_i8 (x y : I8) : Result I8 :=
  .ok (Aeneas.Std.I8.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_i16 (x y : I16) : Result I16 :=
  .ok (Aeneas.Std.I16.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_i32 (x y : I32) : Result I32 :=
  .ok (Aeneas.Std.I32.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_i64 (x y : I64) : Result I64 :=
  .ok (Aeneas.Std.I64.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_i128 (x y : I128) : Result I128 :=
  .ok (Aeneas.Std.I128.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_isize (x y : Isize) : Result Isize :=
  .ok (Aeneas.Std.Isize.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_u8 (x y : U8) : Result U8 :=
  .ok (Aeneas.Std.U8.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_u16 (x y : U16) : Result U16 :=
  .ok (Aeneas.Std.U16.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_u32 (x y : U32) : Result U32 :=
  .ok (Aeneas.Std.U32.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_u64 (x y : U64) : Result U64 :=
  .ok (Aeneas.Std.U64.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_u128 (x y : U128) : Result U128 :=
  .ok (Aeneas.Std.U128.wrapping_sub x y)
def rust_primitives.arithmetic.wrapping_sub_usize (x y : Usize) : Result Usize :=
  .ok (Aeneas.Std.Usize.wrapping_sub x y)

def rust_primitives.arithmetic.wrapping_mul_i8 (x y : I8) : Result I8 :=
  .ok (Aeneas.Std.I8.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_i16 (x y : I16) : Result I16 :=
  .ok (Aeneas.Std.I16.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_i32 (x y : I32) : Result I32 :=
  .ok (Aeneas.Std.I32.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_i64 (x y : I64) : Result I64 :=
  .ok (Aeneas.Std.I64.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_i128 (x y : I128) : Result I128 :=
  .ok (Aeneas.Std.I128.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_isize (x y : Isize) : Result Isize :=
  .ok (Aeneas.Std.Isize.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_u8 (x y : U8) : Result U8 :=
  .ok (Aeneas.Std.U8.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_u16 (x y : U16) : Result U16 :=
  .ok (Aeneas.Std.U16.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_u32 (x y : U32) : Result U32 :=
  .ok (Aeneas.Std.U32.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_u64 (x y : U64) : Result U64 :=
  .ok (Aeneas.Std.U64.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_u128 (x y : U128) : Result U128 :=
  .ok (Aeneas.Std.U128.wrapping_mul x y)
def rust_primitives.arithmetic.wrapping_mul_usize (x y : Usize) : Result Usize :=
  .ok (Aeneas.Std.Usize.wrapping_mul x y)

def rust_primitives.arithmetic.saturating_add_i8 (x y : I8) : Result I8 :=
  .ok (IScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_i16 (x y : I16) : Result I16 :=
  .ok (IScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_i32 (x y : I32) : Result I32 :=
  .ok (IScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_i64 (x y : I64) : Result I64 :=
  .ok (IScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_i128 (x y : I128) : Result I128 :=
  .ok (IScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_isize (x y : Isize) : Result Isize :=
  .ok (IScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_u8 (x y : U8) : Result U8 :=
  .ok (UScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_u16 (x y : U16) : Result U16 :=
  .ok (UScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_u32 (x y : U32) : Result U32 :=
  .ok (UScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_u64 (x y : U64) : Result U64 :=
  .ok (UScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_u128 (x y : U128) : Result U128 :=
  .ok (UScalar.saturating_add x y)
def rust_primitives.arithmetic.saturating_add_usize (x y : Usize) : Result Usize :=
  .ok (UScalar.saturating_add x y)

def rust_primitives.arithmetic.saturating_sub_i8 (x y : I8) : Result I8 :=
  .ok (IScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_i16 (x y : I16) : Result I16 :=
  .ok (IScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_i32 (x y : I32) : Result I32 :=
  .ok (IScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_i64 (x y : I64) : Result I64 :=
  .ok (IScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_i128 (x y : I128) : Result I128 :=
  .ok (IScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_isize (x y : Isize) : Result Isize :=
  .ok (IScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_u8 (x y : U8) : Result U8 :=
  .ok (UScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_u16 (x y : U16) : Result U16 :=
  .ok (UScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_u32 (x y : U32) : Result U32 :=
  .ok (UScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_u64 (x y : U64) : Result U64 :=
  .ok (UScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_u128 (x y : U128) : Result U128 :=
  .ok (UScalar.saturating_sub x y)
def rust_primitives.arithmetic.saturating_sub_usize (x y : Usize) : Result Usize :=
  .ok (UScalar.saturating_sub x y)

def rust_primitives.arithmetic.overflowing_add_i8 (x y : I8) : Result (I8 × Bool) :=
  .ok (IScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_i16 (x y : I16) : Result (I16 × Bool) :=
  .ok (IScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_i32 (x y : I32) : Result (I32 × Bool) :=
  .ok (IScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_i64 (x y : I64) : Result (I64 × Bool) :=
  .ok (IScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_i128 (x y : I128) : Result (I128 × Bool) :=
  .ok (IScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_isize (x y : Isize) : Result (Isize × Bool) :=
  .ok (IScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_u8 (x y : U8) : Result (U8 × Bool) :=
  .ok (UScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_u16 (x y : U16) : Result (U16 × Bool) :=
  .ok (UScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_u32 (x y : U32) : Result (U32 × Bool) :=
  .ok (UScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_u64 (x y : U64) : Result (U64 × Bool) :=
  .ok (UScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_u128 (x y : U128) : Result (U128 × Bool) :=
  .ok (UScalar.overflowing_add x y)
def rust_primitives.arithmetic.overflowing_add_usize (x y : Usize) : Result (Usize × Bool) :=
  .ok (UScalar.overflowing_add x y)

def rust_primitives.arithmetic.rotate_right_i8 (x : I8) (n : U32) : Result I8 :=
  .ok (IScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_i16 (x : I16) (n : U32) : Result I16 :=
  .ok (IScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_i32 (x : I32) (n : U32) : Result I32 :=
  .ok (IScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_i64 (x : I64) (n : U32) : Result I64 :=
  .ok (IScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_i128 (x : I128) (n : U32) : Result I128 :=
  .ok (IScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_isize (x : Isize) (n : U32) : Result Isize :=
  .ok (IScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_u8 (x : U8) (n : U32) : Result U8 :=
  .ok (UScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_u16 (x : U16) (n : U32) : Result U16 :=
  .ok (UScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_u32 (x : U32) (n : U32) : Result U32 :=
  .ok (UScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_u64 (x : U64) (n : U32) : Result U64 :=
  .ok (UScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_u128 (x : U128) (n : U32) : Result U128 :=
  .ok (UScalar.rotate_right x n)
def rust_primitives.arithmetic.rotate_right_usize (x : Usize) (n : U32) : Result Usize :=
  .ok (UScalar.rotate_right x n)

def rust_primitives.arithmetic.rotate_left_i8 (x : I8) (n : U32) : Result I8 :=
  .ok (IScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_i16 (x : I16) (n : U32) : Result I16 :=
  .ok (IScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_i32 (x : I32) (n : U32) : Result I32 :=
  .ok (IScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_i64 (x : I64) (n : U32) : Result I64 :=
  .ok (IScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_i128 (x : I128) (n : U32) : Result I128 :=
  .ok (IScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_isize (x : Isize) (n : U32) : Result Isize :=
  .ok (IScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_u8 (x : U8) (n : U32) : Result U8 :=
  .ok (UScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_u16 (x : U16) (n : U32) : Result U16 :=
  .ok (UScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_u32 (x : U32) (n : U32) : Result U32 :=
  .ok (UScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_u64 (x : U64) (n : U32) : Result U64 :=
  .ok (UScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_u128 (x : U128) (n : U32) : Result U128 :=
  .ok (UScalar.rotate_left x n)
def rust_primitives.arithmetic.rotate_left_usize (x : Usize) (n : U32) : Result Usize :=
  .ok (UScalar.rotate_left x n)

end CoreModels
