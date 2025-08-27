
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

def hacspec_helper.to_le_u32s_3 (bytes : (RustSlice UInt8))
  : Result (RustArray UInt32 3) := do
  let (out : (RustArray UInt32 3)) ← pure (← hax.repeat 0 3);
  let (out : (RustArray UInt32 3)) ← pure
    (← hax.folds.fold_range
    0
      3
      (fun (out : (RustArray UInt32 3)) (_ : USize) => do true)
      out
      (fun (out : (RustArray UInt32 3)) (i : USize) => do
        (← hax.monomorphized_update_at.update_at_usize
        out
          i
          (← num._8_impl.from_le_bytes
          (← result.impl.unwrap (RustArray UInt8 4) array.TryFromSliceError
            (← convert.TryInto.try_into
              (← ops.index.Index.index
                bytes
                  (ops.range.Range.mk
                  (_start := (← 4 *? i)) (_end := (← (← 4 *? i) +? 4))))))))));
  out

def hacspec_helper.to_le_u32s_8 (bytes : (RustSlice UInt8))
  : Result (RustArray UInt32 8) := do
  let (out : (RustArray UInt32 8)) ← pure (← hax.repeat 0 8);
  let (out : (RustArray UInt32 8)) ← pure
    (← hax.folds.fold_range
    0
      8
      (fun (out : (RustArray UInt32 8)) (_ : USize) => do true)
      out
      (fun (out : (RustArray UInt32 8)) (i : USize) => do
        (← hax.monomorphized_update_at.update_at_usize
        out
          i
          (← num._8_impl.from_le_bytes
          (← result.impl.unwrap (RustArray UInt8 4) array.TryFromSliceError
            (← convert.TryInto.try_into
              (← ops.index.Index.index
                bytes
                  (ops.range.Range.mk
                  (_start := (← 4 *? i)) (_end := (← (← 4 *? i) +? 4))))))))));
  out

def hacspec_helper.to_le_u32s_16 (bytes : (RustSlice UInt8))
  : Result (RustArray UInt32 16) := do
  let (out : (RustArray UInt32 16)) ← pure (← hax.repeat 0 16);
  let (out : (RustArray UInt32 16)) ← pure
    (← hax.folds.fold_range
    0
      16
      (fun (out : (RustArray UInt32 16)) (_ : USize) => do true)
      out
      (fun (out : (RustArray UInt32 16)) (i : USize) => do
        (← hax.monomorphized_update_at.update_at_usize
        out
          i
          (← num._8_impl.from_le_bytes
          (← result.impl.unwrap (RustArray UInt8 4) array.TryFromSliceError
            (← convert.TryInto.try_into
              (← ops.index.Index.index
                bytes
                  (ops.range.Range.mk
                  (_start := (← 4 *? i)) (_end := (← (← 4 *? i) +? 4))))))))));
  out

def hacspec_helper.u32s_to_le_bytes (state : (RustArray UInt32 16))
  : Result (RustArray UInt8 64) := do
  let (out : (RustArray UInt8 64)) ← pure (← hax.repeat 0 64);
  let (out : (RustArray UInt8 64)) ← pure
    (← hax.folds.fold_range
    0
      (← slice.impl.len UInt32 (← unsize state))
      (fun (out : (RustArray UInt8 64)) (_ : USize) => do true)
      out
      (fun (out : (RustArray UInt8 64)) (i : USize) => do
        let (tmp : (RustArray UInt8 4)) ← pure
          (← num._8_impl.to_le_bytes (← ops.index.Index.index state i));
        (← hax.folds.fold_range
        0
          4
          (fun (out : (RustArray UInt8 64)) (_ : USize) => do true)
          out
          (fun (out : (RustArray UInt8 64)) (j : USize) => do
            (← hax.monomorphized_update_at.update_at_usize
            out
              (← (← i *? 4) +? j)
              (← ops.index.Index.index tmp j))))));
  out

def hacspec_helper.xor_state
  (state : (RustArray UInt32 16)) (other : (RustArray UInt32 16))
  : Result (RustArray UInt32 16) := do
  let (state : (RustArray UInt32 16)) ← pure
    (← hax.folds.fold_range
    0
      16
      (fun (state : (RustArray UInt32 16)) (_ : USize) => do true)
      state
      (fun (state : (RustArray UInt32 16)) (i : USize) => do
        (← hax.monomorphized_update_at.update_at_usize
        state
          i
          (← hax.machine_int.bitxor
          (← ops.index.Index.index state i)
            (← ops.index.Index.index other i)))));
  state

def hacspec_helper.add_state
  (state : (RustArray UInt32 16)) (other : (RustArray UInt32 16))
  : Result (RustArray UInt32 16) := do
  let (state : (RustArray UInt32 16)) ← pure
    (← hax.folds.fold_range
    0
      16
      (fun (state : (RustArray UInt32 16)) (_ : USize) => do true)
      state
      (fun (state : (RustArray UInt32 16)) (i : USize) => do
        (← hax.monomorphized_update_at.update_at_usize
        state
          i
          (← num._8_impl.wrapping_add
          (← ops.index.Index.index state i)
            (← ops.index.Index.index other i)))));
  state

def hacspec_helper.update_array
  (array : (RustArray UInt8 64)) (val : (RustSlice UInt8))
  : Result (RustArray UInt8 64) := do
  let (_ : hax.Tuple0) ← pure
    (← assert (← hax.machine_int.ge 64 (← slice.impl.len UInt8 val)));
  let (array : (RustArray UInt8 64)) ← pure
    (← hax.folds.fold_range
    0
      (← slice.impl.len UInt8 val)
      (fun (array : (RustArray UInt8 64)) (_ : USize) => do true)
      array
      (fun (array : (RustArray UInt8 64)) (i : USize) => do
        (← hax.monomorphized_update_at.update_at_usize
        array
          i
          (← ops.index.Index.index val i))));
  array

abbrev State := (RustArray UInt32 16)

abbrev Block := (RustArray UInt8 64)

abbrev ChaChaIV := (RustArray UInt8 12)

abbrev ChaChaKey := (RustArray UInt8 32)

abbrev StateIdx := (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0
15)

def chacha20_line
  (a : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (b :
  (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (d :
  (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (s : UInt32)
  (m : (RustArray UInt32 16)) : Result (RustArray UInt32 16) := do
  let (state : (RustArray UInt32 16)) ← pure m;
  let (state : (RustArray UInt32 16)) ← pure
    (← hax.update_at
    state
      a
      (← num._8_impl.wrapping_add
      (← ops.index.Index.index state a)
        (← ops.index.Index.index state b)));
  let (state : (RustArray UInt32 16)) ← pure
    (← hax.update_at
    state
      d
      (← hax.machine_int.bitxor
      (← ops.index.Index.index state d)
        (← ops.index.Index.index state a)));
  let (state : (RustArray UInt32 16)) ← pure
    (← hax.update_at
    state
      d
      (← num._8_impl.rotate_left (← ops.index.Index.index state d) s));
  state

def chacha20_quarter_round
  (a : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (b :
  (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (c :
  (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (d :
  (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (state :
  (RustArray UInt32 16)) : Result (RustArray UInt32 16) := do
  let (state : (RustArray UInt32 16)) ← pure (← chacha20_line a b d 16 state);
  let (state : (RustArray UInt32 16)) ← pure (← chacha20_line c d b 12 state);
  let (state : (RustArray UInt32 16)) ← pure (← chacha20_line a b d 8 state);
  (← chacha20_line c d b 7 state)

def chacha20_double_round (state : (RustArray UInt32 16))
  : Result (RustArray UInt32 16) := do
  let (state : (RustArray UInt32 16)) ← pure
    (← chacha20_quarter_round
    (0 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (4 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (8 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (12 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      state);
  let (state : (RustArray UInt32 16)) ← pure
    (← chacha20_quarter_round
    (1 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (5 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (9 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (13 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      state);
  let (state : (RustArray UInt32 16)) ← pure
    (← chacha20_quarter_round
    (2 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (6 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (10 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (14 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      state);
  let (state : (RustArray UInt32 16)) ← pure
    (← chacha20_quarter_round
    (3 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (7 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (11 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (15 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      state);
  let (state : (RustArray UInt32 16)) ← pure
    (← chacha20_quarter_round
    (0 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (5 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (10 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (15 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      state);
  let (state : (RustArray UInt32 16)) ← pure
    (← chacha20_quarter_round
    (1 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (6 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (11 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (12 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      state);
  let (state : (RustArray UInt32 16)) ← pure
    (← chacha20_quarter_round
    (2 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (7 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (8 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      (13 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
      state);
  (← chacha20_quarter_round
  (3 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
    (4 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
    (9 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
    (14 : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15))
    state)

def chacha20_rounds (state : (RustArray UInt32 16))
  : Result (RustArray UInt32 16) := do
  let (st : (RustArray UInt32 16)) ← pure state;
  let (st : (RustArray UInt32 16)) ← pure
    (← hax.folds.fold_range
    0
      10
      (fun (st : (RustArray UInt32 16)) (_ : Int32) => do true)
      st
      (fun (st : (RustArray UInt32 16)) (_i : Int32) => do
        (← chacha20_double_round st)));
  st

def chacha20_core (ctr : UInt32) (st0 : (RustArray UInt32 16))
  : Result (RustArray UInt32 16) := do
  let (state : (RustArray UInt32 16)) ← pure st0;
  let (state : (RustArray UInt32 16)) ← pure
    (← hax.monomorphized_update_at.update_at_usize
    state
      12
      (← num._8_impl.wrapping_add (← ops.index.Index.index state 12) ctr));
  let (k : (RustArray UInt32 16)) ← pure (← chacha20_rounds state);
  (← hacspec_helper.add_state state k)

def chacha20_init
  (key : (RustArray UInt8 32)) (iv : (RustArray UInt8 12)) (ctr : UInt32)
  : Result (RustArray UInt32 16) := do
  let ((key_u32 : (RustArray UInt32 8)) : (RustArray UInt32 8)) ← pure
    (← hacspec_helper.to_le_u32s_8 (← unsize key));
  let ((iv_u32 : (RustArray UInt32 3)) : (RustArray UInt32 3)) ← pure
    (← hacspec_helper.to_le_u32s_3 (← unsize iv));
  #v[1634760805,
    857760878,
    2036477234,
    1797285236,
    (← ops.index.Index.index key_u32 0),
    (← ops.index.Index.index key_u32 1),
    (← ops.index.Index.index key_u32 2),
    (← ops.index.Index.index key_u32 3),
    (← ops.index.Index.index key_u32 4),
    (← ops.index.Index.index key_u32 5),
    (← ops.index.Index.index key_u32 6),
    (← ops.index.Index.index key_u32 7),
    ctr,
    (← ops.index.Index.index iv_u32 0),
    (← ops.index.Index.index iv_u32 1),
    (← ops.index.Index.index iv_u32 2)]

def chacha20_key_block (state : (RustArray UInt32 16))
  : Result (RustArray UInt8 64) := do
  let (state : (RustArray UInt32 16)) ← pure (← chacha20_core 0 state);
  (← hacspec_helper.u32s_to_le_bytes state)

def chacha20_key_block0 (key : (RustArray UInt8 32)) (iv : (RustArray UInt8 12))
  : Result (RustArray UInt8 64) := do
  let (state : (RustArray UInt32 16)) ← pure (← chacha20_init key iv 0);
  (← chacha20_key_block state)

def chacha20_encrypt_block
  (st0 : (RustArray UInt32 16)) (ctr : UInt32) (plain : (RustArray UInt8 64))
  : Result (RustArray UInt8 64) := do
  let (st : (RustArray UInt32 16)) ← pure (← chacha20_core ctr st0);
  let ((pl : (RustArray UInt32 16)) : (RustArray UInt32 16)) ← pure
    (← hacspec_helper.to_le_u32s_16 (← unsize plain));
  let (encrypted : (RustArray UInt32 16)) ← pure
    (← hacspec_helper.xor_state st pl);
  (← hacspec_helper.u32s_to_le_bytes encrypted)

def _.requires
  (st0 : (RustArray UInt32 16)) (ctr : UInt32) (plain : (RustSlice UInt8))
  : Result Bool := do
  (← hax.machine_int.le (← slice.impl.len UInt8 plain) 64)

def chacha20_encrypt_last
  (st0 : (RustArray UInt32 16)) (ctr : UInt32) (plain : (RustSlice UInt8))
  : Result (vec.Vec UInt8 alloc.Global) := do
  let ((b : (RustArray UInt8 64)) : (RustArray UInt8 64)) ← pure
    (← hax.repeat 0 64);
  let (b : (RustArray UInt8 64)) ← pure (← hacspec_helper.update_array b plain);
  let (b : (RustArray UInt8 64)) ← pure (← chacha20_encrypt_block st0 ctr b);
  (← slice.impl.to_vec UInt8
  (← ops.index.Index.index
    b
      (ops.range.Range.mk
      (_start := 0) (_end := (← slice.impl.len UInt8 plain)))))

def chacha20_update (st0 : (RustArray UInt32 16)) (m : (RustSlice UInt8))
  : Result (vec.Vec UInt8 alloc.Global) := do
  let (blocks_out : (vec.Vec UInt8 alloc.Global)) ← pure
    (← vec.impl.new UInt8 hax.Tuple0);
  let (num_blocks : USize) ← pure (← (← slice.impl.len UInt8 m) /? 64);
  let (remainder_len : USize) ← pure (← (← slice.impl.len UInt8 m) %? 64);
  let (blocks_out : (vec.Vec UInt8 alloc.Global)) ← pure
    (← hax.folds.fold_range
    0
      num_blocks
      (fun (blocks_out : (vec.Vec UInt8 alloc.Global)) (_ : USize) => do true)
      blocks_out
      (fun (blocks_out : (vec.Vec UInt8 alloc.Global)) (i : USize) => do
        let (b : (RustArray UInt8 64)) ← pure
          (← chacha20_encrypt_block
          st0
            (← hax.cast_op i)
            (← result.impl.unwrap (RustArray UInt8 64) array.TryFromSliceError
            (← convert.TryInto.try_into
              (← ops.index.Index.index
                m
                  (ops.range.Range.mk
                  (_start := (← 64 *? i)) (_end := (← (← 64 *? i) +? 64)))))));
        let (_ : hax.Tuple0) ← pure
          (← assume
          (← prop.constructors.from_bool
            (← hax.machine_int.eq
              (← vec._1_impl.len UInt8 alloc.Global blocks_out)
                (← i *? 64))));
        let (blocks_out : (vec.Vec UInt8 alloc.Global)) ← pure
          (← vec._2_impl.extend_from_slice UInt8 alloc.Global
          blocks_out
            (← unsize b));
        blocks_out));
  let (_ : hax.Tuple0) ← pure
    (← assume
    (← prop.constructors.from_bool
      (← hax.machine_int.eq
        (← vec._1_impl.len UInt8 alloc.Global blocks_out)
          (← num_blocks *? 64))));
  let (blocks_out : (vec.Vec UInt8 alloc.Global)) ←
    if (← hax.machine_int.ne remainder_len 0)
    then
      let (b : (vec.Vec UInt8 alloc.Global)) ← pure
        (← chacha20_encrypt_last
        st0
          (← hax.cast_op num_blocks)
          (← ops.index.Index.index
          m
            (ops.range.Range.mk
            (_start := (← 64 *? num_blocks))
            (_end := (← slice.impl.len UInt8 m)))));
      let (blocks_out : (vec.Vec UInt8 alloc.Global)) ← pure
        (← vec._2_impl.extend_from_slice UInt8 alloc.Global
        blocks_out
          (← ops.deref.Deref.deref b));
      pure blocks_out
    else pure blocks_out;
  blocks_out

def chacha20
  (m : (RustSlice UInt8)) (key : (RustArray UInt8 32)) (iv : (RustArray
  UInt8
  12)) (ctr : UInt32) : Result (vec.Vec UInt8 alloc.Global) := do
  let (state : (RustArray UInt32 16)) ← pure (← chacha20_init key iv ctr);
  (← chacha20_update state m)

-- Theorems

@[spec]
theorem hacspec_helper.add_state_spec (state : (Vector u32 16)) (other : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper.add_state state other)
  ⦃ ⇓ _ => True ⦄ := by
  mvcgen [hacspec_helper.add_state]
  <;> try apply SPred.pure_intro
  <;> simp [Vector.size] at *
  <;> cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      rw [h]
      omega

@[spec]
theorem hacspec_helper.to_le_u32s_16_spec bytes :
  bytes.size = 64 →
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper.to_le_u32s_16 bytes)
  ⦃ ⇓ _ => True ⦄ := by
  intro
  open SpecNat in
  mvcgen [hacspec_helper.to_le_u32s_16,
    result.impl.unwrap.spec]
  <;> (try apply SPred.pure_intro)
  all_goals simp [USize.size, Vector.size] at *
  any_goals subst_vars
  all_goals try simp [USize.le_iff_toNat_le]
  all_goals try (cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      rw [h]
      omega ; done )


@[spec]
theorem hacspec_helper.to_le_u32s_3_spec bytes :
  bytes.size = 12 →
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper.to_le_u32s_3 bytes)
  ⦃ ⇓ _ => True ⦄ := by
  intros
  open SpecNat in
  mvcgen [hacspec_helper.to_le_u32s_3,
    result.impl.unwrap.spec]
  all_goals simp [USize.size, RustArray, Vector.size] at *
  any_goals subst_vars
  all_goals try simp [USize.le_iff_toNat_le]
  all_goals try (cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      rw [h]
      omega ; done )



@[spec]
theorem hacspec_helper.to_le_u32s_8_spec (bytes : (Array u8)) :
  bytes.size = 32 →
  ⦃ ⌜ True ⌝ ⦄
  ( hacspec_helper.to_le_u32s_8 bytes )
  ⦃ ⇓ _ => True ⦄ := by
  intros
  open SpecNat in
  mvcgen [hacspec_helper.to_le_u32s_8,
    result.impl.unwrap.spec]
  all_goals simp [USize.size, Vector.size] at *
  any_goals subst_vars
  all_goals try simp [USize.le_iff_toNat_le]
  all_goals try (cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      rw [h]
      omega ; done )

@[spec]
theorem hacspec_helper.u32s_to_le_bytes_spec (state : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper.u32s_to_le_bytes state)
  ⦃ ⇓ _ => True ⦄ := by
  intros
  open SpecNat in
  mvcgen [hacspec_helper.u32s_to_le_bytes,
    result.impl.unwrap.spec,
    num._8_impl.to_le_bytes]
  all_goals simp [USize.size, Vector.size] at *
  any_goals subst_vars
  all_goals try simp [USize.toNat_ofNat'] at *
  all_goals try (cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      rw [h] ;
      try rw [h] at h_2
      try rw [h] at h_3
      try rw [h] at h_5
      omega ; done )

@[spec]
theorem hacspec_helper.xor_state_spec (state other: (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper.xor_state state other)
  ⦃ ⇓ _ => True ⦄ := by
  intros
  open SpecNat in
  mvcgen [hacspec_helper.xor_state,
    result.impl.unwrap.spec,
    num._8_impl.to_le_bytes]
  all_goals simp [USize.size, Vector.size, USize.le_iff_toNat_le] at *
  any_goals subst_vars
  all_goals try simp [USize.toNat_ofNat'] at *
  all_goals try (cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      rw [h] ;
      omega ; done )


@[spec]
theorem hacspec_helper.update_array_spec (a: (Vector u8 64)) (v: Array u8) :
  v.size ≤ 64 →
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper.update_array a v)
  ⦃ ⇓ _ => True ⦄ := by
  intros
  open SpecNat in
  mvcgen_step 24 [hacspec_helper.update_array,
    result.impl.unwrap.spec]
  all_goals simp [USize.size, Vector.size, USize.le_iff_toNat_le, USize.lt_iff_toNat_lt] at *
  any_goals subst_vars
  all_goals try simp [USize.toNat_ofNat'] at *
  all_goals try (cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      try rw [h] ;
      try rw [h] at h_2
      try rw [h] at h_4
      omega ; done )

@[spec]
theorem chacha20_line_spec
    (a : (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (b :
    (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (d :
    (hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (s : u32)
    (m : (Vector u32 16)) :
  ⦃ a.toNat ≤ 15 ∧ b.toNat ≤ 15 ∧ d.toNat ≤ 15 ⦄
  (chacha20_line a b d s m )
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_line] <;> try (simp;omega;done)

@[spec]
theorem chacha20_quarter_round_spec a b c d state:
  ⦃ a.toNat ≤ 15 ∧ b.toNat ≤ 15 ∧ c.toNat ≤ 15 ∧ d.toNat ≤ 15 ⦄
  (chacha20_quarter_round a b c d state)
  ⦃ ⇓ _ => True ⦄ := by
  mintro ⟨ha, hb, hc, hd⟩
  mvcgen [chacha20_quarter_round,
          chacha20_line,
          hax.machine_int.bitxor,
          Result.ofOption,
          ] <;> try (simp;omega;done)

@[spec]
theorem chacha20_double_round_spec (state : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (chacha20_double_round state)
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_double_round] <;> simp <;> try omega

@[spec]
theorem chacha20_rounds_spec state :
  ⦃ ⌜ True ⌝ ⦄
  (chacha20_rounds state)
  ⦃ ⇓ _ => True ⦄ := by
  mvcgen [chacha20_rounds]


@[spec]
theorem chacha20_core_spec ctr state :
  ⦃ ⌜ True ⌝ ⦄
  (chacha20_core ctr state)
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_core,  GetElemResult, Result.ofOption]
  simp [Vector.size] at *


@[spec]
theorem chacha20_init_spec (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32) :
  ⦃ ⌜ True ⌝ ⦄
  (chacha20_init key iv ctr)
  ⦃ ⇓ _ => True ⦄ := by
  mvcgen [chacha20_init]
  all_goals simp [Vector.size_toArray]

@[spec]
theorem chacha20_key_block_spec (state : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (chacha20_key_block state)
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_key_block]

@[spec]
theorem chacha20_encrypt_block_spec (st0 : (Vector u32 16)) (ctr : u32) (plain : (Vector u8 64)) :
  ⦃ ⌜ True ⌝ ⦄
  ( chacha20_encrypt_block st0 ctr plain)
  ⦃ ⇓ _ => True ⦄ := by
  mvcgen [chacha20_encrypt_block]
  all_goals simp [Vector.size_toArray]


@[simp]
theorem System.Platform.numBits_ne_zero : ¬ System.Platform.numBits = 0 :=
by cases (System.Platform.numBits_eq) <;> grind

@[spec]
theorem chacha20_encrypt_last_spec (st0 : (Vector u32 16)) (ctr : u32) (plain : Array u8) :
  ⦃ plain.size <= 64 ⦄
  ( chacha20_encrypt_last st0 ctr plain)
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_encrypt_last, slice.impl.len]
  <;> (try apply SPred.pure_intro)
  <;> (try simp)
  simp [Vector.size, USize.le_iff_toNat_le] at *
  cases System.Platform.numBits_eq with
  | inl h
  | inr h => simp [h, Nat.mod_eq_of_lt] <;> try omega

example : ¬ (0:USize) = (1:USize) := by
  simp [USize.eq_iff_toBitVec_eq] at *

-- set_option pp.raw true
@[spec]
theorem chacha20_update_spec (st0 : (Vector u32 16)) (m : (Array u8)) :
  ⦃ m.size ≤ USize.size ⦄
  (chacha20_update st0 m)
  ⦃ ⇓ _ => True ⦄
:= by
  open SpecNat in
  mvcgen [chacha20_update,
    vec.impl.new, slice.impl.len,
    result.impl.unwrap.spec,
    vec._1_impl.len,
    ] <;> subst_vars
  all_goals simp [Array.size_extract, USize.eq_iff_toBitVec_eq, BitVec.toNat_eq, USize.size, USize.le_iff_toNat_le ] at *
  all_goals try cases System.Platform.numBits_eq with
    | inl h
    | inr h =>
      expose_names
      try rw [h]
      try rw [h] at h_1
      try rw [h] at h_2
      try rw [h] at h_3
      try rw [h] at h_4
      omega ; done

theorem chacha20_spec
  (m : (Array u8)) (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32) :
  m.size ≤ USize.size →
  ⦃⌜True⌝⦄
  (chacha20 m key iv ctr)
  ⦃ ⇓ _ => True ⦄
:= by
  intros
  mvcgen [chacha20]
