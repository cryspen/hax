-- Experimental lean backend for Hax
-- Lib.lean can be found in hax/proof-libs/lean :
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def hacspec_helper_to_le_u32s_3 (bytes : (Array u8))
  : Result (Vector u32 3) := do
  let (out : (Vector u32 3)) ← pure (← hax_repeat 0 3);
  let (out : (Vector u32 3)) ← pure
    (← hax_folds_fold_range
    0
      3
      (fun (out : (Vector u32 3)) (_ : usize)=> do true)
      out
      (fun (out : (Vector u32 3)) (i : usize)=> do
        (← hax_monomorphized_update_at_update_at_usize
        out
          i
          (← num__8_impl_from_le_bytes
          (← result_impl_unwrap (Vector u8 4) array_TryFromSliceError
            (← convert_TryInto_try_into
              (← ops_index_Index_index
                bytes
                  (constr_ops_range_Range
                    (ops_range_Range_start := (← hax_machine_int_mul 4 i))
                    (ops_range_Range_end := (← (← hax_machine_int_mul 4 i) +?
                    4))))))))));
  out

def hacspec_helper_to_le_u32s_8 (bytes : (Array u8))
  : Result (Vector u32 8) := do
  let (out : (Vector u32 8)) ← pure (← hax_repeat 0 8);
  let (out : (Vector u32 8)) ← pure
    (← hax_folds_fold_range
    0
      8
      (fun (out : (Vector u32 8)) (_ : usize)=> do true)
      out
      (fun (out : (Vector u32 8)) (i : usize)=> do
        (← hax_monomorphized_update_at_update_at_usize
        out
          i
          (← num__8_impl_from_le_bytes
          (← result_impl_unwrap (Vector u8 4) array_TryFromSliceError
            (← convert_TryInto_try_into
              (← ops_index_Index_index
                bytes
                  (constr_ops_range_Range
                    (ops_range_Range_start := (← hax_machine_int_mul 4 i))
                    (ops_range_Range_end := (← (← hax_machine_int_mul 4 i) +?
                    4))))))))));
  out

def hacspec_helper_to_le_u32s_16 (bytes : (Array u8))
  : Result (Vector u32 16) := do
  let (out : (Vector u32 16)) ← pure (← hax_repeat 0 16);
  let (out : (Vector u32 16)) ← pure
    (← hax_folds_fold_range
    0
      16
      (fun (out : (Vector u32 16)) (_ : usize)=> do true)
      out
      (fun (out : (Vector u32 16)) (i : usize)=> do
        (← hax_monomorphized_update_at_update_at_usize
        out
          i
          (← num__8_impl_from_le_bytes
          (← result_impl_unwrap (Vector u8 4) array_TryFromSliceError
            (← convert_TryInto_try_into
              (← ops_index_Index_index
                bytes
                  (constr_ops_range_Range
                    (ops_range_Range_start := (← hax_machine_int_mul 4 i))
                    (ops_range_Range_end := (← (← hax_machine_int_mul 4 i) +?
                    4))))))))));
  out

def hacspec_helper_u32s_to_le_bytes (state : (Vector u32 16))
  : Result (Vector u8 64) := do
  let (out : (Vector u8 64)) ← pure (← hax_repeat 0 64);
  let (out : (Vector u8 64)) ← pure
    (← hax_folds_fold_range
    0
      (← slice_impl_len u32 (← unsize state))
      (fun (out : (Vector u8 64)) (_ : usize)=> do true)
      out
      (fun (out : (Vector u8 64)) (i : usize)=> do
        let (tmp : (Vector u8 4)) ← pure
          (← num__8_impl_to_le_bytes (← ops_index_Index_index state i));
        (← hax_folds_fold_range
        0
          4
          (fun (out : (Vector u8 64)) (_ : usize)=> do true)
          out
          (fun (out : (Vector u8 64)) (j : usize)=> do
            (← hax_monomorphized_update_at_update_at_usize
            out
              (← (← hax_machine_int_mul i 4) +? j)
              (← ops_index_Index_index tmp j))))));
  out

def hacspec_helper_xor_state (state : (Vector u32 16)) (other : (Vector u32 16))
  : Result (Vector u32 16) := do
  let (state : (Vector u32 16)) ← pure
    (← hax_folds_fold_range
    0
      16
      (fun (state : (Vector u32 16)) (_ : usize)=> do true)
      state
      (fun (state : (Vector u32 16)) (i : usize)=> do
        (← hax_monomorphized_update_at_update_at_usize
        state
          i
          (← hax_machine_int_bitxor
          (← ops_index_Index_index state i)
            (← ops_index_Index_index other i)))));
  state

def hacspec_helper_add_state (state : (Vector u32 16)) (other : (Vector u32 16))
  : Result (Vector u32 16) := do
  let (state : (Vector u32 16)) ← pure
    (← hax_folds_fold_range
    0
      16
      (fun (state : (Vector u32 16)) (_ : usize)=> do true)
      state
      (fun (state : (Vector u32 16)) (i : usize)=> do
        (← hax_monomorphized_update_at_update_at_usize
        state
          i
          (← num__8_impl_wrapping_add
          (← ops_index_Index_index state i)
            (← ops_index_Index_index other i)))));
  state

def hacspec_helper_update_array (array : (Vector u8 64)) (val : (Array u8))
  : Result (Vector u8 64) := do
  let (_ : hax_Tuple0) ← pure
    (← assert (← hax_machine_int_ge 64 (← slice_impl_len u8 val)));
  let (array : (Vector u8 64)) ← pure
    (← hax_folds_fold_range
    0
      (← slice_impl_len u8 val)
      (fun (array : (Vector u8 64)) (_ : usize)=> do true)
      array
      (fun (array : (Vector u8 64)) (i : usize)=> do
        (← hax_monomorphized_update_at_update_at_usize
        array
          i
          (← ops_index_Index_index val i))));
  array

abbrev State := (Vector u32 16)
abbrev Block := (Vector u8 64)
abbrev ChaChaIV := (Vector u8 12)
abbrev ChaChaKey := (Vector u8 32)
abbrev StateIdx := (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0
15)
def chacha20_line
    (a : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (b :
    (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (d :
    (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (s : u32)
    (m : (Vector u32 16)) : Result (Vector u32 16) := do
  let (state : (Vector u32 16)) ← pure m;
  let (state : (Vector u32 16)) ← pure
    (← hax_update_at
    state
      a
      (← num__8_impl_wrapping_add
      (← ops_index_Index_index state a)
        (← ops_index_Index_index state b)));
  let (state : (Vector u32 16)) ← pure
    (← hax_update_at
    state
      d
      (← hax_machine_int_bitxor
      (← ops_index_Index_index state d)
        (← ops_index_Index_index state a)));
  let (state : (Vector u32 16)) ← pure
    (← hax_update_at
    state
      d
      (← num__8_impl_rotate_left (← ops_index_Index_index state d) s));
  state

def chacha20_quarter_round
    (a : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (b :
    (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (c :
    (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (d :
    (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (state :
    (Vector u32 16)) : Result (Vector u32 16) := do
  let (state : (Vector u32 16)) ← pure (← chacha20_line a b d 16 state);
  let (state : (Vector u32 16)) ← pure (← chacha20_line c d b 12 state);
  let (state : (Vector u32 16)) ← pure (← chacha20_line a b d 8 state);
  (← chacha20_line c d b 7 state)

def chacha20_double_round (state : (Vector u32 16))
  : Result (Vector u32 16) := do
  let (state : (Vector u32 16)) ← pure
    (← chacha20_quarter_round
    (0 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (4 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (8 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (12 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      state);
  let (state : (Vector u32 16)) ← pure
    (← chacha20_quarter_round
    (1 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (5 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (9 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (13 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      state);
  let (state : (Vector u32 16)) ← pure
    (← chacha20_quarter_round
    (2 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (6 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (10 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (14 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      state);
  let (state : (Vector u32 16)) ← pure
    (← chacha20_quarter_round
    (3 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (7 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (11 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (15 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      state);
  let (state : (Vector u32 16)) ← pure
    (← chacha20_quarter_round
    (0 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (5 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (10 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (15 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      state);
  let (state : (Vector u32 16)) ← pure
    (← chacha20_quarter_round
    (1 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (6 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (11 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (12 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      state);
  let (state : (Vector u32 16)) ← pure
    (← chacha20_quarter_round
    (2 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (7 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (8 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      (13 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
      state);
  (← chacha20_quarter_round
  (3 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
    (4 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
    (9 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
    (14 : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15))
    state)

def chacha20_rounds (state : (Vector u32 16)) : Result (Vector u32 16) := do
  let (st : (Vector u32 16)) ← pure state;
  let (st : (Vector u32 16)) ← pure
    (← hax_folds_fold_range
    0
      10
      (fun (st : (Vector u32 16)) (_ : i32)=> do true)
      st
      (fun (st : (Vector u32 16)) (_i : i32)=> do
        (← chacha20_double_round st)));
  st

def chacha20_core (ctr : u32) (st0 : (Vector u32 16))
  : Result (Vector u32 16) := do
  let (state : (Vector u32 16)) ← pure st0;
  let (state : (Vector u32 16)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    state
      12
      (← num__8_impl_wrapping_add (← ops_index_Index_index state 12) ctr));
  let (k : (Vector u32 16)) ← pure (← chacha20_rounds state);
  (← hacspec_helper_add_state state k)

def chacha20_init (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32)
  : Result (Vector u32 16) := do
  let (key_u32 : (Vector u32 8)) ← pure
    (← hacspec_helper_to_le_u32s_8 (← unsize key));
  let (iv_u32 : (Vector u32 3)) ← pure
    (← hacspec_helper_to_le_u32s_3 (← unsize iv));
  #v[1634760805,
    857760878,
    2036477234,
    1797285236,
    (← ops_index_Index_index key_u32 0),
    (← ops_index_Index_index key_u32 1),
    (← ops_index_Index_index key_u32 2),
    (← ops_index_Index_index key_u32 3),
    (← ops_index_Index_index key_u32 4),
    (← ops_index_Index_index key_u32 5),
    (← ops_index_Index_index key_u32 6),
    (← ops_index_Index_index key_u32 7),
    ctr,
    (← ops_index_Index_index iv_u32 0),
    (← ops_index_Index_index iv_u32 1),
    (← ops_index_Index_index iv_u32 2)]

def chacha20_key_block (state : (Vector u32 16)) : Result (Vector u8 64) := do
  let (state : (Vector u32 16)) ← pure (← chacha20_core 0 state);
  (← hacspec_helper_u32s_to_le_bytes state)

def chacha20_key_block0 (key : (Vector u8 32)) (iv : (Vector u8 12))
  : Result (Vector u8 64) := do
  let (state : (Vector u32 16)) ← pure (← chacha20_init key iv 0);
  (← chacha20_key_block state)

def chacha20_encrypt_block
    (st0 : (Vector u32 16)) (ctr : u32) (plain : (Vector u8 64))
  : Result (Vector u8 64) := do
  let (st : (Vector u32 16)) ← pure (← chacha20_core ctr st0);
  let (pl : (Vector u32 16)) ← pure
    (← hacspec_helper_to_le_u32s_16 (← unsize plain));
  let (encrypted : (Vector u32 16)) ← pure (← hacspec_helper_xor_state st pl);
  (← hacspec_helper_u32s_to_le_bytes encrypted)

def __requires (st0 : (Vector u32 16)) (ctr : u32) (plain : (Array u8))
  : Result Bool := do
  (← hax_machine_int_le (← slice_impl_len u8 plain) 64)

def chacha20_encrypt_last
    (st0 : (Vector u32 16)) (ctr : u32) (plain : (Array u8))
  : Result (vec_Vec u8 alloc_Global) := do
  let (b : (Vector u8 64)) ← pure (← hax_repeat 0 64);
  let (b : (Vector u8 64)) ← pure (← hacspec_helper_update_array b plain);
  let (b : (Vector u8 64)) ← pure (← chacha20_encrypt_block st0 ctr b);
  (← slice_impl_to_vec u8
  (← ops_index_Index_index
    b
      (constr_ops_range_Range
        (ops_range_Range_start := 0)
        (ops_range_Range_end := (← slice_impl_len u8 plain)))))

def chacha20_update (st0 : (Vector u32 16)) (m : (Array u8))
  : Result (vec_Vec u8 alloc_Global) := do
  let (blocks_out : (vec_Vec u8 alloc_Global)) ← pure
    (← vec_impl_new u8 hax_Tuple0);
  let (num_blocks : usize) ← pure
    (← hax_machine_int_div (← slice_impl_len u8 m) 64);
  let (remainder_len : usize) ← pure
    (← hax_machine_int_rem (← slice_impl_len u8 m) 64);
  let (blocks_out : (vec_Vec u8 alloc_Global)) ← pure
    (← hax_folds_fold_range
    0
      num_blocks
      (fun (blocks_out : (vec_Vec u8 alloc_Global)) (_ : usize)=> do true)
      blocks_out
      (fun (blocks_out : (vec_Vec u8 alloc_Global)) (i : usize)=> do
        let (b : (Vector u8 64)) ← pure
          (← chacha20_encrypt_block
          st0
            (← hax_cast_op i)
            (← result_impl_unwrap (Vector u8 64) array_TryFromSliceError
            (← convert_TryInto_try_into
              (← ops_index_Index_index
                m
                  (constr_ops_range_Range
                    (ops_range_Range_start := (← hax_machine_int_mul 64 i))
                    (ops_range_Range_end := (← (← hax_machine_int_mul 64 i) +?
                    64)))))));
        let (_ : hax_Tuple0) ← pure
          (← assume
          (← prop_constructors_from_bool
            (← hax_machine_int_eq
              (← vec__1_impl_len u8 alloc_Global blocks_out)
                (← hax_machine_int_mul i 64))));
        let (blocks_out : (vec_Vec u8 alloc_Global)) ← pure
          (← vec__2_impl_extend_from_slice u8 alloc_Global
          blocks_out
            (← unsize b));
        blocks_out));
  let (_ : hax_Tuple0) ← pure
    (← assume
    (← prop_constructors_from_bool
      (← hax_machine_int_eq
        (← vec__1_impl_len u8 alloc_Global blocks_out)
          (← hax_machine_int_mul num_blocks 64))));
  let (blocks_out : (vec_Vec u8 alloc_Global)) ←
    if (← hax_machine_int_ne remainder_len 0)
    then
      let (b : (vec_Vec u8 alloc_Global)) ← pure
        (← chacha20_encrypt_last
        st0
          (← hax_cast_op num_blocks)
          (← ops_index_Index_index
          m
            (constr_ops_range_Range
              (ops_range_Range_start := (← hax_machine_int_mul 64 num_blocks))
              (ops_range_Range_end := (← slice_impl_len u8 m)))));
      let (blocks_out : (vec_Vec u8 alloc_Global)) ← pure
        (← vec__2_impl_extend_from_slice u8 alloc_Global
        blocks_out
          (← ops_deref_Deref_deref b));
      blocks_out
    else blocks_out;
  blocks_out

def chacha20
    (m : (Array u8)) (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32)
  : Result (vec_Vec u8 alloc_Global) := do
  let (state : (Vector u32 16)) ← pure (← chacha20_init key iv ctr);
  (← chacha20_update state m)


-- Theorems

@[spec]
theorem hacspec_helper_add_state_spec (state : (Vector u32 16)) (other : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper_add_state state other)
  ⦃ ⇓ _ => True ⦄
:= by sorry

@[spec]
theorem hacspec_helper_to_le_u32s_16_spec bytes :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper_to_le_u32s_16 bytes)
  ⦃ ⇓ _ => True ⦄
:= by sorry

@[spec]
theorem hacspec_helper_to_le_u32s_3_spec bytes :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper_to_le_u32s_3 bytes)
  ⦃ ⇓ _ => True ⦄
:= by sorry

@[spec]
theorem hacspec_helper_to_le_u32s_8_spec (bytes : (Array u8)) :
  ⦃ ⌜ True ⌝ ⦄
  ( hacspec_helper_to_le_u32s_8 bytes )
  ⦃ ⇓ _ => True ⦄
:= by sorry

@[spec]
theorem hacspec_helper_u32s_to_le_bytes_spec (state : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper_u32s_to_le_bytes state)
  ⦃ ⇓ _ => True ⦄
:= by sorry

@[spec]
theorem hacspec_helper_xor_state_spec (state other: (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper_xor_state state other)
  ⦃ ⇓ _ => True ⦄
:= by sorry

@[spec]
theorem hacspec_helper_update_array_spec (a: (Vector u8 64)) v :
  ⦃ ⌜ True ⌝ ⦄
  (hacspec_helper_update_array a v)
  ⦃ ⇓ _ => True ⦄
:= by sorry

@[spec]
theorem chacha20_line_spec
    (a : (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (b :
    (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (d :
    (hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 15)) (s : u32)
    (m : (Vector u32 16)) :
  ⦃ a.toNat ≤ 15 ∧ b.toNat ≤ 15 ∧ d.toNat ≤ 15 ⦄
  (chacha20_line a b d s m )
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_line] <;> try (simp;omega;done)
  mvcgen [hax_machine_int_bitxor]
  simp
  omega

@[spec]
theorem chacha20_quarter_round_spec a b c d state:
  ⦃ a.toNat ≤ 15 ∧ b.toNat ≤ 15 ∧ c.toNat ≤ 15 ∧ d.toNat ≤ 15 ⦄
  (chacha20_quarter_round a b c d state)
  ⦃ ⇓ _ => True ⦄ := by
  mintro ⟨ha, hb, hc, hd⟩
  mvcgen [chacha20_quarter_round,
          chacha20_line,
          hax_machine_int_bitxor,
          num__8_impl_rotate_left,
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
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_rounds, hax_folds_fold_range_spec] <;> (try ((simp <;> try omega) ; done))
  apply SPred.and_intro <;> (try (simp; done))
  apply SPred.and_intro <;> (try (simp; done))
  apply SPred.forall_intro; intro acc
  apply SPred.forall_intro; intro i
  intros _ _ _
  mvcgen


@[spec]
theorem chacha20_core_spec ctr state :
  ⦃ ⌜ True ⌝ ⦄
  (chacha20_core ctr state)
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_core, ops_index_Index_index, GetElemResult, Result.ofOption, hax_monomorphized_update_at_update_at_usize]
  simp [Vector.size] at *


@[spec]
theorem chacha20_init_spec (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32) :
  ⦃ ⌜ True ⌝ ⦄
  (chacha20_init key iv ctr)
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_init]

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
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_encrypt_block]

@[simp]
theorem System.Platform.numBits_ne_zero : ¬ System.Platform.numBits = 0 :=
by cases (System.Platform.numBits_eq) <;> grind

@[spec]
theorem chacha20_encrypt_last_spec (st0 : (Vector u32 16)) (ctr : u32) (plain : Array u8) :
  ⦃ plain.size <= 64 ⦄
  ( chacha20_encrypt_last st0 ctr plain)
  ⦃ ⇓ _ => True ⦄
:= by
  mvcgen [chacha20_encrypt_last, slice_impl_len]
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
  open USize.SpecNat in
  mvcgen [chacha20_update, vec_impl_new, slice_impl_len] <;> subst_vars
  . -- No division by zero
    simp [USize.eq_iff_toBitVec_eq, BitVec.toNat_eq]
    cases System.Platform.numBits_eq with
    | inl h
    | inr h => simp [h]
  . -- No remainder by zero
    simp [USize.eq_iff_toBitVec_eq, BitVec.toNat_eq]
    cases System.Platform.numBits_eq with
    | inl h
    | inr h => simp [h]
  . -- loop
    apply SPred.and_intro ; simp
    apply SPred.and_intro ; simp
    apply SPred.forall_intro; intro acc
    apply SPred.forall_intro; intro i
    apply SPred.imp_intro
    apply SPred.imp_intro
    apply SPred.imp_intro
    open USize.SpecNat in
    mvcgen [convert_TryInto_try_into,
            result_impl_unwrap,
            vec__1_impl_len]
    <;> subst_vars
    <;> try apply SPred.pure_intro
    . -- No overflow on multiplication
      simp [USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h =>
        expose_names
        rw [h] at h_1 h_2 ⊢
        omega
    . -- No overflow on multiplication
      simp [USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h =>
        expose_names
        rw [h] at h_1 h_2 ⊢
        omega
    . -- No overflow on addition
      simp [USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h =>
        expose_names
        rw [h] at h_1 h_2 ⊢
        omega
    . -- No overflow on addition
      simp [USize.le_iff_toNat_le, USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h =>
        expose_names
        rw [h] at h_1 h_2 ⊢
        omega
    . -- No overflow on addition
      simp [USize.le_iff_toNat_le, USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h =>
        expose_names
        rw [h] at h_1 h_2 ⊢
        omega
    . -- No overflow on addition
      simp [USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h =>
        expose_names
        rw [h] at h_1 h_2 ⊢
        omega
    . simp
      split at * <;> injections
      apply_assumption
      simp [Array.size_extract, USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h => expose_names; rw [h] at h_1 h_2 h_3 ⊢ ; omega
  . mvcgen [vec__1_impl_len, assume, hax_machine_int_eq, hax_machine_int_ne]
    <;> (try apply SPred.pure_intro)
    <;> subst_vars
    . simp [USize.toNat_div, USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h => expose_names; rw [h] at h_1 ⊢ ; omega
    . simp [USize.toNat_div, USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h => expose_names; rw [h] at h_1 ⊢ ; omega
    . simp [USize.le_iff_toNat_le, USize.size] at *
      cases System.Platform.numBits_eq with
      | inl h
      | inr h =>
        expose_names
        rw [h] at h_1 ⊢
        omega
    . apply USize.le_refl
    . simp [USize.size] at *
      cases System.Platform.numBits_eq with
        | inl h
        | inr h =>
          expose_names
          rw [h] at h_1 ⊢
          omega

theorem chacha20_spec
  (m : (Array u8)) (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32) :
  m.size ≤ USize.size →
  ⦃⌜True⌝⦄
  (chacha20 m key iv ctr)
  ⦃ ⇓ _ => True ⦄
:= by
  intros
  mvcgen [chacha20]
