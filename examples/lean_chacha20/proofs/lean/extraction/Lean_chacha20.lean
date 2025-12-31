
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

def Lean_chacha20.Hacspec_helper.to_le_u32s_3
  (bytes : (RustSlice u8))
  : RustM (RustArray u32 3)
  := do
  let out : (RustArray u32 3) ←
    (Rust_primitives.Hax.repeat (0 : u32) (3 : usize));
  let out : (RustArray u32 3) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (3 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i => (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← (Core.Num.Impl_8.from_le_bytes
            (← (Core.Result.Impl.unwrap
              (RustArray u8 4)
              Core.Array.TryFromSliceError
              (← (Core.Convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← bytes[
                  (Core.Ops.Range.Range.mk
                    (start := (← ((4 : usize) *? i)))
                    (_end := (← ((← ((4 : usize) *? i)) +? (4 : usize)))))
                  ]_?)))))))) : RustM (RustArray u32 3))));
  (pure out)


@[spec]
theorem Lean_chacha20.Hacspec_helper.to_le_u32s_3.spec bytes :
  bytes.size = 12 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.to_le_u32s_3 bytes)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  mvcgen [Lean_chacha20.Hacspec_helper.to_le_u32s_3] <;> try grind

def Lean_chacha20.Hacspec_helper.to_le_u32s_8
  (bytes : (RustSlice u8))
  : RustM (RustArray u32 8)
  := do
  let out : (RustArray u32 8) ←
    (Rust_primitives.Hax.repeat (0 : u32) (8 : usize));
  let out : (RustArray u32 8) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i => (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← (Core.Num.Impl_8.from_le_bytes
            (← (Core.Result.Impl.unwrap
              (RustArray u8 4)
              Core.Array.TryFromSliceError
              (← (Core.Convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← bytes[
                  (Core.Ops.Range.Range.mk
                    (start := (← ((4 : usize) *? i)))
                    (_end := (← ((← ((4 : usize) *? i)) +? (4 : usize)))))
                  ]_?)))))))) : RustM (RustArray u32 8))));
  (pure out)


@[spec]
theorem Lean_chacha20.Hacspec_helper.to_le_u32s_8_spec (bytes : (Array u8)) :
  bytes.size = 32 →
  ⦃ ⌜ True ⌝ ⦄
  ( Lean_chacha20.Hacspec_helper.to_le_u32s_8 bytes )
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  mvcgen [Lean_chacha20.Hacspec_helper.to_le_u32s_8] <;> try grind

def Lean_chacha20.Hacspec_helper.to_le_u32s_16
  (bytes : (RustSlice u8))
  : RustM (RustArray u32 16)
  := do
  let out : (RustArray u32 16) ←
    (Rust_primitives.Hax.repeat (0 : u32) (16 : usize));
  let out : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i => (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← (Core.Num.Impl_8.from_le_bytes
            (← (Core.Result.Impl.unwrap
              (RustArray u8 4)
              Core.Array.TryFromSliceError
              (← (Core.Convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← bytes[
                  (Core.Ops.Range.Range.mk
                    (start := (← ((4 : usize) *? i)))
                    (_end := (← ((← ((4 : usize) *? i)) +? (4 : usize)))))
                  ]_?)))))))) : RustM (RustArray u32 16))));
  (pure out)


@[spec]
theorem Lean_chacha20.Hacspec_helper.to_le_u32s_16_spec bytes :
  bytes.size = 64 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.to_le_u32s_16 bytes)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intro
  mvcgen [Lean_chacha20.Hacspec_helper.to_le_u32s_16] <;> try grind

def Lean_chacha20.Hacspec_helper.u32s_to_le_bytes
  (state : (RustArray u32 16))
  : RustM (RustArray u8 64)
  := do
  let out : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let out : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Core.Slice.Impl.len u32 (← (Rust_primitives.unsize state))))
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i => (do
        let tmp : (RustArray u8 4) ←
          (Core.Num.Impl_8.to_le_bytes (← state[i]_?));
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (4 : usize)
          (fun out _ => (do (pure true) : RustM Bool))
          out
          (fun out j => (do
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              (← ((← (i *? (4 : usize))) +? j))
              (← tmp[j]_?)) : RustM (RustArray u8 64)))) : RustM
        (RustArray u8 64))));
  (pure out)


@[spec]
theorem Lean_chacha20.Hacspec_helper.u32s_to_le_bytes_spec (state : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.u32s_to_le_bytes state)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  mvcgen [Lean_chacha20.Hacspec_helper.u32s_to_le_bytes, Core.Num.Impl_8.to_le_bytes]
    <;> try grind

def Lean_chacha20.Hacspec_helper.xor_state
  (state : (RustArray u32 16))
  (other : (RustArray u32 16))
  : RustM (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i => (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          i
          (← ((← state[i]_?) ^^^? (← other[i]_?)))) : RustM
        (RustArray u32 16))));
  (pure state)


@[spec]
theorem Lean_chacha20.Hacspec_helper.xor_state_spec (state other: (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.xor_state state other)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  mvcgen [Lean_chacha20.Hacspec_helper.xor_state, Core.Num.Impl_8.to_le_bytes]
    <;> try grind

def Lean_chacha20.Hacspec_helper.add_state
  (state : (RustArray u32 16))
  (other : (RustArray u32 16))
  : RustM (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i => (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          i
          (← (Core.Num.Impl_8.wrapping_add (← state[i]_?) (← other[i]_?)))) :
        RustM (RustArray u32 16))));
  (pure state)


@[spec]
theorem Lean_chacha20.Hacspec_helper.add_state_spec (state : (Vector u32 16)) (other : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.add_state state other)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have := USize.le_size
  mvcgen [Lean_chacha20.Hacspec_helper.add_state]
  <;> simp [Vector.size] at *
  <;> apply (USize.lt_ofNat_iff _).mp
  <;> omega
  done

def Lean_chacha20.Hacspec_helper.update_array
  (array : (RustArray u8 64))
  (val : (RustSlice u8))
  : RustM (RustArray u8 64)
  := do
  let _ ←
    (Hax_lib.assert
      (← (Rust_primitives.Hax.Machine_int.ge
        (64 : usize)
        (← (Core.Slice.Impl.len u8 val)))));
  let array : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Core.Slice.Impl.len u8 val))
      (fun array _ => (do (pure true) : RustM Bool))
      array
      (fun array i => (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          array
          i
          (← val[i]_?)) : RustM (RustArray u8 64))));
  (pure array)


@[spec]
theorem Lean_chacha20.Hacspec_helper.update_array_spec (a: (Vector u8 64)) (v: Array u8) :
  v.size ≤ 64 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.update_array a v)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  mvcgen [Lean_chacha20.Hacspec_helper.update_array, Hax_lib.assert]
    <;> try grind

abbrev Lean_chacha20.State : Type := (RustArray u32 16)

abbrev Lean_chacha20.Block : Type := (RustArray u8 64)

abbrev Lean_chacha20.ChaChaIV : Type := (RustArray u8 12)

abbrev Lean_chacha20.ChaChaKey : Type := (RustArray u8 32)

abbrev Lean_chacha20.StateIdx
  : Type :=
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize)))

def Lean_chacha20.chacha20_line
  (a :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize))))
  (b :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize))))
  (d :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize))))
  (s : u32)
  (m : (RustArray u32 16))
  : RustM (RustArray u32 16)
  := do
  let state : (RustArray u32 16) := m;
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.update_at
      state
      a
      (← (Core.Num.Impl_8.wrapping_add (← state[a]_?) (← state[b]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.update_at
      state
      d
      (← ((← state[d]_?) ^^^? (← state[a]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.update_at
      state
      d
      (← (Core.Num.Impl_8.rotate_left (← state[d]_?) s)));
  (pure state)


@[spec]
theorem Lean_chacha20.chacha20_line_spec
    (a : (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (b :
    (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (d :
    (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize 0 15)) (s : u32)
    (m : (Vector u32 16)) :
  a.toNat ≤ 15 →
  b.toNat ≤ 15 →
  d.toNat ≤ 15 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.chacha20_line a b d s m )
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄
  := by intros; mvcgen [Lean_chacha20.chacha20_line] <;> omega

def Lean_chacha20.chacha20_quarter_round
  (a :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize))))
  (b :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize))))
  (c :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize))))
  (d :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    ((0 : usize))
    ((15 : usize))))
  (state : (RustArray u32 16))
  : RustM (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_line a b d (16 : u32) state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_line c d b (12 : u32) state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_line a b d (8 : u32) state);
  (Lean_chacha20.chacha20_line c d b (7 : u32) state)


@[spec]
theorem Lean_chacha20.chacha20_quarter_round_spec a b c d state:
  a.toNat ≤ 15 →
  b.toNat ≤ 15 →
  c.toNat ≤ 15 →
  d.toNat ≤ 15 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.chacha20_quarter_round a b c d state)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄
:= by
  intros
  mvcgen [Lean_chacha20.chacha20_quarter_round,
          Lean_chacha20.chacha20_line,
          RustM.ofOption, ]
  <;> try omega

def Lean_chacha20.chacha20_double_round
  (state : (RustArray u32 16))
  : RustM (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_quarter_round
      ((0 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((4 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((8 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((12 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_quarter_round
      ((1 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((5 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((9 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((13 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_quarter_round
      ((2 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((6 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((10 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((14 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_quarter_round
      ((3 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((7 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((11 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((15 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_quarter_round
      ((0 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((5 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((10 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((15 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_quarter_round
      ((1 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((6 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((11 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((12 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      state);
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_quarter_round
      ((2 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((7 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((8 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      ((13 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        ((0 : usize))
        ((15 : usize))))
      state);
  (Lean_chacha20.chacha20_quarter_round
    ((3 : usize) :
    (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
      ((0 : usize))
      ((15 : usize))))
    ((4 : usize) :
    (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
      ((0 : usize))
      ((15 : usize))))
    ((9 : usize) :
    (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
      ((0 : usize))
      ((15 : usize))))
    ((14 : usize) :
    (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
      ((0 : usize))
      ((15 : usize))))
    state)

def Lean_chacha20.chacha20_rounds
  (state : (RustArray u32 16))
  : RustM (RustArray u32 16)
  := do
  let st : (RustArray u32 16) := state;
  let e : usize := (10 : usize);
  let st : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      e
      (fun st _ => (do (pure true) : RustM Bool))
      st
      (fun st _i => (do
        (Lean_chacha20.chacha20_double_round st) : RustM (RustArray u32 16))));
  (pure st)

def Lean_chacha20.chacha20_core
  (ctr : u32)
  (st0 : (RustArray u32 16))
  : RustM (RustArray u32 16)
  := do
  let state : (RustArray u32 16) := st0;
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (12 : usize)
      (← (Core.Num.Impl_8.wrapping_add (← state[(12 : usize)]_?) ctr)));
  let k : (RustArray u32 16) ← (Lean_chacha20.chacha20_rounds state);
  (Lean_chacha20.Hacspec_helper.add_state state k)

def Lean_chacha20.chacha20_init
  (key : (RustArray u8 32))
  (iv : (RustArray u8 12))
  (ctr : u32)
  : RustM (RustArray u32 16)
  := do
  let key_u32 : (RustArray u32 8) ←
    (Lean_chacha20.Hacspec_helper.to_le_u32s_8
      (← (Rust_primitives.unsize key)));
  let iv_u32 : (RustArray u32 3) ←
    (Lean_chacha20.Hacspec_helper.to_le_u32s_3 (← (Rust_primitives.unsize iv)));
  (pure #v[(1634760805 : u32),
             (857760878 : u32),
             (2036477234 : u32),
             (1797285236 : u32),
             (← key_u32[(0 : usize)]_?),
             (← key_u32[(1 : usize)]_?),
             (← key_u32[(2 : usize)]_?),
             (← key_u32[(3 : usize)]_?),
             (← key_u32[(4 : usize)]_?),
             (← key_u32[(5 : usize)]_?),
             (← key_u32[(6 : usize)]_?),
             (← key_u32[(7 : usize)]_?),
             ctr,
             (← iv_u32[(0 : usize)]_?),
             (← iv_u32[(1 : usize)]_?),
             (← iv_u32[(2 : usize)]_?)])

def Lean_chacha20.chacha20_key_block
  (state : (RustArray u32 16))
  : RustM (RustArray u8 64)
  := do
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_core (0 : u32) state);
  (Lean_chacha20.Hacspec_helper.u32s_to_le_bytes state)

def Lean_chacha20.chacha20_key_block0
  (key : (RustArray u8 32))
  (iv : (RustArray u8 12))
  : RustM (RustArray u8 64)
  := do
  let state : (RustArray u32 16) ←
    (Lean_chacha20.chacha20_init key iv (0 : u32));
  (Lean_chacha20.chacha20_key_block state)

def Lean_chacha20.chacha20_encrypt_block
  (st0 : (RustArray u32 16))
  (ctr : u32)
  (plain : (RustArray u8 64))
  : RustM (RustArray u8 64)
  := do
  let st : (RustArray u32 16) ← (Lean_chacha20.chacha20_core ctr st0);
  let pl : (RustArray u32 16) ←
    (Lean_chacha20.Hacspec_helper.to_le_u32s_16
      (← (Rust_primitives.unsize plain)));
  let encrypted : (RustArray u32 16) ←
    (Lean_chacha20.Hacspec_helper.xor_state st pl);
  (Lean_chacha20.Hacspec_helper.u32s_to_le_bytes encrypted)


@[spec]
theorem Lean_chacha20.chacha20_encrypt_block_spec (st0 : (Vector u32 16)) (ctr : u32) (plain : (Vector u8 64)) :
  ⦃ ⌜ True ⌝ ⦄
  ( Lean_chacha20.chacha20_encrypt_block st0 ctr plain)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄
  := by
  mvcgen [chacha20_encrypt_block,
          chacha20_core,
          chacha20_rounds,
          chacha20_double_round]
  <;> simp [Vector.size_toArray, Vector.size] at *
  <;> try omega

def Lean_chacha20.chacha20_encrypt_last
  (st0 : (RustArray u32 16))
  (ctr : u32)
  (plain : (RustSlice u8))
  : RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let b : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let b : (RustArray u8 64) ←
    (Lean_chacha20.Hacspec_helper.update_array b plain);
  let b : (RustArray u8 64) ← (Lean_chacha20.chacha20_encrypt_block st0 ctr b);
  (Alloc.Slice.Impl.to_vec u8
    (← b[
      (Core.Ops.Range.Range.mk
        (start := (0 : usize)) (_end := (← (Core.Slice.Impl.len u8 plain))))
      ]_?))


@[spec]
theorem Lean_chacha20.chacha20_encrypt_last_spec (st0 : (Vector u32 16)) (ctr : u32) (plain : Array u8) :
  plain.size ≤ 64 →
  ⦃ ⌜ True ⌝ ⦄
  ( Lean_chacha20.chacha20_encrypt_last st0 ctr plain)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄
:= by
  intros
  mvcgen [Lean_chacha20.chacha20_encrypt_last,
          Lean_chacha20.chacha20_key_block,
          Lean_chacha20.chacha20_init,
          Lean_chacha20.chacha20_core,
          Alloc.Slice.Impl.to_vec,]
  <;> grind

def Lean_chacha20.chacha20_update
  (st0 : (RustArray u32 16))
  (m : (RustSlice u8))
  : RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
  let num_blocks : usize ← ((← (Core.Slice.Impl.len u8 m)) /? (64 : usize));
  let remainder_len : usize ← ((← (Core.Slice.Impl.len u8 m)) %? (64 : usize));
  let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      num_blocks
      (fun blocks_out _ => (do (pure true) : RustM Bool))
      blocks_out
      (fun blocks_out i => (do
        let b : (RustArray u8 64) ←
          (Lean_chacha20.chacha20_encrypt_block
            st0
            (← (Rust_primitives.Hax.cast_op i))
            (← (Core.Result.Impl.unwrap
              (RustArray u8 64)
              Core.Array.TryFromSliceError
              (← (Core.Convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 64)
                (← m[
                  (Core.Ops.Range.Range.mk
                    (start := (← ((64 : usize) *? i)))
                    (_end := (← ((← ((64 : usize) *? i)) +? (64 : usize)))))
                  ]_?))))));
        let _ ←
          (Hax_lib.assume
            (← (Hax_lib.Prop.Constructors.from_bool
              (← (Rust_primitives.Hax.Machine_int.eq
                (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global blocks_out))
                (← (i *? (64 : usize))))))));
        let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
            blocks_out
            (← (Rust_primitives.unsize b)));
        (pure blocks_out) : RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let _ ←
    (Hax_lib.assume
      (← (Hax_lib.Prop.Constructors.from_bool
        (← (Rust_primitives.Hax.Machine_int.eq
          (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global blocks_out))
          (← (num_blocks *? (64 : usize))))))));
  let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    if (← (Rust_primitives.Hax.Machine_int.ne remainder_len (0 : usize))) then
      let b : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Lean_chacha20.chacha20_encrypt_last
          st0
          (← (Rust_primitives.Hax.cast_op num_blocks))
          (← m[
            (Core.Ops.Range.Range.mk
              (start := (← ((64 : usize) *? num_blocks)))
              (_end := (← (Core.Slice.Impl.len u8 m))))
            ]_?));
      let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
          blocks_out
          (← (Core.Ops.Deref.Deref.deref
            (Alloc.Vec.Vec u8 Alloc.Alloc.Global) b)));
      (pure blocks_out)
    else
      (pure blocks_out);
  (pure blocks_out)


set_option maxHeartbeats 1200000 in
@[spec]
theorem Lean_chacha20.chacha20_update_spec (st0 : (Vector u32 16)) (m : (Array u8)) :
  m.size < USize64.size →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.chacha20_update st0 m)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
by
  intros
  mvcgen [Lean_chacha20.chacha20_update,
      Alloc.Slice.Impl.to_vec,
      Core.Result.Impl.unwrap.spec,
      Alloc.Vec.Impl.new,
      Alloc.Vec.Impl_1.len,
      ]
    <;> simp_all [Nat.lt_div_iff_mul_lt]
    <;> grind

def Lean_chacha20.chacha20
  (m : (RustSlice u8))
  (key : (RustArray u8 32))
  (iv : (RustArray u8 12))
  (ctr : u32)
  : RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let state : (RustArray u32 16) ← (Lean_chacha20.chacha20_init key iv ctr);
  (Lean_chacha20.chacha20_update state m)


theorem Lean_chacha20.chacha20_spec
  (m : (Array u8)) (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32) :
  m.size < USize64.size →
  ⦃⌜True⌝⦄
  (Lean_chacha20.chacha20 m key iv ctr)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄
:= by intros ; mvcgen [Lean_chacha20.chacha20, chacha20_init] <;> simp at *