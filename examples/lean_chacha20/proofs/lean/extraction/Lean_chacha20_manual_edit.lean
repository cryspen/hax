
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
  : Result (RustArray u32 3)
  := do
  let out : (RustArray u32 3) ← (pure
    (← Rust_primitives.Hax.repeat (0 : u32) 3));
  let out : (RustArray u32 3) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (3 : usize)
        (fun out _ => (do true : Result Bool))
        out
        (fun out i => (do
            (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                out
                i
                (← Core.Num.Impl_8.from_le_bytes
                    (← Core.Result.Impl.unwrap
                        (RustArray u8 4)
                        Core.Array.TryFromSliceError
                        (← Core.Convert.TryInto.try_into
                            (← bytes[
                              (Core.Ops.Range.Range.mk
                                (start := (← (4 : usize) *? i))
                                (_end := (← (← (4 : usize) *? i)
                                  +? (4 : usize))))
                              ]_?))))) : Result (RustArray u32 3)))));
  out

def Lean_chacha20.Hacspec_helper.to_le_u32s_8
  (bytes : (RustSlice u8))
  : Result (RustArray u32 8)
  := do
  let out : (RustArray u32 8) ← (pure
    (← Rust_primitives.Hax.repeat (0 : u32) 8));
  let out : (RustArray u32 8) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (8 : usize)
        (fun out _ => (do true : Result Bool))
        out
        (fun out i => (do
            (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                out
                i
                (← Core.Num.Impl_8.from_le_bytes
                    (← Core.Result.Impl.unwrap
                        (RustArray u8 4)
                        Core.Array.TryFromSliceError
                        (← Core.Convert.TryInto.try_into
                            (← bytes[
                              (Core.Ops.Range.Range.mk
                                (start := (← (4 : usize) *? i))
                                (_end := (← (← (4 : usize) *? i)
                                  +? (4 : usize))))
                              ]_?))))) : Result (RustArray u32 8)))));
  out

def Lean_chacha20.Hacspec_helper.to_le_u32s_16
  (bytes : (RustSlice u8))
  : Result (RustArray u32 16)
  := do
  let out : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.repeat (0 : u32) 16));
  let out : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (16 : usize)
        (fun out _ => (do true : Result Bool))
        out
        (fun out i => (do
            (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                out
                i
                (← Core.Num.Impl_8.from_le_bytes
                    (← Core.Result.Impl.unwrap
                        (RustArray u8 4)
                        Core.Array.TryFromSliceError
                        (← Core.Convert.TryInto.try_into
                            (← bytes[
                              (Core.Ops.Range.Range.mk
                                (start := (← (4 : usize) *? i))
                                (_end := (← (← (4 : usize) *? i)
                                  +? (4 : usize))))
                              ]_?))))) : Result (RustArray u32 16)))));
  out

def Lean_chacha20.Hacspec_helper.u32s_to_le_bytes
  (state : (RustArray u32 16))
  : Result (RustArray u8 64)
  := do
  let out : (RustArray u8 64) ← (pure
    (← Rust_primitives.Hax.repeat (0 : u8) 64));
  let out : (RustArray u8 64) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (← Core.Slice.Impl.len u32 (← Rust_primitives.unsize state))
        (fun out _ => (do true : Result Bool))
        out
        (fun out i => (do
            let tmp : (RustArray u8 4) ← (pure
              (← Core.Num.Impl_8.to_le_bytes (← state[i]_?)));
            (← Rust_primitives.Hax.Folds.fold_range
                (0 : usize)
                (4 : usize)
                (fun out _ => (do true : Result Bool))
                out
                (fun out j => (do
                    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                        out
                        (← (← i *? (4 : usize)) +? j)
                        (← tmp[j]_?)) : Result (RustArray u8 64)))) : Result
            (RustArray u8 64)))));
  out

def Lean_chacha20.Hacspec_helper.xor_state
  (state : (RustArray u32 16))
  (other : (RustArray u32 16))
  : Result (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (16 : usize)
        (fun state _ => (do true : Result Bool))
        state
        (fun state i => (do
            (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                state
                i
                (← (← state[i]_?) ^^^? (← other[i]_?))) : Result
            (RustArray u32 16)))));
  state

def Lean_chacha20.Hacspec_helper.add_state
  (state : (RustArray u32 16))
  (other : (RustArray u32 16))
  : Result (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (16 : usize)
        (fun state _ => (do true : Result Bool))
        state
        (fun state i => (do
            (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                state
                i
                (← Core.Num.Impl_8.wrapping_add (← state[i]_?) (← other[i]_?)))
            : Result (RustArray u32 16)))));
  state

def Lean_chacha20.Hacspec_helper.update_array
  (array : (RustArray u8 64))
  (val : (RustSlice u8))
  : Result (RustArray u8 64)
  := do
  let _ ← (pure
    (← Hax_lib.assert
        (← Rust_primitives.Hax.Machine_int.ge
            (64 : usize)
            (← Core.Slice.Impl.len u8 val))));
  let array : (RustArray u8 64) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (← Core.Slice.Impl.len u8 val)
        (fun array _ => (do true : Result Bool))
        array
        (fun array i => (do
            (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                array
                i
                (← val[i]_?)) : Result (RustArray u8 64)))));
  array

abbrev Lean_chacha20.State := (RustArray u32 16)

abbrev Lean_chacha20.Block := (RustArray u8 64)

abbrev Lean_chacha20.ChaChaIV := (RustArray u8 12)

abbrev Lean_chacha20.ChaChaKey := (RustArray u8 32)

abbrev Lean_chacha20.StateIdx :=
(Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
  (0 : usize)
  (15 : usize))

def Lean_chacha20.chacha20_line
  (a :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    (0 : usize)
    (15 : usize)))
  (b :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    (0 : usize)
    (15 : usize)))
  (d :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    (0 : usize)
    (15 : usize)))
  (s : u32)
  (m : (RustArray u32 16))
  : Result (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ← (pure m);
  let state : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.update_at
        state
        a
        (← Core.Num.Impl_8.wrapping_add (← state[a]_?) (← state[b]_?))));
  let state : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.update_at
        state
        d
        (← (← state[d]_?) ^^^? (← state[a]_?))));
  let state : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.update_at
        state
        d
        (← Core.Num.Impl_8.rotate_left (← state[d]_?) s)));
  state

def Lean_chacha20.chacha20_quarter_round
  (a :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    (0 : usize)
    (15 : usize)))
  (b :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    (0 : usize)
    (15 : usize)))
  (c :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    (0 : usize)
    (15 : usize)))
  (d :
  (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
    (0 : usize)
    (15 : usize)))
  (state : (RustArray u32 16))
  : Result (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_line a b d (16 : u32) state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_line c d b (12 : u32) state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_line a b d (8 : u32) state));
  (← Lean_chacha20.chacha20_line c d b (7 : u32) state)

def Lean_chacha20.chacha20_double_round
  (state : (RustArray u32 16))
  : Result (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_quarter_round
        ((0 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((4 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((8 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((12 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_quarter_round
        ((1 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((5 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((9 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((13 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_quarter_round
        ((2 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((6 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((10 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((14 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_quarter_round
        ((3 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((7 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((11 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((15 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_quarter_round
        ((0 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((5 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((10 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((15 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_quarter_round
        ((1 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((6 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((11 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((12 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        state));
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_quarter_round
        ((2 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((7 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((8 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        ((13 : usize) :
        (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
          (0 : usize)
          (15 : usize)))
        state));
  (← Lean_chacha20.chacha20_quarter_round
      ((3 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        (0 : usize)
        (15 : usize)))
      ((4 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        (0 : usize)
        (15 : usize)))
      ((9 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        (0 : usize)
        (15 : usize)))
      ((14 : usize) :
      (Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
        (0 : usize)
        (15 : usize)))
      state)

def Lean_chacha20.chacha20_rounds
  (state : (RustArray u32 16))
  : Result (RustArray u32 16)
  := do
  let st : (RustArray u32 16) ← (pure state);
  let st : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (10 : usize)
        (fun st _ => (do true : Result Bool))
        st
        (fun st _i => (do
            (← Lean_chacha20.chacha20_double_round st) : Result
            (RustArray u32 16)))));
  st

def Lean_chacha20.chacha20_core
  (ctr : u32)
  (st0 : (RustArray u32 16))
  : Result (RustArray u32 16)
  := do
  let state : (RustArray u32 16) ← (pure st0);
  let state : (RustArray u32 16) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        state
        (12 : usize)
        (← Core.Num.Impl_8.wrapping_add (← state[(12 : usize)]_?) ctr)));
  let k : (RustArray u32 16) ← (pure (← Lean_chacha20.chacha20_rounds state));
  (← Lean_chacha20.Hacspec_helper.add_state state k)

def Lean_chacha20.chacha20_init
  (key : (RustArray u8 32))
  (iv : (RustArray u8 12))
  (ctr : u32)
  : Result (RustArray u32 16)
  := do
  let key_u32 ← (pure
    (← Lean_chacha20.Hacspec_helper.to_le_u32s_8
        (← Rust_primitives.unsize key)));
  let iv_u32 ← (pure
    (← Lean_chacha20.Hacspec_helper.to_le_u32s_3
        (← Rust_primitives.unsize iv)));
  #v[(1634760805 : u32),
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
       (← iv_u32[(2 : usize)]_?)]

def Lean_chacha20.chacha20_key_block
  (state : (RustArray u32 16))
  : Result (RustArray u8 64)
  := do
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_core (0 : u32) state));
  (← Lean_chacha20.Hacspec_helper.u32s_to_le_bytes state)

def Lean_chacha20.chacha20_key_block0
  (key : (RustArray u8 32))
  (iv : (RustArray u8 12))
  : Result (RustArray u8 64)
  := do
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_init key iv (0 : u32)));
  (← Lean_chacha20.chacha20_key_block state)

def Lean_chacha20.chacha20_encrypt_block
  (st0 : (RustArray u32 16))
  (ctr : u32)
  (plain : (RustArray u8 64))
  : Result (RustArray u8 64)
  := do
  let st : (RustArray u32 16) ← (pure (← Lean_chacha20.chacha20_core ctr st0));
  let pl ← (pure
    (← Lean_chacha20.Hacspec_helper.to_le_u32s_16
        (← Rust_primitives.unsize plain)));
  let encrypted : (RustArray u32 16) ← (pure
    (← Lean_chacha20.Hacspec_helper.xor_state st pl));
  (← Lean_chacha20.Hacspec_helper.u32s_to_le_bytes encrypted)

def Lean_chacha20._.requires
  (st0 : (RustArray u32 16))
  (ctr : u32)
  (plain : (RustSlice u8))
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.le
      (← Core.Slice.Impl.len u8 plain)
      (64 : usize))

def Lean_chacha20.chacha20_encrypt_last
  (st0 : (RustArray u32 16))
  (ctr : u32)
  (plain : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let b ← (pure (← Rust_primitives.Hax.repeat (0 : u8) 64));
  let b : (RustArray u8 64) ← (pure
    (← Lean_chacha20.Hacspec_helper.update_array b plain));
  let b : (RustArray u8 64) ← (pure
    (← Lean_chacha20.chacha20_encrypt_block st0 ctr b));
  (← Alloc.Slice.Impl.to_vec u8
      (← b[
        (Core.Ops.Range.Range.mk
          (start := (0 : usize)) (_end := (← Core.Slice.Impl.len u8 plain)))
        ]_?))

def Lean_chacha20.chacha20_update
  (st0 : (RustArray u32 16))
  (m : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk));
  let num_blocks : usize ← (pure
    (← (← Core.Slice.Impl.len u8 m) /? (64 : usize)));
  let remainder_len : usize ← (pure
    (← (← Core.Slice.Impl.len u8 m) %? (64 : usize)));
  let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        num_blocks
        (fun blocks_out _ => (do true : Result Bool))
        blocks_out
        (fun blocks_out i => (do
            let b : (RustArray u8 64) ← (pure
              (← Lean_chacha20.chacha20_encrypt_block
                  st0
                  (← Rust_primitives.Hax.cast_op i)
                  (← Core.Result.Impl.unwrap
                      (RustArray u8 64)
                      Core.Array.TryFromSliceError
                      (← Core.Convert.TryInto.try_into
                          (← m[
                            (Core.Ops.Range.Range.mk
                              (start := (← (64 : usize) *? i))
                              (_end := (← (← (64 : usize) *? i)
                                +? (64 : usize))))
                            ]_?)))));
            let _ ← (pure
              (← Hax_lib.assume
                  (← Hax_lib.Prop.Constructors.from_bool
                      (← Rust_primitives.Hax.Machine_int.eq
                          (← Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global
                              blocks_out)
                          (← i *? (64 : usize))))));
            let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
              (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
                  blocks_out
                  (← Rust_primitives.unsize b)));
            blocks_out : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let _ ← (pure
    (← Hax_lib.assume
        (← Hax_lib.Prop.Constructors.from_bool
            (← Rust_primitives.Hax.Machine_int.eq
                (← Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global blocks_out)
                (← num_blocks *? (64 : usize))))));
  let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← if
    (← Rust_primitives.Hax.Machine_int.ne remainder_len (0 : usize)) then do
      let b : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
        (← Lean_chacha20.chacha20_encrypt_last
            st0
            (← Rust_primitives.Hax.cast_op num_blocks)
            (← m[
              (Core.Ops.Range.Range.mk
                (start := (← (64 : usize) *? num_blocks))
                (_end := (← Core.Slice.Impl.len u8 m)))
              ]_?)));
      let blocks_out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
        (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
            blocks_out
            (← Core.Ops.Deref.Deref.deref b)));
      blocks_out
    else do
      blocks_out));
  blocks_out

def Lean_chacha20.chacha20
  (m : (RustSlice u8))
  (key : (RustArray u8 32))
  (iv : (RustArray u8 12))
  (ctr : u32)
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let state : (RustArray u32 16) ← (pure
    (← Lean_chacha20.chacha20_init key iv ctr));
  (← Lean_chacha20.chacha20_update state m)

-- Theorems

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

@[spec]
theorem Lean_chacha20.Hacspec_helper.to_le_u32s_16_spec bytes :
  bytes.size = 64 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.to_le_u32s_16 bytes)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intro
  have := USize.le_size
  open Spec.Nat in
    mvcgen [Lean_chacha20.Hacspec_helper.to_le_u32s_16]
    <;> subst_eqs
    <;> simp [Vector.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le] at *
    <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try rw [h_size])
    <;> (try omega)
  done

@[spec]
theorem Lean_chacha20.Hacspec_helper.to_le_u32s_3_spec bytes :
  bytes.size = 12 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.to_le_u32s_3 bytes)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  open Spec.Nat in
    mvcgen [Lean_chacha20.Hacspec_helper.to_le_u32s_3]
    <;> subst_eqs
    <;> simp [Vector.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le] at *
    <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try rw [h_size])
    <;> (try omega)
  done

@[spec]
theorem Lean_chacha20.Hacspec_helper.to_le_u32s_8_spec (bytes : (Array u8)) :
  bytes.size = 32 →
  ⦃ ⌜ True ⌝ ⦄
  ( Lean_chacha20.Hacspec_helper.to_le_u32s_8 bytes )
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  open Spec.Nat in
    mvcgen [Lean_chacha20.Hacspec_helper.to_le_u32s_8]
    <;> subst_eqs
    <;> simp [Vector.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le] at *
    <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try rw [h_size])
    <;> (try omega)
  done

@[spec]
theorem Lean_chacha20.Hacspec_helper.u32s_to_le_bytes_spec (state : (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.u32s_to_le_bytes state)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  open Spec.Nat in
    mvcgen [Lean_chacha20.Hacspec_helper.u32s_to_le_bytes, Core.Num.Impl_8.to_le_bytes]
    <;> subst_eqs
    <;> simp [Vector.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le] at *
    <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try simp_all)
    <;> (try omega)
  done

@[spec]
theorem Lean_chacha20.Hacspec_helper.xor_state_spec (state other: (Vector u32 16)) :
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.xor_state state other)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  open Spec.Nat in
    mvcgen [Lean_chacha20.Hacspec_helper.xor_state, Core.Num.Impl_8.to_le_bytes]
    <;> subst_eqs
    <;> simp [Vector.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le] at *
    <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try simp_all)
    <;> (try omega)
  done

@[spec]
theorem Lean_chacha20.Hacspec_helper.update_array_spec (a: (Vector u8 64)) (v: Array u8) :
  v.size ≤ 64 →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.Hacspec_helper.update_array a v)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intros
  open Spec.Nat in
    mvcgen [Lean_chacha20.Hacspec_helper.update_array, Hax_lib.assert]
    <;> subst_eqs
    <;> simp [Vector.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le] at *
    <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try simp_all)
    <;> (try omega)
  done

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
          Rust_primitives.Hax.Machine_int.bitxor,
          Result.ofOption, ]
  <;> try omega

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
  <;> simp [Vector.size_toArray, Vector.size, USize.le_iff_toNat_le] at *
  <;> try omega


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
  <;> simp [Vector.size, USize.le_iff_toNat_le] at *
  <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try simp_all)
  <;> (try omega)


@[simp]
theorem System.Platform.numBits_ne_zero : ¬ System.Platform.numBits = 0 :=
by cases (System.Platform.numBits_eq) <;> grind

@[spec]
theorem Lean_chacha20.chacha20_update_spec (st0 : (Vector u32 16)) (m : (Array u8)) :
  m.size ≤ USize.size →
  ⦃ ⌜ True ⌝ ⦄
  (Lean_chacha20.chacha20_update st0 m)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
by
  intros
  open Spec.BV in
    mvcgen [Lean_chacha20.chacha20_update,
      Alloc.Slice.Impl.to_vec,
      Core.Result.Impl.unwrap.spec,
      Alloc.Vec.Impl.new,
      Alloc.Vec.Impl_1.len,
      ]
  <;> subst_vars
  <;> simp [
      USize.size,
      USize.eq_iff_toBitVec_eq,
      ] at *
  <;> (try omega)
  <;> (try (intro h ; injections ; simp_all ; done))
  <;> (rcases System.Platform.numBits_eq with h_size | h_size <;> try rw [h_size])
  <;> (try bv_decide)
  <;> try (simp [USize.lt_iff_toNat_lt, h_size ] at * <;> omega )


theorem Lean_chacha20.chacha20_spec
  (m : (Array u8)) (key : (Vector u8 32)) (iv : (Vector u8 12)) (ctr : u32) :
  m.size ≤ USize.size →
  ⦃⌜True⌝⦄
  (Lean_chacha20.chacha20 m key iv ctr)
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄
:= by intros ; mvcgen [Lean_chacha20.chacha20, chacha20_init] <;> simp at *
