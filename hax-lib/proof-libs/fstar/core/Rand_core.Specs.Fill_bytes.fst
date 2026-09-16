module Rand_core.Specs.Fill_bytes

/// The `RngCore` contract in usable form. Its implementations are external, so
/// the trait's `requires`/`ensures` is the specification; hax puts it on the
/// class fields as refinements, which typeclass projection hides from Z3. The
/// SMTPats hand it back to call sites.

open FStar.Mul
open Rust_primitives

let next_u32_pre (#v_Self: Type0) (#i0: Rand_core.t_RngCore v_Self) (self_: v_Self)
    : Lemma (i0.f_next_u32_pre self_)
      [SMTPat (i0.f_next_u32_pre self_)]
  = ()

let next_u64_pre (#v_Self: Type0) (#i0: Rand_core.t_RngCore v_Self) (self_: v_Self)
    : Lemma (i0.f_next_u64_pre self_)
      [SMTPat (i0.f_next_u64_pre self_)]
  = ()

let fill_bytes_pre (#v_Self: Type0) (#i0: Rand_core.t_RngCore v_Self)
      (self_: v_Self) (dst: t_Slice u8)
    : Lemma (i0.f_fill_bytes_pre self_ dst)
      [SMTPat (i0.f_fill_bytes_pre self_ dst)]
  = ()

/// `fill_bytes` fills `dst` in place, so the output slice has the input's length.
let fill_bytes_post_len (#v_Self: Type0) (#i0: Rand_core.t_RngCore v_Self)
      (self_: v_Self) (dst: t_Slice u8) (result: v_Self & t_Slice u8)
    : Lemma (requires i0.f_fill_bytes_post self_ dst result)
      (ensures
        Core_models.Slice.impl__len #u8 (snd result) == Core_models.Slice.impl__len #u8 dst /\
        Seq.length (snd result) == Seq.length dst)
      [SMTPat (i0.f_fill_bytes_post self_ dst result)]
  = ()
