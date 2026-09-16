module Rand_core.Specs.Fill_bytes

/// Usable form of the `RngCore` trait contract.
///
/// The implementations are external — there is no randomness to model — so the
/// trait's `requires`/`ensures` IS the specification, and what a consumer needs
/// is to be able to *use* it. hax puts both on the class fields as refinements
/// (`pred: Type0{true ==> pred}` for a `requires true`, and
/// `pred: Type0{pred ==> …}` for an `ensures`), which typeclass projection at a
/// call site otherwise hides from Z3.
///
/// Every lemma here discharges from those refinements and carries an SMTPat, so
/// call sites get the contract for free instead of assuming it.

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
