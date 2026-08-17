module Core_models.Iter.Sources.Successors
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Successors`]
type t_Successors (v_T: Type0) (v_F: Type0) = {
  f_next:Rust_primitives.Sequence.t_Seq v_T;
  f_succ:v_F
}

/// See [`std::iter::successors`]
let successors
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
      (first: Core_models.Option.t_Option v_T)
      (succ: v_F)
    : t_Successors v_T v_F =
  let next:Rust_primitives.Sequence.t_Seq v_T =
    match first <: Core_models.Option.t_Option v_T with
    | Core_models.Option.Option_Some v -> Rust_primitives.Sequence.seq_one #v_T v
    | Core_models.Option.Option_None  -> Rust_primitives.Sequence.seq_empty #v_T ()
  in
  { f_next = next; f_succ = succ } <: t_Successors v_T v_F

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_Successors v_T v_F) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Successors v_T v_F) -> true);
    f_next_post
    =
    (fun
        (self: t_Successors v_T v_F)
        (out1: (t_Successors v_T v_F & Core_models.Option.t_Option v_T))
        ->
        true);
    f_next
    =
    fun (self: t_Successors v_T v_F) ->
      let (self: t_Successors v_T v_F), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self.f_next <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Successors v_T v_F & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self.f_next (mk_usize 0)
          in
          let self:t_Successors v_T v_F = { self with f_next = tmp0 } <: t_Successors v_T v_F in
          let item:v_T = out in
          let self:t_Successors v_T v_F =
            match
              Core_models.Ops.Function.f_call #v_F
                #v_T
                #FStar.Tactics.Typeclasses.solve
                self.f_succ
                (item <: v_T)
              <:
              Core_models.Option.t_Option v_T
            with
            | Core_models.Option.Option_Some n ->
              { self with f_next = Rust_primitives.Sequence.seq_push #v_T self.f_next n }
              <:
              t_Successors v_T v_F
            | Core_models.Option.Option_None  -> self
          in
          self, (Core_models.Option.Option_Some item <: Core_models.Option.t_Option v_T)
          <:
          (t_Successors v_T v_F & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Successors v_T v_F & Core_models.Option.t_Option v_T)
  }
