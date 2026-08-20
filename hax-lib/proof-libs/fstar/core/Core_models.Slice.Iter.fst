module Core_models.Slice.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// Index of the first element of `s` satisfying `pred`, or `s.len()` if
/// there is none. A bounded loop with no early exit, which is the shape both
/// backends handle; `pred` is taken by reference so the split iterators can
/// call it out of `&mut self`.
assume
val position_of':
    #v_T: Type0 ->
    #v_P: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_P v_T |} ->
    s: t_Slice v_T ->
    pred: v_P
  -> Prims.Pure usize
      Prims.l_True
      (ensures
        fun res ->
          let res:usize = res in
          res <=. (Rust_primitives.Slice.slice_length #v_T s <: usize))

unfold
let position_of
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
     = position_of' #v_T #v_P #i0

/// Index of the *last* element of `s` satisfying `pred`, or `s.len()` if
/// there is none.
assume
val rposition_of':
    #v_T: Type0 ->
    #v_P: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_P v_T |} ->
    s: t_Slice v_T ->
    pred: v_P
  -> Prims.Pure usize
      Prims.l_True
      (ensures
        fun res ->
          let res:usize = res in
          res <=. (Rust_primitives.Slice.slice_length #v_T s <: usize))

unfold
let rposition_of
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
     = rposition_of' #v_T #v_P #i0

/// See [`std::slice::Chunks`]
type t_Chunks (v_T: Type0) = {
  f_cs:usize;
  f_elements:t_Slice v_T
}

let impl__new (#v_T: Type0) (cs: usize) (elements: t_Slice v_T) : t_Chunks v_T =
  { f_cs = cs; f_elements = elements } <: t_Chunks v_T

/// See [`std::slice::ChunksExact`]
type t_ChunksExact (v_T: Type0) = {
  f_cs:usize;
  f_elements:t_Slice v_T;
  f_rem:t_Slice v_T
}

let impl_1__new (#v_T: Type0) (cs: usize) (elements: t_Slice v_T) : t_ChunksExact v_T =
  let len:usize = Rust_primitives.Slice.slice_length #v_T elements in
  let rem_len:usize = if cs =. mk_usize 0 then mk_usize 0 else len %! cs in
  let rem:t_Slice v_T =
    Rust_primitives.Slice.slice_slice #v_T elements (len -! rem_len <: usize) len
  in
  { f_cs = cs; f_elements = elements; f_rem = rem } <: t_ChunksExact v_T

/// See [`std::slice::ChunksExact::remainder`]
let impl_1__remainder (#v_T: Type0) (self: t_ChunksExact v_T) : t_Slice v_T = self.f_rem

/// See [`std::slice::Iter`]
type t_Iter (v_T: Type0) = | Iter : Rust_primitives.Sequence.t_Seq v_T -> t_Iter v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Iter v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Iter v_T) -> true);
    f_next_post
    =
    (fun (self: t_Iter v_T) (out1: (t_Iter v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Iter v_T) ->
      let (self: t_Iter v_T), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Iter v_T & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Iter v_T = { self with _0 = tmp0 } <: t_Iter v_T in
          let res:v_T = out in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option v_T)
          <:
          (t_Iter v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Iter v_T & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Chunks v_T) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_Chunks v_T) -> true);
    f_next_post
    =
    (fun (self: t_Chunks v_T) (out: (t_Chunks v_T & Core_models.Option.t_Option (t_Slice v_T))) ->
        true);
    f_next
    =
    fun (self: t_Chunks v_T) ->
      let (self: t_Chunks v_T), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
        if (Rust_primitives.Slice.slice_length #v_T self.f_elements <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_Chunks v_T & Core_models.Option.t_Option (t_Slice v_T))
        else
          if (Rust_primitives.Slice.slice_length #v_T self.f_elements <: usize) <. self.f_cs
          then
            let res:t_Slice v_T = self.f_elements in
            let self:t_Chunks v_T =
              {
                self with
                f_elements
                =
                Rust_primitives.Slice.slice_slice #v_T self.f_elements (mk_usize 0) (mk_usize 0)
              }
              <:
              t_Chunks v_T
            in
            self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
            <:
            (t_Chunks v_T & Core_models.Option.t_Option (t_Slice v_T))
          else
            let (res: t_Slice v_T), (new_elements: t_Slice v_T) =
              Rust_primitives.Slice.slice_split_at #v_T self.f_elements self.f_cs
            in
            let self:t_Chunks v_T = { self with f_elements = new_elements } <: t_Chunks v_T in
            self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
            <:
            (t_Chunks v_T & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output <: (t_Chunks v_T & Core_models.Option.t_Option (t_Slice v_T))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_ChunksExact v_T) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_ChunksExact v_T) -> true);
    f_next_post
    =
    (fun
        (self: t_ChunksExact v_T)
        (out: (t_ChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T)))
        ->
        true);
    f_next
    =
    fun (self: t_ChunksExact v_T) ->
      let (self: t_ChunksExact v_T), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
        if (Rust_primitives.Slice.slice_length #v_T self.f_elements <: usize) <. self.f_cs
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_ChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T))
        else
          let (res: t_Slice v_T), (new_elements: t_Slice v_T) =
            Rust_primitives.Slice.slice_split_at #v_T self.f_elements self.f_cs
          in
          let self:t_ChunksExact v_T =
            { self with f_elements = new_elements } <: t_ChunksExact v_T
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_ChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output <: (t_ChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::Windows`]
type t_Windows (v_T: Type0) = {
  f_size:usize;
  f_elements:t_Slice v_T
}

let impl_5__new (#v_T: Type0) (size: usize) (elements: t_Slice v_T) : t_Windows v_T =
  { f_size = size; f_elements = elements } <: t_Windows v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': #v_T: Type0 -> Core_models.Iter.Traits.Iterator.t_Iterator (t_Windows v_T)

unfold
let impl_6 (#v_T: Type0) = impl_6' #v_T

/// See [`std::slice::RChunks`]
type t_RChunks (v_T: Type0) = {
  f_cs:usize;
  f_elements:t_Slice v_T
}

let impl_7__new (#v_T: Type0) (cs: usize) (elements: t_Slice v_T) : t_RChunks v_T =
  { f_cs = cs; f_elements = elements } <: t_RChunks v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_RChunks v_T) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_RChunks v_T) -> true);
    f_next_post
    =
    (fun (self: t_RChunks v_T) (out: (t_RChunks v_T & Core_models.Option.t_Option (t_Slice v_T))) ->
        true);
    f_next
    =
    fun (self: t_RChunks v_T) ->
      let len:usize = Rust_primitives.Slice.slice_length #v_T self.f_elements in
      let (self: t_RChunks v_T), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
        if len =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_RChunks v_T & Core_models.Option.t_Option (t_Slice v_T))
        else
          if len <. self.f_cs
          then
            let res:t_Slice v_T = self.f_elements in
            let self:t_RChunks v_T =
              {
                self with
                f_elements
                =
                Rust_primitives.Slice.slice_slice #v_T self.f_elements (mk_usize 0) (mk_usize 0)
              }
              <:
              t_RChunks v_T
            in
            self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
            <:
            (t_RChunks v_T & Core_models.Option.t_Option (t_Slice v_T))
          else
            let (rest: t_Slice v_T), (res: t_Slice v_T) =
              Rust_primitives.Slice.slice_split_at #v_T self.f_elements (len -! self.f_cs <: usize)
            in
            let self:t_RChunks v_T = { self with f_elements = rest } <: t_RChunks v_T in
            self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
            <:
            (t_RChunks v_T & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output <: (t_RChunks v_T & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::RChunksExact`]
type t_RChunksExact (v_T: Type0) = {
  f_cs:usize;
  f_elements:t_Slice v_T;
  f_rem:t_Slice v_T
}

let impl_9__new (#v_T: Type0) (cs: usize) (elements: t_Slice v_T) : t_RChunksExact v_T =
  let rem_len:usize =
    if cs =. mk_usize 0
    then mk_usize 0
    else (Rust_primitives.Slice.slice_length #v_T elements <: usize) %! cs
  in
  let (rem: t_Slice v_T), (els: t_Slice v_T) =
    Rust_primitives.Slice.slice_split_at #v_T elements rem_len
  in
  { f_cs = cs; f_elements = els; f_rem = rem } <: t_RChunksExact v_T

/// See [`std::slice::RChunksExact::remainder`]
let impl_9__remainder (#v_T: Type0) (self: t_RChunksExact v_T) : t_Slice v_T = self.f_rem

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_RChunksExact v_T) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_RChunksExact v_T) -> true);
    f_next_post
    =
    (fun
        (self: t_RChunksExact v_T)
        (out: (t_RChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T)))
        ->
        true);
    f_next
    =
    fun (self: t_RChunksExact v_T) ->
      let len:usize = Rust_primitives.Slice.slice_length #v_T self.f_elements in
      let (self: t_RChunksExact v_T), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
        if len <. self.f_cs
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_RChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T))
        else
          let (rest: t_Slice v_T), (res: t_Slice v_T) =
            Rust_primitives.Slice.slice_split_at #v_T self.f_elements (len -! self.f_cs <: usize)
          in
          let self:t_RChunksExact v_T = { self with f_elements = rest } <: t_RChunksExact v_T in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_RChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output <: (t_RChunksExact v_T & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::Split`]
type t_Split (v_T: Type0) (v_P: Type0) = {
  f_v:t_Slice v_T;
  f_pred:v_P;
  f_finished:bool
}

let impl_11__new
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (v: t_Slice v_T)
      (pred: v_P)
    : t_Split v_T v_P = { f_v = v; f_pred = pred; f_finished = false } <: t_Split v_T v_P

/// See [`std::slice::Split::as_slice`]
let impl_11__as_slice
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (self: t_Split v_T v_P)
    : t_Slice v_T =
  if self.f_finished
  then Rust_primitives.Slice.slice_slice #v_T self.f_v (mk_usize 0) (mk_usize 0)
  else self.f_v

/// Yields the whole remaining slice and stops: what `splitn` does once
/// its split budget is used up.
let impl_11__finish
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (self: t_Split v_T v_P)
    : (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T)) =
  let (self: t_Split v_T v_P), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
    if self.f_finished
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
      <:
      (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
    else
      let self:t_Split v_T v_P = { self with f_finished = true } <: t_Split v_T v_P in
      self, (Core_models.Option.Option_Some self.f_v <: Core_models.Option.t_Option (t_Slice v_T))
      <:
      (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
  in
  self, hax_temp_output <: (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))

/// The `DoubleEndedIterator` half of `Split`, which is all `RSplit` is.
let impl_11__next_back
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (self: t_Split v_T v_P)
    : (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T)) =
  let (self: t_Split v_T v_P), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
    if self.f_finished
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
      <:
      (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
    else
      let len:usize = Rust_primitives.Slice.slice_length #v_T self.f_v in
      let idx:usize = rposition_of #v_T #v_P self.f_v self.f_pred in
      if idx =. len
      then
        let self:t_Split v_T v_P = { self with f_finished = true } <: t_Split v_T v_P in
        self, (Core_models.Option.Option_Some self.f_v <: Core_models.Option.t_Option (t_Slice v_T))
        <:
        (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
      else
        let res:t_Slice v_T =
          Rust_primitives.Slice.slice_slice #v_T self.f_v (idx +! mk_usize 1 <: usize) len
        in
        let self:t_Split v_T v_P =
          { self with f_v = Rust_primitives.Slice.slice_slice #v_T self.f_v (mk_usize 0) idx }
          <:
          t_Split v_T v_P
        in
        self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
        <:
        (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
  in
  self, hax_temp_output <: (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_Split v_T v_P) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_Split v_T v_P) -> true);
    f_next_post
    =
    (fun
        (self: t_Split v_T v_P)
        (out: (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T)))
        ->
        true);
    f_next
    =
    fun (self: t_Split v_T v_P) ->
      let (self: t_Split v_T v_P), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
        if self.f_finished
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
        else
          let len:usize = Rust_primitives.Slice.slice_length #v_T self.f_v in
          let idx:usize = position_of #v_T #v_P self.f_v self.f_pred in
          if idx =. len
          then
            let self:t_Split v_T v_P = { self with f_finished = true } <: t_Split v_T v_P in
            self,
            (Core_models.Option.Option_Some self.f_v <: Core_models.Option.t_Option (t_Slice v_T))
            <:
            (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
          else
            let res:t_Slice v_T =
              Rust_primitives.Slice.slice_slice #v_T self.f_v (mk_usize 0) idx
            in
            let self:t_Split v_T v_P =
              {
                self with
                f_v
                =
                Rust_primitives.Slice.slice_slice #v_T self.f_v (idx +! mk_usize 1 <: usize) len
              }
              <:
              t_Split v_T v_P
            in
            self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
            <:
            (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output <: (t_Split v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::SplitInclusive`]
type t_SplitInclusive (v_T: Type0) (v_P: Type0) = {
  f_v:t_Slice v_T;
  f_pred:v_P;
  f_finished:bool
}

let impl_13__new
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (v: t_Slice v_T)
      (pred: v_P)
    : t_SplitInclusive v_T v_P =
  let finished:bool = (Rust_primitives.Slice.slice_length #v_T v <: usize) =. mk_usize 0 in
  { f_v = v; f_pred = pred; f_finished = finished } <: t_SplitInclusive v_T v_P

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_SplitInclusive v_T v_P) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_SplitInclusive v_T v_P) -> true);
    f_next_post
    =
    (fun
        (self: t_SplitInclusive v_T v_P)
        (out: (t_SplitInclusive v_T v_P & Core_models.Option.t_Option (t_Slice v_T)))
        ->
        true);
    f_next
    =
    fun (self: t_SplitInclusive v_T v_P) ->
      let
      (self: t_SplitInclusive v_T v_P), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T))
      =
        if self.f_finished
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_SplitInclusive v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
        else
          let len:usize = Rust_primitives.Slice.slice_length #v_T self.f_v in
          let p:usize = position_of #v_T #v_P self.f_v self.f_pred in
          let idx:usize = if p =. len then len else p +! mk_usize 1 in
          let self:t_SplitInclusive v_T v_P =
            if idx =. len
            then
              let self:t_SplitInclusive v_T v_P =
                { self with f_finished = true } <: t_SplitInclusive v_T v_P
              in
              self
            else self
          in
          let res:t_Slice v_T = Rust_primitives.Slice.slice_slice #v_T self.f_v (mk_usize 0) idx in
          let self:t_SplitInclusive v_T v_P =
            { self with f_v = Rust_primitives.Slice.slice_slice #v_T self.f_v idx len }
            <:
            t_SplitInclusive v_T v_P
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_SplitInclusive v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output
      <:
      (t_SplitInclusive v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::SplitN`]
type t_SplitN (v_T: Type0) (v_P: Type0) = {
  f_inner:t_Split v_T v_P;
  f_count:usize
}

let impl_15__new
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (v: t_Slice v_T)
      (n: usize)
      (pred: v_P)
    : t_SplitN v_T v_P =
  { f_inner = impl_11__new #v_T #v_P v pred; f_count = n } <: t_SplitN v_T v_P

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_SplitN v_T v_P) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_SplitN v_T v_P) -> true);
    f_next_post
    =
    (fun
        (self: t_SplitN v_T v_P)
        (out1: (t_SplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T)))
        ->
        true);
    f_next
    =
    fun (self: t_SplitN v_T v_P) ->
      let (self: t_SplitN v_T v_P), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
        if self.f_count =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_SplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
        else
          if self.f_count =. mk_usize 1
          then
            let self:t_SplitN v_T v_P = { self with f_count = mk_usize 0 } <: t_SplitN v_T v_P in
            let (tmp0: t_Split v_T v_P), (out: Core_models.Option.t_Option (t_Slice v_T)) =
              impl_11__finish #v_T #v_P self.f_inner
            in
            let self:t_SplitN v_T v_P = { self with f_inner = tmp0 } <: t_SplitN v_T v_P in
            self, out <: (t_SplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
          else
            let self:t_SplitN v_T v_P =
              { self with f_count = self.f_count -! mk_usize 1 } <: t_SplitN v_T v_P
            in
            let (tmp0: t_Split v_T v_P), (out: Core_models.Option.t_Option (t_Slice v_T)) =
              Core_models.Iter.Traits.Iterator.f_next #(t_Split v_T v_P)
                #FStar.Tactics.Typeclasses.solve
                self.f_inner
            in
            let self:t_SplitN v_T v_P = { self with f_inner = tmp0 } <: t_SplitN v_T v_P in
            self, out <: (t_SplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output <: (t_SplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::RSplit`]
type t_RSplit (v_T: Type0) (v_P: Type0) = { f_inner:t_Split v_T v_P }

let impl_17__new
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (v: t_Slice v_T)
      (pred: v_P)
    : t_RSplit v_T v_P = { f_inner = impl_11__new #v_T #v_P v pred } <: t_RSplit v_T v_P

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_RSplit v_T v_P) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_RSplit v_T v_P) -> true);
    f_next_post
    =
    (fun
        (self: t_RSplit v_T v_P)
        (out1: (t_RSplit v_T v_P & Core_models.Option.t_Option (t_Slice v_T)))
        ->
        true);
    f_next
    =
    fun (self: t_RSplit v_T v_P) ->
      let (tmp0: t_Split v_T v_P), (out: Core_models.Option.t_Option (t_Slice v_T)) =
        impl_11__next_back #v_T #v_P self.f_inner
      in
      let self:t_RSplit v_T v_P = { self with f_inner = tmp0 } <: t_RSplit v_T v_P in
      let hax_temp_output:Core_models.Option.t_Option (t_Slice v_T) = out in
      self, hax_temp_output <: (t_RSplit v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::RSplitN`]
type t_RSplitN (v_T: Type0) (v_P: Type0) = {
  f_inner:t_Split v_T v_P;
  f_count:usize
}

let impl_19__new
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (v: t_Slice v_T)
      (n: usize)
      (pred: v_P)
    : t_RSplitN v_T v_P =
  { f_inner = impl_11__new #v_T #v_P v pred; f_count = n } <: t_RSplitN v_T v_P

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_RSplitN v_T v_P) =
  {
    f_Item = t_Slice v_T;
    f_next_pre = (fun (self: t_RSplitN v_T v_P) -> true);
    f_next_post
    =
    (fun
        (self: t_RSplitN v_T v_P)
        (out1: (t_RSplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T)))
        ->
        true);
    f_next
    =
    fun (self: t_RSplitN v_T v_P) ->
      let (self: t_RSplitN v_T v_P), (hax_temp_output: Core_models.Option.t_Option (t_Slice v_T)) =
        if self.f_count =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T))
          <:
          (t_RSplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
        else
          if self.f_count =. mk_usize 1
          then
            let self:t_RSplitN v_T v_P = { self with f_count = mk_usize 0 } <: t_RSplitN v_T v_P in
            let (tmp0: t_Split v_T v_P), (out: Core_models.Option.t_Option (t_Slice v_T)) =
              impl_11__finish #v_T #v_P self.f_inner
            in
            let self:t_RSplitN v_T v_P = { self with f_inner = tmp0 } <: t_RSplitN v_T v_P in
            self, out <: (t_RSplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
          else
            let self:t_RSplitN v_T v_P =
              { self with f_count = self.f_count -! mk_usize 1 } <: t_RSplitN v_T v_P
            in
            let (tmp0: t_Split v_T v_P), (out: Core_models.Option.t_Option (t_Slice v_T)) =
              impl_11__next_back #v_T #v_P self.f_inner
            in
            let self:t_RSplitN v_T v_P = { self with f_inner = tmp0 } <: t_RSplitN v_T v_P in
            self, out <: (t_RSplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
      in
      self, hax_temp_output <: (t_RSplitN v_T v_P & Core_models.Option.t_Option (t_Slice v_T))
  }

/// See [`std::slice::ChunkBy`]
type t_ChunkBy (v_T: Type0) (v_P: Type0) = {
  f_v:t_Slice v_T;
  f_pred:v_P
}

let impl_21__new
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P (v_T & v_T))
      (v: t_Slice v_T)
      (pred: v_P)
    : t_ChunkBy v_T v_P = { f_v = v; f_pred = pred } <: t_ChunkBy v_T v_P

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_22': #v_T: Type0 -> #v_P: Type0 -> {| i0: Core_models.Ops.Function.t_Fn v_P (v_T & v_T) |}
  -> Core_models.Iter.Traits.Iterator.t_Iterator (t_ChunkBy v_T v_P)

unfold
let impl_22
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P (v_T & v_T))
     = impl_22' #v_T #v_P #i0
