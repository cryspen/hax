module Core_models.Slice.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Chunks (v_T: Type0) = {
  f_cs:usize;
  f_elements:t_Slice v_T
}

let impl__new (#v_T: Type0) (cs: usize) (elements: t_Slice v_T) : t_Chunks v_T =
  { f_cs = cs; f_elements = elements } <: t_Chunks v_T

type t_ChunksExact (v_T: Type0) = {
  f_cs:usize;
  f_elements:t_Slice v_T
}

let impl_1__new (#v_T: Type0) (cs: usize) (elements: t_Slice v_T) : t_ChunksExact v_T =
  { f_cs = cs; f_elements = elements } <: t_ChunksExact v_T

type t_Iter (v_T: Type0) = | Iter : Rust_primitives.Sequence.t_Seq v_T -> t_Iter v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Iter v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Iter v_T) -> true);
    f_next_post
    =
    (fun (self: t_Iter v_T) (out: (t_Iter v_T & Core_models.Option.t_Option v_T)) -> true);
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
          let res:v_T = Rust_primitives.Sequence.seq_first #v_T self._0 in
          let self:t_Iter v_T =
            {
              self with
              _0
              =
              Rust_primitives.Sequence.seq_slice #v_T
                self._0
                (mk_usize 1)
                (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize)
            }
            <:
            t_Iter v_T
          in
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
