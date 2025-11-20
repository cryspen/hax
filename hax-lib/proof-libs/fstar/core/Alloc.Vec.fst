module Alloc.Vec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Vec (v_T: Type0) (v_A: Type0) = | Vec : Rust_primitives.Seq.t_Seq v_T v_A -> t_Vec v_T v_A

let impl__new (#v_T: Type0) (_: Prims.unit) : t_Vec v_T Alloc.Alloc.t_Global =
  Vec (Rust_primitives.Seq.seq_empty #v_T #Alloc.Alloc.t_Global ())
  <:
  t_Vec v_T Alloc.Alloc.t_Global

let impl__with_capacity (#v_T: Type0) (_: Prims.unit) : t_Vec v_T Alloc.Alloc.t_Global =
  Vec (Rust_primitives.Seq.seq_empty #v_T #Alloc.Alloc.t_Global ())
  <:
  t_Vec v_T Alloc.Alloc.t_Global

let impl_1__len (#v_T #v_A: Type0) (self: t_Vec v_T v_A) : usize =
  Rust_primitives.Seq.seq_len #v_T #v_A self._0

let impl_1__pop (#v_T #v_A: Type0) (self: t_Vec v_T v_A)
    : (t_Vec v_T v_A & Core_models.Option.t_Option v_T) =
  let (self: t_Vec v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if (Rust_primitives.Seq.seq_len #v_T #v_A self._0 <: usize) =. mk_usize 0
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_Vec v_T v_A & Core_models.Option.t_Option v_T)
    else
      let self:t_Vec v_T v_A =
        {
          self with
          _0
          =
          Rust_primitives.Seq.seq_slice #v_T
            #v_A
            self._0
            (mk_usize 0)
            ((Rust_primitives.Seq.seq_len #v_T #v_A self._0 <: usize) -! mk_usize 1 <: usize)
        }
        <:
        t_Vec v_T v_A
      in
      self,
      (Core_models.Option.Option_Some (Rust_primitives.Seq.seq_last #v_T #v_A self._0)
        <:
        Core_models.Option.t_Option v_T)
      <:
      (t_Vec v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_Vec v_T v_A & Core_models.Option.t_Option v_T)

let impl_1__is_empty (#v_T #v_A: Type0) (self: t_Vec v_T v_A) : bool =
  (Rust_primitives.Seq.seq_len #v_T #v_A self._0 <: usize) =. mk_usize 0

let impl_1__as_slice (#v_T #v_A: Type0) (self: t_Vec v_T v_A) : t_Slice v_T =
  Rust_primitives.Seq.seq_to_slice #v_T #v_A self._0

assume
val impl_1__truncate': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> n: usize
  -> t_Vec v_T v_A

unfold
let impl_1__truncate (#v_T #v_A: Type0) = impl_1__truncate' #v_T #v_A

assume
val impl_1__swap_remove': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> n: usize
  -> (t_Vec v_T v_A & v_T)

unfold
let impl_1__swap_remove (#v_T #v_A: Type0) = impl_1__swap_remove' #v_T #v_A

assume
val impl_1__remove': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> index: usize
  -> (t_Vec v_T v_A & v_T)

unfold
let impl_1__remove (#v_T #v_A: Type0) = impl_1__remove' #v_T #v_A

assume
val impl_1__clear': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> t_Vec v_T v_A

unfold
let impl_1__clear (#v_T #v_A: Type0) = impl_1__clear' #v_T #v_A

let impl_1__push (#v_T #v_A: Type0) (self: t_Vec v_T v_A) (x: v_T)
    : Prims.Pure (t_Vec v_T v_A)
      (requires
        (Rust_primitives.Seq.seq_len #v_T #v_A self._0 <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_Vec v_T v_A =
    {
      self with
      _0
      =
      Rust_primitives.Seq.seq_concat #v_T
        #v_A
        self._0
        (Rust_primitives.Seq.seq_one #v_T #v_A x <: Rust_primitives.Seq.t_Seq v_T v_A)
    }
    <:
    t_Vec v_T v_A
  in
  self

let impl_1__insert (#v_T #v_A: Type0) (self: t_Vec v_T v_A) (index: usize) (element: v_T)
    : Prims.Pure (t_Vec v_T v_A)
      (requires index <=. (Rust_primitives.Seq.seq_len #v_T #v_A self._0 <: usize))
      (fun _ -> Prims.l_True) =
  let left:Rust_primitives.Seq.t_Seq v_T v_A =
    Rust_primitives.Seq.seq_slice #v_T #v_A self._0 (mk_usize 0) index
  in
  let right:Rust_primitives.Seq.t_Seq v_T v_A =
    Rust_primitives.Seq.seq_slice #v_T
      #v_A
      self._0
      index
      (Rust_primitives.Seq.seq_len #v_T #v_A self._0 <: usize)
  in
  let left:Rust_primitives.Seq.t_Seq v_T v_A =
    Rust_primitives.Seq.seq_concat #v_T
      #v_A
      left
      (Rust_primitives.Seq.seq_one #v_T #v_A element <: Rust_primitives.Seq.t_Seq v_T v_A)
  in
  let left:Rust_primitives.Seq.t_Seq v_T v_A =
    Rust_primitives.Seq.seq_concat #v_T #v_A left right
  in
  let self:t_Vec v_T v_A = { self with _0 = left } <: t_Vec v_T v_A in
  self

assume
val impl_1__resize':
    #v_T: Type0 ->
    #v_A: Type0 ->
    self: t_Vec v_T v_A ->
    new_size: usize ->
    value: v_T
  -> Prims.Pure (t_Vec v_T v_A)
      Prims.l_True
      (ensures
        fun self_e_future ->
          let self_e_future:t_Vec v_T v_A = self_e_future in
          (impl_1__len #v_T #v_A self_e_future <: usize) =. new_size)

unfold
let impl_1__resize (#v_T #v_A: Type0) = impl_1__resize' #v_T #v_A

let impl_1__append (#v_T #v_A: Type0) (self other: t_Vec v_T v_A)
    : Prims.Pure (t_Vec v_T v_A & t_Vec v_T v_A)
      (requires
        ((Rust_primitives.Hax.Int.from_machine (impl_1__len #v_T #v_A self <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (impl_1__len #v_T #v_A other <: usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let self:t_Vec v_T v_A =
    { self with _0 = Rust_primitives.Seq.seq_concat #v_T #v_A self._0 other._0 } <: t_Vec v_T v_A
  in
  let other:t_Vec v_T v_A =
    { other with _0 = Rust_primitives.Seq.seq_empty #v_T #v_A () } <: t_Vec v_T v_A
  in
  self, other <: (t_Vec v_T v_A & t_Vec v_T v_A)

let impl_2__extend_from_slice (#v_T #v_A: Type0) (s: t_Vec v_T v_A) (other: t_Slice v_T)
    : Prims.Pure (t_Vec v_T v_A)
      (requires
        ((Rust_primitives.Hax.Int.from_machine (Rust_primitives.Seq.seq_len #v_T #v_A s._0 <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #v_T other <: usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let s:t_Vec v_T v_A =
    {
      s with
      _0
      =
      Rust_primitives.Seq.seq_concat #v_T
        #v_A
        s._0
        (Rust_primitives.Seq.seq_from_slice #v_T #v_A other <: Rust_primitives.Seq.t_Seq v_T v_A)
    }
    <:
    t_Vec v_T v_A
  in
  s
