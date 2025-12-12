module Core_models.Iter.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Enumerate (v_I: Type0) = {
  f_iter:v_I;
  f_count:usize
}

let impl__new (#v_I: Type0) (iter: v_I) : t_Enumerate v_I =
  { f_iter = iter; f_count = mk_usize 0 } <: t_Enumerate v_I

type t_FlatMap (v_I: Type0) (v_U: Type0) (v_F: Type0) = {
  f_it:v_I;
  f_f:v_F;
  f_current:Core_models.Option.t_Option v_U
}

type t_Map (v_I: Type0) (v_F: Type0) = {
  f_iter:v_I;
  f_f:v_F
}

let impl__new__from__map (#v_I #v_F: Type0) (iter: v_I) (f: v_F) : t_Map v_I v_F =
  { f_iter = iter; f_f = f } <: t_Map v_I v_F

type t_StepBy (v_I: Type0) = {
  f_iter:v_I;
  f_step:usize
}

let impl__new__from__step_by (#v_I: Type0) (iter: v_I) (step: usize) : t_StepBy v_I =
  { f_iter = iter; f_step = step } <: t_StepBy v_I

type t_Take (v_I: Type0) = {
  f_iter:v_I;
  f_n:usize
}

let impl__new__from__take (#v_I: Type0) (iter: v_I) (n: usize) : t_Take v_I =
  { f_iter = iter; f_n = n } <: t_Take v_I

type t_Zip (v_I1: Type0) (v_I2: Type0) = {
  f_it1:v_I1;
  f_it2:v_I2
}

class t_Iterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Item:Type0;
  f_next_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_next_post:v_Self -> (v_Self & Core_models.Option.t_Option f_Item) -> Type0;
  f_next:x0: v_Self
    -> Prims.Pure (v_Self & Core_models.Option.t_Option f_Item)
        (f_next_pre x0)
        (fun result -> f_next_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : t_Iterator (t_Enumerate v_I) =
  {
    f_Item = (usize & i0.f_Item);
    f_next_pre = (fun (self: t_Enumerate v_I) -> true);
    f_next_post
    =
    (fun
        (self: t_Enumerate v_I)
        (out1: (t_Enumerate v_I & Core_models.Option.t_Option (usize & i0.f_Item)))
        ->
        true);
    f_next
    =
    fun (self: t_Enumerate v_I) ->
      let (tmp0: v_I), (out: Core_models.Option.t_Option i0.f_Item) =
        f_next #v_I #FStar.Tactics.Typeclasses.solve self.f_iter
      in
      let self:t_Enumerate v_I = { self with f_iter = tmp0 } <: t_Enumerate v_I in
      let
      (self: t_Enumerate v_I), (hax_temp_output: Core_models.Option.t_Option (usize & i0.f_Item)) =
        match out <: Core_models.Option.t_Option i0.f_Item with
        | Core_models.Option.Option_Some a ->
          let i:usize = self.f_count in
          let _:Prims.unit =
            Hax_lib.v_assume (b2t (self.f_count <. Core_models.Num.impl_usize__MAX <: bool))
          in
          let self:t_Enumerate v_I =
            { self with f_count = self.f_count +! mk_usize 1 } <: t_Enumerate v_I
          in
          self,
          (Core_models.Option.Option_Some (i, a <: (usize & i0.f_Item))
            <:
            Core_models.Option.t_Option (usize & i0.f_Item))
          <:
          (t_Enumerate v_I & Core_models.Option.t_Option (usize & i0.f_Item))
        | Core_models.Option.Option_None  ->
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (usize & i0.f_Item))
          <:
          (t_Enumerate v_I & Core_models.Option.t_Option (usize & i0.f_Item))
      in
      self, hax_temp_output <: (t_Enumerate v_I & Core_models.Option.t_Option (usize & i0.f_Item))
  }

let impl__new__from__flat_map
      (#v_I #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
      (#_: unit{i2.Core_models.Ops.Function.f_Output == v_U})
      (it: v_I)
      (f: v_F)
    : t_FlatMap v_I v_U v_F =
  {
    f_it = it;
    f_f = f;
    f_current = Core_models.Option.Option_None <: Core_models.Option.t_Option v_U
  }
  <:
  t_FlatMap v_I v_U v_F

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__flat_map':
    #v_I: Type0 ->
    #v_U: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: t_Iterator v_U |} ->
    {| i2: Core_models.Ops.Function.t_FnOnce v_F i0.f_Item |} ->
    #_: unit{i2.Core_models.Ops.Function.f_Output == v_U}
  -> t_Iterator (t_FlatMap v_I v_U v_F)

unfold
let impl_1__from__flat_map
      (#v_I #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
      (#_: unit{i2.Core_models.Ops.Function.f_Output == v_U})
     = impl_1__from__flat_map' #v_I #v_U #v_F #i0 #i1 #i2 #_

noeq

type t_Flatten (v_I: Type0) {| i0: t_Iterator v_I |} {| i1: t_Iterator i0.f_Item |} = {
  f_it:v_I;
  f_current:Core_models.Option.t_Option i0.f_Item
}

let impl__new__from__flatten
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item)
      (it: v_I)
    : t_Flatten v_I =
  { f_it = it; f_current = Core_models.Option.Option_None <: Core_models.Option.t_Option i0.f_Item }
  <:
  t_Flatten v_I

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__flatten':
    #v_I: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: t_Iterator i0.f_Item |}
  -> t_Iterator (t_Flatten v_I)

unfold
let impl_1__from__flatten
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item)
     = impl_1__from__flatten' #v_I #i0 #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__map
      (#v_I #v_O #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_O})
    : t_Iterator (t_Map v_I v_F) =
  {
    f_Item = v_O;
    f_next_pre = (fun (self: t_Map v_I v_F) -> true);
    f_next_post
    =
    (fun (self: t_Map v_I v_F) (out1: (t_Map v_I v_F & Core_models.Option.t_Option v_O)) -> true);
    f_next
    =
    fun (self: t_Map v_I v_F) ->
      let (tmp0: v_I), (out: Core_models.Option.t_Option i0.f_Item) =
        f_next #v_I #FStar.Tactics.Typeclasses.solve self.f_iter
      in
      let self:t_Map v_I v_F = { self with f_iter = tmp0 } <: t_Map v_I v_F in
      let hax_temp_output:Core_models.Option.t_Option v_O =
        match out <: Core_models.Option.t_Option i0.f_Item with
        | Core_models.Option.Option_Some v ->
          Core_models.Option.Option_Some
          (Core_models.Ops.Function.f_call_once #v_F
              #i0.f_Item
              #FStar.Tactics.Typeclasses.solve
              self.f_f
              v)
          <:
          Core_models.Option.t_Option v_O
        | Core_models.Option.Option_None  ->
          Core_models.Option.Option_None <: Core_models.Option.t_Option v_O
      in
      self, hax_temp_output <: (t_Map v_I v_F & Core_models.Option.t_Option v_O)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__step_by': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> t_Iterator (t_StepBy v_I)

unfold
let impl_1__from__step_by
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
     = impl_1__from__step_by' #v_I #i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__take (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : t_Iterator (t_Take v_I) =
  {
    f_Item = i0.f_Item;
    f_next_pre = (fun (self: t_Take v_I) -> true);
    f_next_post
    =
    (fun (self: t_Take v_I) (out1: (t_Take v_I & Core_models.Option.t_Option i0.f_Item)) -> true);
    f_next
    =
    fun (self: t_Take v_I) ->
      let (self: t_Take v_I), (hax_temp_output: Core_models.Option.t_Option i0.f_Item) =
        if self.f_n <>. mk_usize 0
        then
          let self:t_Take v_I = { self with f_n = self.f_n -! mk_usize 1 } <: t_Take v_I in
          let (tmp0: v_I), (out: Core_models.Option.t_Option i0.f_Item) =
            f_next #v_I #FStar.Tactics.Typeclasses.solve self.f_iter
          in
          let self:t_Take v_I = { self with f_iter = tmp0 } <: t_Take v_I in
          self, out <: (t_Take v_I & Core_models.Option.t_Option i0.f_Item)
        else
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i0.f_Item)
          <:
          (t_Take v_I & Core_models.Option.t_Option i0.f_Item)
      in
      self, hax_temp_output <: (t_Take v_I & Core_models.Option.t_Option i0.f_Item)
  }

let impl__new__from__zip
      (#v_I1 #v_I2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
      (it1: v_I1)
      (it2: v_I2)
    : t_Zip v_I1 v_I2 = { f_it1 = it1; f_it2 = it2 } <: t_Zip v_I1 v_I2

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__zip':
    #v_I1: Type0 ->
    #v_I2: Type0 ->
    {| i0: t_Iterator v_I1 |} ->
    {| i1: t_Iterator v_I2 |}
  -> t_Iterator (t_Zip v_I1 v_I2)

unfold
let impl_1__from__zip
      (#v_I1 #v_I2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
     = impl_1__from__zip' #v_I1 #v_I2 #i0 #i1

assume
val fold':
    #v_I: Type0 ->
    #v_B: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_FnOnce v_F (v_B & i0.f_Item) |} ->
    #_: unit{i1.Core_models.Ops.Function.f_Output == v_B} ->
    it: v_I ->
    init: v_B ->
    f: v_F
  -> v_B

unfold
let fold
      (#v_I #v_B #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F (v_B & i0.f_Item))
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_B})
     = fold' #v_I #v_B #v_F #i0 #i1 #_

let enumerate (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) (it: v_I)
    : t_Enumerate v_I = impl__new #v_I it

let step_by
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (it: v_I)
      (step: usize)
    : t_StepBy v_I = impl__new__from__step_by #v_I it step

let map
      (#v_I #v_O #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_O})
      (it: v_I)
      (f: v_F)
    : t_Map v_I v_F = impl__new__from__map #v_I #v_F it f

assume
val all':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_FnOnce v_F i0.f_Item |} ->
    #_: unit{i1.Core_models.Ops.Function.f_Output == bool} ->
    it: v_I ->
    f: v_F
  -> bool

unfold
let all
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
      (#_: unit{i1.Core_models.Ops.Function.f_Output == bool})
     = all' #v_I #v_F #i0 #i1 #_

let take
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (it: v_I)
      (n: usize)
    : t_Take v_I = impl__new__from__take #v_I it n

let flat_map
      (#v_I #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
      (#_: unit{i2.Core_models.Ops.Function.f_Output == v_U})
      (it: v_I)
      (f: v_F)
    : t_FlatMap v_I v_U v_F = impl__new__from__flat_map #v_I #v_U #v_F it f

let flatten
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item)
      (it: v_I)
    : t_Flatten v_I = impl__new__from__flatten #v_I it

let zip
      (#v_I1 #v_I2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
      (it1: v_I1)
      (it2: v_I2)
    : t_Zip v_I1 v_I2 = impl__new__from__zip #v_I1 #v_I2 it1 it2
