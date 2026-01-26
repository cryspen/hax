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

class t_IteratorMethods (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Iterator v_Self;
  f_fold_pre:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (v_B & (_super_i0).f_Item) |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == v_B} ->
      v_Self ->
      v_B ->
      v_F
    -> Type0;
  f_fold_post:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (v_B & (_super_i0).f_Item) |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == v_B} ->
      v_Self ->
      v_B ->
      v_F ->
      v_B
    -> Type0;
  f_fold:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (v_B & (_super_i0).f_Item) |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == v_B} ->
      x0: v_Self ->
      x1: v_B ->
      x2: v_F
    -> Prims.Pure v_B
        (f_fold_pre #v_B #v_F #i1 #_ x0 x1 x2)
        (fun result -> f_fold_post #v_B #v_F #i1 #_ x0 x1 x2 result);
  f_enumerate_pre:v_Self -> Type0;
  f_enumerate_post:v_Self -> t_Enumerate v_Self -> Type0;
  f_enumerate:x0: v_Self
    -> Prims.Pure (t_Enumerate v_Self)
        (f_enumerate_pre x0)
        (fun result -> f_enumerate_post x0 result);
  f_step_by_pre:v_Self -> usize -> Type0;
  f_step_by_post:v_Self -> usize -> t_StepBy v_Self -> Type0;
  f_step_by:x0: v_Self -> x1: usize
    -> Prims.Pure (t_StepBy v_Self)
        (f_step_by_pre x0 x1)
        (fun result -> f_step_by_post x0 x1 result);
  f_map_pre:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == v_O} ->
      v_Self ->
      v_F
    -> Type0;
  f_map_post:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == v_O} ->
      v_Self ->
      v_F ->
      t_Map v_Self v_F
    -> Type0;
  f_map:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == v_O} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (t_Map v_Self v_F)
        (f_map_pre #v_O #v_F #i1 #_ x0 x1)
        (fun result -> f_map_post #v_O #v_F #i1 #_ x0 x1 result);
  f_all_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_F
    -> Type0;
  f_all_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_F ->
      bool
    -> Type0;
  f_all:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i1.Core_models.Ops.Function.f_Output == bool} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure bool
        (f_all_pre #v_F #i1 #_ x0 x1)
        (fun result -> f_all_post #v_F #i1 #_ x0 x1 result);
  f_take_pre:v_Self -> usize -> Type0;
  f_take_post:v_Self -> usize -> t_Take v_Self -> Type0;
  f_take:x0: v_Self -> x1: usize
    -> Prims.Pure (t_Take v_Self) (f_take_pre x0 x1) (fun result -> f_take_post x0 x1 result);
  f_flat_map_pre:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i2.Core_models.Ops.Function.f_Output == v_U} ->
      v_Self ->
      v_F
    -> Type0;
  f_flat_map_post:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i2.Core_models.Ops.Function.f_Output == v_U} ->
      v_Self ->
      v_F ->
      t_FlatMap v_Self v_U v_F
    -> Type0;
  f_flat_map:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_FnOnce v_F (_super_i0).f_Item |} ->
      #_: unit{i2.Core_models.Ops.Function.f_Output == v_U} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (t_FlatMap v_Self v_U v_F)
        (f_flat_map_pre #v_U #v_F #i1 #i2 #_ x0 x1)
        (fun result -> f_flat_map_post #v_U #v_F #i1 #i2 #_ x0 x1 result);
  f_flatten_pre:{| i1: t_Iterator (_super_i0).f_Item |} -> v_Self -> Type0;
  f_flatten_post:{| i1: t_Iterator (_super_i0).f_Item |} -> v_Self -> t_Flatten v_Self -> Type0;
  f_flatten:{| i1: t_Iterator (_super_i0).f_Item |} -> x0: v_Self
    -> Prims.Pure (t_Flatten v_Self)
        (f_flatten_pre #i1 x0)
        (fun result -> f_flatten_post #i1 x0 result);
  f_zip_pre:#v_I2: Type0 -> {| i1: t_Iterator v_I2 |} -> v_Self -> v_I2 -> Type0;
  f_zip_post:#v_I2: Type0 -> {| i1: t_Iterator v_I2 |} -> v_Self -> v_I2 -> t_Zip v_Self v_I2
    -> Type0;
  f_zip:#v_I2: Type0 -> {| i1: t_Iterator v_I2 |} -> x0: v_Self -> x1: v_I2
    -> Prims.Pure (t_Zip v_Self v_I2)
        (f_zip_pre #v_I2 #i1 x0 x1)
        (fun result -> f_zip_post #v_I2 #i1 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_IteratorMethods v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : t_IteratorMethods v_I =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_fold_pre
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F (v_B & i0.f_Item))
        (self: v_I)
        (init: v_B)
        (f: v_F)
        ->
        true);
    f_fold_post
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F (v_B & i0.f_Item))
        (self: v_I)
        (init: v_B)
        (f: v_F)
        (out: v_B)
        ->
        true);
    f_fold
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F (v_B & i0.f_Item))
        (self: v_I)
        (init: v_B)
        (f: v_F)
        ->
        init);
    f_enumerate_pre = (fun (self: v_I) -> true);
    f_enumerate_post = (fun (self: v_I) (out: t_Enumerate v_I) -> true);
    f_enumerate = (fun (self: v_I) -> impl__new #v_I self);
    f_step_by_pre = (fun (self: v_I) (step: usize) -> true);
    f_step_by_post = (fun (self: v_I) (step: usize) (out: t_StepBy v_I) -> true);
    f_step_by = (fun (self: v_I) (step: usize) -> impl__new__from__step_by #v_I self step);
    f_map_pre
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_map_post
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: t_Map v_I v_F)
        ->
        true);
    f_map
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        impl__new__from__map #v_I #v_F self f);
    f_all_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_all_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: bool)
        ->
        true);
    f_all
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_take_pre = (fun (self: v_I) (n: usize) -> true);
    f_take_post = (fun (self: v_I) (n: usize) (out: t_Take v_I) -> true);
    f_take = (fun (self: v_I) (n: usize) -> impl__new__from__take #v_I self n);
    f_flat_map_pre
    =
    (fun
        (#v_U: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_flat_map_post
    =
    (fun
        (#v_U: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: t_FlatMap v_I v_U v_F)
        ->
        true);
    f_flat_map
    =
    (fun
        (#v_U: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Ops.Function.t_FnOnce v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        impl__new__from__flat_map #v_I #v_U #v_F self f);
    f_flatten_pre
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item) (self: v_I) -> true);
    f_flatten_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item)
        (self: v_I)
        (out: t_Flatten v_I)
        ->
        true);
    f_flatten
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item) (self: v_I) ->
        impl__new__from__flatten #v_I self);
    f_zip_pre
    =
    (fun
        (#v_I2: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
        (self: v_I)
        (it2: v_I2)
        ->
        true);
    f_zip_post
    =
    (fun
        (#v_I2: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
        (self: v_I)
        (it2: v_I2)
        (out: t_Zip v_I v_I2)
        ->
        true);
    f_zip
    =
    fun
      (#v_I2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
      (self: v_I)
      (it2: v_I2)
      ->
      impl__new__from__zip #v_I #v_I2 self it2
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__iterator
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : Core_models.Iter.Traits.Collect.t_IntoIterator v_I =
  {
    f_IntoIter = v_I;
    f_into_iter_pre = (fun (self: v_I) -> true);
    f_into_iter_post = (fun (self: v_I) (out: v_I) -> true);
    f_into_iter = fun (self: v_I) -> self
  }
