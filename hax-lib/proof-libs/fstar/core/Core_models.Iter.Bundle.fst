module Core_models.Iter.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Chain`]
type t_Chain (v_A: Type0) (v_B: Type0) = {
  f_a:Core_models.Option.t_Option v_A;
  f_b:v_B
}

/// See [`std::iter::Enumerate`]
type t_Enumerate (v_I: Type0) = {
  f_iter:v_I;
  f_count:usize
}

let impl__new__from__enumerate (#v_I: Type0) (iter: v_I) : t_Enumerate v_I =
  { f_iter = iter; f_count = mk_usize 0 } <: t_Enumerate v_I

/// See [`std::iter::Filter`]
type t_Filter (v_I: Type0) (v_P: Type0) = {
  f_iter:v_I;
  f_predicate:v_P
}

let impl__new__from__filter (#v_I #v_P: Type0) (iter: v_I) (predicate: v_P) : t_Filter v_I v_P =
  { f_iter = iter; f_predicate = predicate } <: t_Filter v_I v_P

/// See [`std::iter::FlatMap`]
type t_FlatMap (v_I: Type0) (v_U: Type0) (v_F: Type0) = {
  f_it:v_I;
  f_f:v_F;
  f_current:Core_models.Option.t_Option v_U
}

/// See [`std::iter::Map`]
type t_Map (v_I: Type0) (v_F: Type0) = {
  f_iter:v_I;
  f_f:v_F
}

let impl__new__from__map (#v_I #v_F: Type0) (iter: v_I) (f: v_F) : t_Map v_I v_F =
  { f_iter = iter; f_f = f } <: t_Map v_I v_F

/// See [`std::iter::Skip`]
type t_Skip (v_I: Type0) = {
  f_iter:v_I;
  f_n:usize
}

let impl__new__from__skip (#v_I: Type0) (iter: v_I) (n: usize) : t_Skip v_I =
  { f_iter = iter; f_n = n } <: t_Skip v_I

/// See [`std::iter::StepBy`]
type t_StepBy (v_I: Type0) = {
  f_iter:v_I;
  f_step:usize
}

let impl__new__from__step_by (#v_I: Type0) (iter: v_I) (step: usize) : t_StepBy v_I =
  { f_iter = iter; f_step = step } <: t_StepBy v_I

/// See [`std::iter::Take`]
type t_Take (v_I: Type0) = {
  f_iter:v_I;
  f_n:usize
}

let impl__new__from__take (#v_I: Type0) (iter: v_I) (n: usize) : t_Take v_I =
  { f_iter = iter; f_n = n } <: t_Take v_I

/// See [`std::iter::Zip`]
type t_Zip (v_I1: Type0) (v_I2: Type0) = {
  f_it1:v_I1;
  f_it2:v_I2
}

/// See [`std::iter::Iterator`]
class t_Iterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Item:Type0;
  f_next_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_next_post:v_Self -> (v_Self & Core_models.Option.t_Option f_Item) -> Type0;
  f_next:x0: v_Self
    -> Prims.Pure (v_Self & Core_models.Option.t_Option f_Item)
        (f_next_pre x0)
        (fun result -> f_next_post x0 result)
}

let impl__new
      (#v_A #v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_B)
      (#_: unit{i1.f_Item == i0.f_Item})
      (a: v_A)
      (b: v_B)
    : t_Chain v_A v_B =
  { f_a = Core_models.Option.Option_Some a <: Core_models.Option.t_Option v_A; f_b = b }
  <:
  t_Chain v_A v_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1':
    #v_A: Type0 ->
    #v_B: Type0 ->
    {| i0: t_Iterator v_A |} ->
    {| i1: t_Iterator v_B |} ->
    #_: unit{i1.f_Item == i0.f_Item}
  -> t_Iterator (t_Chain v_A v_B)

unfold
let impl_1
      (#v_A #v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_B)
      (#_: unit{i1.f_Item == i0.f_Item})
     = impl_1' #v_A #v_B #i0 #i1 #_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__enumerate
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__filter':
    #v_I: Type0 ->
    #v_P: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool}
  -> t_Iterator (t_Filter v_I v_P)

unfold
let impl_1__from__filter
      (#v_I #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool})
     = impl_1__from__filter' #v_I #v_P #i0 #i1 #_

let impl__new__from__flat_map
      (#v_I #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (#_: unit{i2._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_U})
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
    {| i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    #_: unit{i2._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_U}
  -> t_Iterator (t_FlatMap v_I v_U v_F)

unfold
let impl_1__from__flat_map
      (#v_I #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (#_: unit{i2._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_U})
     = impl_1__from__flat_map' #v_I #v_U #v_F #i0 #i1 #i2 #_

noeq

/// See [`std::iter::Flatten`]
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
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_O})
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
          (Core_models.Ops.Function.f_call #v_F
              #i0.f_Item
              #FStar.Tactics.Typeclasses.solve
              self.f_f
              (v <: i0.f_Item))
          <:
          Core_models.Option.t_Option v_O
        | Core_models.Option.Option_None  ->
          Core_models.Option.Option_None <: Core_models.Option.t_Option v_O
      in
      self, hax_temp_output <: (t_Map v_I v_F & Core_models.Option.t_Option v_O)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__skip': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> t_Iterator (t_Skip v_I)

unfold
let impl_1__from__skip (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  impl_1__from__skip' #v_I #i0

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
      {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & (_super_i0).f_Item) |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_B} ->
      v_Self ->
      v_B ->
      v_F
    -> Type0;
  f_fold_post:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & (_super_i0).f_Item) |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_B} ->
      v_Self ->
      v_B ->
      v_F ->
      v_B
    -> Type0;
  f_fold:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & (_super_i0).f_Item) |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_B} ->
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
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_O} ->
      v_Self ->
      v_F
    -> Type0;
  f_map_post:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_O} ->
      v_Self ->
      v_F ->
      t_Map v_Self v_F
    -> Type0;
  f_map:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_O} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (t_Map v_Self v_F)
        (f_map_pre #v_O #v_F #i1 #_ x0 x1)
        (fun result -> f_map_post #v_O #v_F #i1 #_ x0 x1 result);
  f_all_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_F
    -> Type0;
  f_all_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_F ->
      bool
    -> Type0;
  f_all:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
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
      {| i2: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i2._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_U} ->
      v_Self ->
      v_F
    -> Type0;
  f_flat_map_post:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i2._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_U} ->
      v_Self ->
      v_F ->
      t_FlatMap v_Self v_U v_F
    -> Type0;
  f_flat_map:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i2._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_U} ->
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
        (fun result -> f_zip_post #v_I2 #i1 x0 x1 result);
  f_filter_pre:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_P
    -> Type0;
  f_filter_post:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_P ->
      t_Filter v_Self v_P
    -> Type0;
  f_filter:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      x0: v_Self ->
      x1: v_P
    -> Prims.Pure (t_Filter v_Self v_P)
        (f_filter_pre #v_P #i1 #_ x0 x1)
        (fun result -> f_filter_post #v_P #i1 #_ x0 x1 result);
  f_chain_pre:
      #v_U: Type0 ->
      {| i1: t_Iterator v_U |} ->
      #_: unit{i1.f_Item == (_super_i0).f_Item} ->
      v_Self ->
      v_U
    -> Type0;
  f_chain_post:
      #v_U: Type0 ->
      {| i1: t_Iterator v_U |} ->
      #_: unit{i1.f_Item == (_super_i0).f_Item} ->
      v_Self ->
      v_U ->
      t_Chain v_Self v_U
    -> Type0;
  f_chain:
      #v_U: Type0 ->
      {| i1: t_Iterator v_U |} ->
      #_: unit{i1.f_Item == (_super_i0).f_Item} ->
      x0: v_Self ->
      x1: v_U
    -> Prims.Pure (t_Chain v_Self v_U)
        (f_chain_pre #v_U #i1 #_ x0 x1)
        (fun result -> f_chain_post #v_U #i1 #_ x0 x1 result);
  f_skip_pre:v_Self -> usize -> Type0;
  f_skip_post:v_Self -> usize -> t_Skip v_Self -> Type0;
  f_skip:x0: v_Self -> x1: usize
    -> Prims.Pure (t_Skip v_Self) (f_skip_pre x0 x1) (fun result -> f_skip_post x0 x1 result);
  f_any_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_F
    -> Type0;
  f_any_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_F ->
      bool
    -> Type0;
  f_any:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure bool
        (f_any_pre #v_F #i1 #_ x0 x1)
        (fun result -> f_any_post #v_F #i1 #_ x0 x1 result);
  f_find_pre:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_P
    -> Type0;
  f_find_post:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_P ->
      Core_models.Option.t_Option (_super_i0).f_Item
    -> Type0;
  f_find:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      x0: v_Self ->
      x1: v_P
    -> Prims.Pure (Core_models.Option.t_Option (_super_i0).f_Item)
        (f_find_pre #v_P #i1 #_ x0 x1)
        (fun result -> f_find_post #v_P #i1 #_ x0 x1 result);
  f_find_map_pre:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_:
        unit
          { i1._super_i0._super_i0.Core_models.Ops.Function.f_Output ==
            Core_models.Option.t_Option v_B } ->
      v_Self ->
      v_F
    -> Type0;
  f_find_map_post:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_:
        unit
          { i1._super_i0._super_i0.Core_models.Ops.Function.f_Output ==
            Core_models.Option.t_Option v_B } ->
      v_Self ->
      v_F ->
      Core_models.Option.t_Option v_B
    -> Type0;
  f_find_map:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_:
        unit
          { i1._super_i0._super_i0.Core_models.Ops.Function.f_Output ==
            Core_models.Option.t_Option v_B } ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (Core_models.Option.t_Option v_B)
        (f_find_map_pre #v_B #v_F #i1 #_ x0 x1)
        (fun result -> f_find_map_post #v_B #v_F #i1 #_ x0 x1 result);
  f_position_pre:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_P
    -> Type0;
  f_position_post:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      v_Self ->
      v_P ->
      Core_models.Option.t_Option usize
    -> Type0;
  f_position:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
      x0: v_Self ->
      x1: v_P
    -> Prims.Pure (Core_models.Option.t_Option usize)
        (f_position_pre #v_P #i1 #_ x0 x1)
        (fun result -> f_position_post #v_P #i1 #_ x0 x1 result);
  f_count_pre:v_Self -> Type0;
  f_count_post:v_Self -> usize -> Type0;
  f_count:x0: v_Self -> Prims.Pure usize (f_count_pre x0) (fun result -> f_count_post x0 result);
  f_nth_pre:v_Self -> usize -> Type0;
  f_nth_post:v_Self -> usize -> Core_models.Option.t_Option (_super_i0).f_Item -> Type0;
  f_nth:x0: v_Self -> x1: usize
    -> Prims.Pure (Core_models.Option.t_Option (_super_i0).f_Item)
        (f_nth_pre x0 x1)
        (fun result -> f_nth_post x0 x1 result);
  f_last_pre:v_Self -> Type0;
  f_last_post:v_Self -> Core_models.Option.t_Option (_super_i0).f_Item -> Type0;
  f_last:x0: v_Self
    -> Prims.Pure (Core_models.Option.t_Option (_super_i0).f_Item)
        (f_last_pre x0)
        (fun result -> f_last_post x0 result);
  f_for_each_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == Prims.unit} ->
      v_Self ->
      v_F
    -> Type0;
  f_for_each_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == Prims.unit} ->
      v_Self ->
      v_F ->
      Prims.unit
    -> Type0;
  f_for_each:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == Prims.unit} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure Prims.unit
        (f_for_each_pre #v_F #i1 #_ x0 x1)
        (fun result -> f_for_each_post #v_F #i1 #_ x0 x1 result);
  f_reduce_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F ((_super_i0).f_Item & (_super_i0).f_Item) |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == (_super_i0).f_Item} ->
      v_Self ->
      v_F
    -> Type0;
  f_reduce_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F ((_super_i0).f_Item & (_super_i0).f_Item) |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == (_super_i0).f_Item} ->
      v_Self ->
      v_F ->
      Core_models.Option.t_Option (_super_i0).f_Item
    -> Type0;
  f_reduce:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F ((_super_i0).f_Item & (_super_i0).f_Item) |} ->
      #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == (_super_i0).f_Item} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (Core_models.Option.t_Option (_super_i0).f_Item)
        (f_reduce_pre #v_F #i1 #_ x0 x1)
        (fun result -> f_reduce_post #v_F #i1 #_ x0 x1 result);
  f_min_pre:{| i1: Core_models.Cmp.t_Ord (_super_i0).f_Item |} -> v_Self -> Type0;
  f_min_post:
      {| i1: Core_models.Cmp.t_Ord (_super_i0).f_Item |} ->
      v_Self ->
      Core_models.Option.t_Option (_super_i0).f_Item
    -> Type0;
  f_min:{| i1: Core_models.Cmp.t_Ord (_super_i0).f_Item |} -> x0: v_Self
    -> Prims.Pure (Core_models.Option.t_Option (_super_i0).f_Item)
        (f_min_pre #i1 x0)
        (fun result -> f_min_post #i1 x0 result);
  f_max_pre:{| i1: Core_models.Cmp.t_Ord (_super_i0).f_Item |} -> v_Self -> Type0;
  f_max_post:
      {| i1: Core_models.Cmp.t_Ord (_super_i0).f_Item |} ->
      v_Self ->
      Core_models.Option.t_Option (_super_i0).f_Item
    -> Type0;
  f_max:{| i1: Core_models.Cmp.t_Ord (_super_i0).f_Item |} -> x0: v_Self
    -> Prims.Pure (Core_models.Option.t_Option (_super_i0).f_Item)
        (f_max_pre #i1 x0)
        (fun result -> f_max_post #i1 x0 result);
  f_collect_pre:
      #v_B: Type0 ->
      {| i1: Core_models.Iter.Traits.Collect.t_FromIterator v_B (_super_i0).f_Item |} ->
      v_Self
    -> Type0;
  f_collect_post:
      #v_B: Type0 ->
      {| i1: Core_models.Iter.Traits.Collect.t_FromIterator v_B (_super_i0).f_Item |} ->
      v_Self ->
      v_B
    -> Type0;
  f_collect:
      #v_B: Type0 ->
      {| i1: Core_models.Iter.Traits.Collect.t_FromIterator v_B (_super_i0).f_Item |} ->
      x0: v_Self
    -> Prims.Pure v_B (f_collect_pre #v_B #i1 x0) (fun result -> f_collect_post #v_B #i1 x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_IteratorMethods v_Self|} -> i._super_i0

assume
val iter_fold':
    #v_I: Type0 ->
    #v_B: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item) |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_B} ->
    iter: v_I ->
    init: v_B ->
    f: v_F
  -> v_B

unfold
let iter_fold
      (#v_I #v_B #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_B})
     = iter_fold' #v_I #v_B #v_F #i0 #i1 #_

assume
val iter_all':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
    iter: v_I ->
    f: v_F
  -> bool

unfold
let iter_all
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool})
     = iter_all' #v_I #v_F #i0 #i1 #_

assume
val iter_any':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
    iter: v_I ->
    f: v_F
  -> bool

unfold
let iter_any
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool})
     = iter_any' #v_I #v_F #i0 #i1 #_

assume
val iter_find':
    #v_I: Type0 ->
    #v_P: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
    iter: v_I ->
    predicate: v_P
  -> (v_I & Core_models.Option.t_Option i0.f_Item)

unfold
let iter_find
      (#v_I #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool})
     = iter_find' #v_I #v_P #i0 #i1 #_

assume
val iter_find_map':
    #v_I: Type0 ->
    #v_B: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    #_:
      unit
        { i1._super_i0._super_i0.Core_models.Ops.Function.f_Output ==
          Core_models.Option.t_Option v_B } ->
    iter: v_I ->
    f: v_F
  -> Core_models.Option.t_Option v_B

unfold
let iter_find_map
      (#v_I #v_B #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (#_:
          unit
            { i1._super_i0._super_i0.Core_models.Ops.Function.f_Output ==
              Core_models.Option.t_Option v_B })
     = iter_find_map' #v_I #v_B #v_F #i0 #i1 #_

assume
val iter_position':
    #v_I: Type0 ->
    #v_P: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool} ->
    iter: v_I ->
    predicate: v_P
  -> Core_models.Option.t_Option usize

unfold
let iter_position
      (#v_I #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == bool})
     = iter_position' #v_I #v_P #i0 #i1 #_

assume
val iter_count': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> iter: v_I -> usize

unfold
let iter_count (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  iter_count' #v_I #i0

assume
val iter_nth': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> iter: v_I -> n: usize
  -> Core_models.Option.t_Option i0.f_Item

unfold
let iter_nth (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  iter_nth' #v_I #i0

assume
val iter_last': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> iter: v_I
  -> Core_models.Option.t_Option i0.f_Item

unfold
let iter_last (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  iter_last' #v_I #i0

assume
val iter_for_each':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == Prims.unit} ->
    iter: v_I ->
    f: v_F
  -> Prims.unit

unfold
let iter_for_each
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == Prims.unit})
     = iter_for_each' #v_I #v_F #i0 #i1 #_

assume
val iter_reduce':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item) |} ->
    #_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == i0.f_Item} ->
    iter: v_I ->
    f: v_F
  -> Core_models.Option.t_Option i0.f_Item

unfold
let iter_reduce
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
      (#_: unit{i1._super_i0._super_i0.Core_models.Ops.Function.f_Output == i0.f_Item})
     = iter_reduce' #v_I #v_F #i0 #i1 #_

assume
val iter_min':
    #v_I: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Cmp.t_Ord i0.f_Item |} ->
    iter: v_I
  -> Core_models.Option.t_Option i0.f_Item

unfold
let iter_min
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
     = iter_min' #v_I #i0 #i1

assume
val iter_max':
    #v_I: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Cmp.t_Ord i0.f_Item |} ->
    iter: v_I
  -> Core_models.Option.t_Option i0.f_Item

unfold
let iter_max
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
     = iter_max' #v_I #i0 #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__iterator
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : Core_models.Iter.Traits.Collect.t_IntoIterator v_I =
  {
    f_Item = i0.f_Item;
    f_IntoIter = v_I;
    f_into_iter_pre = (fun (self: v_I) -> true);
    f_into_iter_post = (fun (self: v_I) (out: v_I) -> true);
    f_into_iter = fun (self: v_I) -> self
  }

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
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
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
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
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
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
        (self: v_I)
        (init: v_B)
        (f: v_F)
        ->
        iter_fold #v_I #v_B #v_F self init f);
    f_enumerate_pre = (fun (self: v_I) -> true);
    f_enumerate_post = (fun (self: v_I) (out: t_Enumerate v_I) -> true);
    f_enumerate = (fun (self: v_I) -> impl__new__from__enumerate #v_I self);
    f_step_by_pre = (fun (self: v_I) (step: usize) -> true);
    f_step_by_post = (fun (self: v_I) (step: usize) (out: t_StepBy v_I) -> true);
    f_step_by = (fun (self: v_I) (step: usize) -> impl__new__from__step_by #v_I self step);
    f_map_pre
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_map_post
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
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
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        impl__new__from__map #v_I #v_F self f);
    f_all_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_all_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: bool)
        ->
        true);
    f_all
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_all #v_I #v_F self f);
    f_take_pre = (fun (self: v_I) (n: usize) -> true);
    f_take_post = (fun (self: v_I) (n: usize) (out: t_Take v_I) -> true);
    f_take = (fun (self: v_I) (n: usize) -> impl__new__from__take #v_I self n);
    f_flat_map_pre
    =
    (fun
        (#v_U: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
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
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
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
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
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
    (fun
        (#v_I2: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
        (self: v_I)
        (it2: v_I2)
        ->
        impl__new__from__zip #v_I #v_I2 self it2);
    f_filter_pre
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        true);
    f_filter_post
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        (out: t_Filter v_I v_P)
        ->
        true);
    f_filter
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        impl__new__from__filter #v_I #v_P self predicate);
    f_chain_pre
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (self: v_I)
        (other: v_U)
        ->
        true);
    f_chain_post
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (self: v_I)
        (other: v_U)
        (out: t_Chain v_I v_U)
        ->
        true);
    f_chain
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (self: v_I)
        (other: v_U)
        ->
        impl__new #v_I #v_U self other);
    f_skip_pre = (fun (self: v_I) (n: usize) -> true);
    f_skip_post = (fun (self: v_I) (n: usize) (out: t_Skip v_I) -> true);
    f_skip = (fun (self: v_I) (n: usize) -> impl__new__from__skip #v_I self n);
    f_any_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_any_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: bool)
        ->
        true);
    f_any
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_any #v_I #v_F self f);
    f_find_pre
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        true);
    f_find_post
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        (out1: Core_models.Option.t_Option i0.f_Item)
        ->
        true);
    f_find
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        let (tmp0: v_I), (out: Core_models.Option.t_Option i0.f_Item) =
          iter_find #v_I #v_P self predicate
        in
        let self:v_I = tmp0 in
        out);
    f_find_map_pre
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_find_map_post
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: Core_models.Option.t_Option v_B)
        ->
        true);
    f_find_map
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_find_map #v_I #v_B #v_F self f);
    f_position_pre
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        true);
    f_position_post
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        (out: Core_models.Option.t_Option usize)
        ->
        true);
    f_position
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        iter_position #v_I #v_P self predicate);
    f_count_pre = (fun (self: v_I) -> true);
    f_count_post = (fun (self: v_I) (out: usize) -> true);
    f_count = (fun (self: v_I) -> iter_count #v_I self);
    f_nth_pre = (fun (self: v_I) (n: usize) -> true);
    f_nth_post = (fun (self: v_I) (n: usize) (out: Core_models.Option.t_Option i0.f_Item) -> true);
    f_nth = (fun (self: v_I) (n: usize) -> iter_nth #v_I self n);
    f_last_pre = (fun (self: v_I) -> true);
    f_last_post = (fun (self: v_I) (out: Core_models.Option.t_Option i0.f_Item) -> true);
    f_last = (fun (self: v_I) -> iter_last #v_I self);
    f_for_each_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_for_each_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: Prims.unit)
        ->
        true);
    f_for_each
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_for_each #v_I #v_F self f);
    f_reduce_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_reduce_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
        (self: v_I)
        (f: v_F)
        (out: Core_models.Option.t_Option i0.f_Item)
        ->
        true);
    f_reduce
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
        (self: v_I)
        (f: v_F)
        ->
        iter_reduce #v_I #v_F self f);
    f_min_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
        (self: v_I)
        ->
        true);
    f_min_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
        (self: v_I)
        (out: Core_models.Option.t_Option i0.f_Item)
        ->
        true);
    f_min
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
        (self: v_I)
        ->
        iter_min #v_I self);
    f_max_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
        (self: v_I)
        ->
        true);
    f_max_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
        (self: v_I)
        (out: Core_models.Option.t_Option i0.f_Item)
        ->
        true);
    f_max
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord i0.f_Item)
        (self: v_I)
        ->
        iter_max #v_I self);
    f_collect_pre
    =
    (fun
        (#v_B: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Iter.Traits.Collect.t_FromIterator v_B i0.f_Item)
        (self: v_I)
        ->
        true);
    f_collect_post
    =
    (fun
        (#v_B: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Iter.Traits.Collect.t_FromIterator v_B i0.f_Item)
        (self: v_I)
        (out: v_B)
        ->
        true);
    f_collect
    =
    fun
      (#v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i1:
        Core_models.Iter.Traits.Collect.t_FromIterator v_B i0.f_Item)
      (self: v_I)
      ->
      Core_models.Iter.Traits.Collect.f_from_iter #v_B
        #i0.f_Item
        #FStar.Tactics.Typeclasses.solve
        #v_I
        self
  }
